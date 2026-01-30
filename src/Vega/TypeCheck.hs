{-# LANGUAGE MagicHash #-}

module Vega.TypeCheck (checkDeclaration) where

import Vega.Syntax

import Effectful hiding (Effect)
import Relude hiding (NonEmpty, State, Type, evalState, get, mapMaybe, put, runState, trace)
import Relude.Extra

import Vega.Error (TypeError (..), TypeErrorSet (MkTypeErrorSet))
import Vega.Util (compose, for2, mapAccumLM, unzip3Seq, zipWithSeqM)

import Vega.Effect.GraphPersistence (CachedType (..), GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence

import Data.Foldable (foldrM)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError_)
import Effectful.State.Static.Local (evalState, get, put, runState)
import GHC.Exts (isTrue#, reallyUnsafePtrEquality)
import GHC.List (List)
import Vega.Builtins (boolType, intType)
import Vega.Builtins qualified as Builtins
import Vega.Debug (showHeadConstructor)
import Vega.Effect.Meta.Static (BindMeta, ReadMeta, bindMetaUnchecked, followMetas, freshMeta, readMeta, runMeta)
import Vega.Effect.Output.Static.Local (Output, output, runOutputList, runOutputSeq)
import Vega.Effect.Trace (Category (..), Trace, trace, withTrace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique, runNewUnique)
import Vega.Loc (HasLoc (getLoc), Loc)
import Vega.Panic (panic)
import Vega.Pretty (align, emphasis, errorText, keyword, note, pretty, (<+>))
import Vega.Seq.NonEmpty (NonEmpty (..), toSeq)
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.TypeCheck.Zonk (zonk)
import Vega.Util qualified as Util
import Witherable (mapMaybe)

data Env = MkEnv
    { localTypes :: HashMap LocalName Type
    , localTypeVariables :: HashMap LocalName (Type, Kind, Monomorphization)
    , localTypeConstructors :: HashMap LocalName Kind
    }

data DeferredConstraint
    = AssertMonomorphized Loc Env Type

emptyEnv :: Env
emptyEnv =
    MkEnv
        { localTypes = mempty
        , localTypeVariables = mempty
        , localTypeConstructors = mempty
        }

bindVarType :: LocalName -> Type -> Env -> Env
bindVarType name type_ env@MkEnv{localTypes} = env{localTypes = insert name type_ localTypes}

bindTypeVariable :: LocalName -> Type -> Kind -> Monomorphization -> Env -> Env
bindTypeVariable name type_ kind monomorphization env@MkEnv{localTypeVariables} = env{localTypeVariables = insert name (type_, kind, monomorphization) localTypeVariables}

lookupTypeVariable :: (HasCallStack) => LocalName -> Env -> (Type, Kind, Monomorphization)
lookupTypeVariable name env = case lookup name env.localTypeVariables of
    Nothing -> error $ "type variable not found in type checker: " <> show name
    Just result -> result

typeVariableKind :: (HasCallStack) => LocalName -> Env -> Kind
typeVariableKind name env =
    case lookup name env.localTypeVariables of
        Nothing -> error $ "type variable not found in type checker: " <> show name
        Just (_, kind, _) -> kind

typeVariableMonomorphization :: (HasCallStack) => LocalName -> Env -> Monomorphization
typeVariableMonomorphization name env =
    case lookup name env.localTypeVariables of
        Nothing -> error $ "type variable not found in type checker: " <> show name
        Just (_, _, monomorphization) -> monomorphization

type TypeCheckCore es =
    ( Trace :> es
    , Output TypeError :> es
    , Error TypeError :> es
    , ReadMeta :> es
    , BindMeta :> es
    )

-- TODO: factor out the reference/unique bits so you don't need full IOE
type TypeCheck es =
    ( GraphPersistence :> es
    , Output DeferredConstraint :> es
    , Output TypeError :> es
    , Error TypeError :> es
    , Trace :> es
    , ReadMeta :> es
    , BindMeta :> es
    , NewUnique :> es
    )

-- TODO: does it make sense to return the declaration anyway even if we have errors?
-- We already have the *renamed* syntax so I'm not sure if this is really beneficial
-- (in any case, we can't just compile it if it has type errors so there isn't that much
-- we could do with it anyway. it might help the LSP though)
checkDeclaration :: (GraphPersistence :> es, Trace :> es, IOE :> es) => Declaration Renamed -> Eff es (Either TypeErrorSet (Declaration Typed))
checkDeclaration (MkDeclaration{loc, name, syntax}) = withTrace TypeCheck ("Declaration: " <> pretty name) do
    ((syntaxOrFatalError, deferredConstraints), nonFatalDirectErrors) <-
        checkDeclarationSyntax loc syntax
            & runNewUnique
            & runMeta
            & runErrorNoCallStack @TypeError
            & runOutputList @DeferredConstraint
            & runOutputSeq @TypeError

    (fatalSolverError, nonFatalSolverErrors) <-
        solveConstraints deferredConstraints
            & runMeta
            & runErrorNoCallStack @TypeError
            & runOutputSeq @TypeError

    let nonFatalErrors = nonFatalDirectErrors <> nonFatalSolverErrors
    let fatalErrorsOrSyntax = case (syntaxOrFatalError, fatalSolverError) of
            (Left error1, Left error2) -> Left [error1, error2]
            (Left error1, Right ()) -> Left [error1]
            (Right _, Left error2) -> Left [error2]
            (Right syntax, Right ()) -> Right syntax

    runMeta $ case fatalErrorsOrSyntax of
        Left fatalErrors -> do
            errors <- zonk (MkTypeErrorSet (nonFatalErrors <> fatalErrors))
            pure (Left errors)
        Right syntax ->
            case nonFatalErrors of
                [] -> pure (Right (MkDeclaration{loc, name, syntax}))
                errors -> do
                    errors <- zonk (MkTypeErrorSet errors)
                    pure (Left errors)

typeError :: (Output TypeError :> es, Trace :> es) => TypeError -> Eff es ()
typeError error = do
    trace TypeCheck (errorText ("ERROR:") <+> showHeadConstructor error)
    output error

fatalTypeError :: (Error TypeError :> es, Trace :> es) => TypeError -> Eff es a
fatalTypeError error = do
    trace TypeCheck (errorText ("FATAL ERROR:") <+> showHeadConstructor error)
    throwError_ error

getGlobalType :: (TypeCheck es) => GlobalName -> Eff es Type
getGlobalType name = withTrace TypeCheck ("getGlobalType " <> prettyGlobal VarKind name) do
    case isInternalName name of
        True -> case lookup name Builtins.builtinTypes of
            Just type_ -> pure type_
            Nothing -> panic $ "builtin variable without a type: " <> prettyGlobal VarKind name
        False ->
            GraphPersistence.getGlobalType name >>= \case
                CachedType cachedType -> do
                    trace TypeCheck $ "cached ~> " <> pretty cachedType
                    pure cachedType
                CachedTypeSyntax syntax -> do
                    (_rep, type_, _) <- inferTypeRep emptyEnv syntax
                    GraphPersistence.cacheGlobalType name type_
                    pure type_
                RenamingFailed -> dummyMetaOfUnknownKind

globalConstructorKind :: (TypeCheck es) => GlobalName -> Eff es Kind
globalConstructorKind name = do
    if isInternalName name
        then case lookup name Builtins.builtinKinds of
            Nothing -> error $ "builtin type without a kind: " <> show name
            Just kind -> pure kind
        else do
            GraphPersistence.getCachedGlobalKind name >>= \case
                Ok cachedKind -> pure cachedKind
                Failed{} -> dummyMetaOfUnknownKind
                Missing{} -> do
                    declarationName <-
                        GraphPersistence.getDefiningDeclaration name >>= \case
                            Nothing -> panic "trying to find kind of non-internal definition without declaration"
                            Just declarationName -> pure declarationName
                    GraphPersistence.getRenamed declarationName >>= \case
                        Failed{} -> dummyMetaOfUnknownKind
                        Missing{} -> panic $ "missing renamed for declaration" <+> pretty declarationName <+> "in type checker"
                        Ok renamed -> computeAndCacheKind renamed

-- TODO: check that data constructors don't contain other data constructors from the same SCC
-- as arguments to type constructors where their representation ends up in the resulting representation
computeAndCacheKind :: forall es. (TypeCheck es) => Declaration Renamed -> Eff es Kind
computeAndCacheKind declaration = withTrace KindCheck ("computeAndCacheKind: " <> showHeadConstructor declaration) $ case declaration.syntax of
    DefineFunction{} -> error "trying to compute kind of a function"
    DefineVariantType{name, typeParameters, constructors} -> do
        ownSCC <- GraphPersistence.getSCC declaration.name

        let inSameSCC :: Name -> Eff es Bool
            inSameSCC (Local _) = undefined
            inSameSCC (Global globalName)
                | isInternalName globalName = pure False
                | otherwise = do
                    declarationName <-
                        GraphPersistence.getDefiningDeclaration globalName >>= \case
                            Nothing -> error "trying to find SCC of non-internal definition without declaration"
                            Just declarationName -> pure declarationName
                    scc <- GraphPersistence.getSCC declarationName
                    pure (scc == ownSCC)

        let env = emptyEnv
        (env, bindersAndSyntax) <- mapAccumLM applyForallBinder env typeParameters
        let binders = foldMap fst bindersAndSyntax

        let repOfDifferentSCC typeSyntax = do
                (representation, _, _) <- inferTypeRep env typeSyntax
                pure representation

        constructorRepresentations <- for constructors \(_loc, _name, components) -> do
            components <- for components \case
                component@(TypeConstructorS _ name) ->
                    inSameSCC name >>= \case
                        True -> pure (PrimitiveRep BoxedRep)
                        False -> repOfDifferentSCC component
                component@(TypeApplicationS _ (TypeConstructorS _loc name) _) ->
                    inSameSCC name >>= \case
                        True -> pure (PrimitiveRep BoxedRep)
                        False -> repOfDifferentSCC component
                component -> repOfDifferentSCC component
            case components of
                [] -> pure (PrimitiveRep UnitRep)
                [r] -> pure r
                _ -> pure (ProductRep components)

        let bodyRepresentation = case constructorRepresentations of
                [] -> PrimitiveRep EmptyRep
                [r] -> r
                _ -> SumRep constructorRepresentations

        let (inferredBinders, visibleBinderKinds) = Util.partitionWithSeq binders \case
                binder@MkForallBinder{visibility = Inferred} -> Left binder
                MkForallBinder{visibility = Visible, kind} -> Right kind

        computedKind <- case visibleBinderKinds of
            Empty -> pure (forall_ inferredBinders (Type bodyRepresentation))
            _ -> pure (forall_ inferredBinders (TypeFunction visibleBinderKinds (Type bodyRepresentation)))

        GraphPersistence.cacheGlobalKind name computedKind
        pure computedKind
    DefineExternalFunction{} -> error "trying to compute kind of an (external) function"

checkDeclarationSyntax :: (TypeCheck es) => Loc -> DeclarationSyntax Renamed -> Eff es (DeclarationSyntax Typed)
checkDeclarationSyntax loc = \case
    DefineFunction{ext = (), name, typeSignature, declaredTypeParameters, parameters, body} -> do
        let env = emptyEnv
        (functionType, typeSignature) <- checkType env Parametric (Type functionRepresentation) typeSignature

        (env, remainingType) <- bindTypeParameters loc env declaredTypeParameters functionType

        -- We bound the declared type parameters above and the rest are not accessible in the body
        -- so we can just skolemize them away here
        remainingType <- skolemize loc env remainingType
        (parameterTypes, effect, returnType, parameterMismatch) <- splitFunctionType loc env (length parameters) remainingType

        case parameterMismatch of
            Nothing -> pure ()
            Just actualParameterTypes ->
                typeError
                    ( FunctionDefinedWithIncorrectNumberOfArguments
                        { loc
                        , functionName = Global name
                        , expectedType = functionType
                        , expectedNumberOfArguments = length actualParameterTypes
                        , numberOfDefinedParameters = length parameters
                        }
                    )

        let checkParameter (pattern_, ()) type_ = do
                (pattern_, envTrans) <- checkPattern env type_ pattern_
                representation <- representationOfType (getLoc pattern_) env type_
                pure ((pattern_, representation), envTrans)

        (parameters, transformers) <- Seq.unzip <$> zipWithSeqM checkParameter parameters parameterTypes
        env <- pure (compose transformers env)

        body <- check env effect returnType body

        -- TODO: add metadata for error messages in case this fails (i think it should have thrown earlier in that case though)
        returnRepresentation <- representationOfType (getLoc typeSignature) env returnType
        let (forallAndExistentialBinders, _) = collectPrenexBinders functionType
        let forallBinders =
                forallAndExistentialBinders & mapMaybe \case
                    Left forallBinder -> Just forallBinder
                    Right _existentialBinder -> Nothing
        pure
            DefineFunction
                { ext = MkDefineFunctionTypedExt{returnRepresentation = returnRepresentation, forallBinders}
                , name
                , typeSignature
                , declaredTypeParameters
                , parameters
                , body
                }
    DefineVariantType{name, typeParameters, constructors} -> do
        let env = emptyEnv
        (env, binders) <- mapAccumLM applyForallBinder env typeParameters
        let typeParameters = fmap (\(_, binder) -> binder) binders

        constructors <- for constructors \(name, loc, parameters) -> do
            -- TODO: we need the representations, right??
            (representations, _, parameters) <- unzip3Seq <$> traverse (inferTypeRep env) parameters
            pure (name, loc, parameters)
        pure (DefineVariantType{name, typeParameters, constructors})
    DefineExternalFunction{name, type_} -> do
        (_, type_) <- checkType emptyEnv Parametric (Type functionRepresentation) type_
        pure (DefineExternalFunction{name, type_})

checkPattern :: (TypeCheck es) => Env -> Type -> Pattern Renamed -> Eff es (Pattern Typed, Env -> Env)
checkPattern env expectedType pattern_ = withTrace TypeCheck ("checkPattern " <> showHeadConstructor pattern_) do
    let deferToInference = do
            (pattern_, type_, envTrans) <- inferPattern env pattern_
            subsumes (getLoc pattern_) env type_ expectedType
            pure (pattern_, envTrans)
    case pattern_ of
        VarPattern loc () var isShadowed -> do
            rep <- representationOfType loc env expectedType
            pure (VarPattern { loc = loc, ext = rep, name = var, isShadowed = isShadowed }, bindVarType var expectedType)
        AsPattern loc () pattern_ name -> do
            (pattern_, innerTrans) <- checkPattern env expectedType pattern_
            rep <- representationOfType loc env expectedType
            pure (AsPattern loc rep pattern_ name, bindVarType name expectedType . innerTrans)
        ConstructorPattern{} -> deferToInference
        TypePattern loc innerPattern innerTypeSyntax -> do
            (_typeRep, innerType, innerTypeSyntax) <- inferTypeRep env innerTypeSyntax
            (innerPattern, innerTrans) <- checkPattern env innerType innerPattern
            subsumes loc env innerType expectedType
            pure (TypePattern loc innerPattern innerTypeSyntax, innerTrans)
        OrPattern loc branches -> do
            -- TODO: this was wrong. we can't just compose the environment transformers from the branches.
            -- all cases need to return *the same* environment constructor, but we need to actually
            -- check that (i.e. check that every variable is bound to the same type in every branch)
            undefined
        WildcardPattern loc -> pure (WildcardPattern loc, id)
        TuplePattern loc elementPatterns -> do
            elementTypes <-
                followMetas expectedType >>= \case
                    Tuple elementTypes -> pure elementTypes
                    _ -> for elementPatterns \_ -> do
                        MetaVar <$> freshTypeMeta "e"
            when (length elementPatterns /= length elementTypes) do
                typeError
                    ( TuplePatternOfIncorrectNumberOfArgs
                        { loc
                        , expected = length elementTypes
                        , actual = length elementPatterns
                        , expectedType
                        }
                    )

            (patterns, envTransformers) <- for2 elementPatterns elementTypes \pattern_ type_ -> do
                checkPattern env type_ pattern_
            pure (TuplePattern loc patterns, Util.compose envTransformers)

inferPattern :: (TypeCheck es) => Env -> Pattern Renamed -> Eff es (Pattern Typed, Type, Env -> Env)
inferPattern env pattern_ = withTrace TypeCheck ("inferPattern " <> showHeadConstructor pattern_) $ case pattern_ of
    WildcardPattern loc -> do
        type_ <- MetaVar <$> freshTypeMeta "w"
        pure (WildcardPattern loc, type_, id)
    VarPattern loc () varName isShadowed -> do
        rep <- MetaVar <$> freshMeta "r" Rep
        type_ <- MetaVar <$> freshMeta (varName.name) (Type rep)
        pure (VarPattern { loc = loc, ext = rep, name = varName, isShadowed = isShadowed }, type_, bindVarType varName type_)
    AsPattern loc () innerPattern name -> do
        (innerPattern, innerType, innerTrans) <- inferPattern env innerPattern
        rep <- representationOfType loc env innerType
        pure (AsPattern loc rep innerPattern name, innerType, bindVarType name innerType . innerTrans)
    ConstructorPattern{loc, constructor, subPatterns} -> do
        constructorType <- instantiate loc env =<< varType env constructor

        -- We need to do this hacky dance to special case nullary constructors, where
        -- the constructor doesn't have a function type
        let nullaryCase = case subPatterns of
                (_ :<| _) -> do
                    typeError
                        ( ConstructorPatternOfIncorrectNumberOfArgs
                            { loc
                            , actual = length subPatterns
                            , expectedTypes = []
                            }
                        )
                    -- We still infer sub-patterns to catch type errors and bind any spurious variables
                    (subPatterns, _subPatternTypes, envTransformers) <-
                        unzip3Seq <$> for subPatterns \pattern_ -> do
                            inferPattern env pattern_
                    pure (ConstructorPattern{loc, constructor, subPatterns}, constructorType, Util.compose envTransformers)
                Empty -> do
                    pure (ConstructorPattern{loc, constructor, subPatterns = []}, constructorType, id)

        case constructorType of
            TypeConstructor{} -> nullaryCase
            TypeApplication{} -> nullaryCase
            _ -> do
                (parameterTypes, _, resultType, parameterCountMismatch) <- splitFunctionType loc env (length subPatterns) constructorType
                case parameterCountMismatch of
                    Nothing -> pure ()
                    Just actualParameterTypes ->
                        typeError
                            ( ConstructorPatternOfIncorrectNumberOfArgs
                                { loc
                                , actual = length subPatterns
                                , expectedTypes = actualParameterTypes
                                }
                            )
                (subPatterns, envTransformers) <- for2 parameterTypes subPatterns \type_ pattern_ -> do
                    checkPattern env type_ pattern_

                pure (ConstructorPattern{loc, constructor, subPatterns}, resultType, Util.compose envTransformers)
    TuplePattern{loc, subPatterns} -> do
        (subPatterns, subPatternTypes, envTransformers) <-
            unzip3Seq <$> for subPatterns \pattern_ -> do
                inferPattern env pattern_
        pure (TuplePattern{loc, subPatterns}, Tuple subPatternTypes, Util.compose envTransformers)
    TypePattern loc innerPattern typeSyntax -> do
        (_kind, type_, typeSyntax) <- inferTypeRep env typeSyntax
        (innerPattern, envTrans) <- checkPattern env type_ innerPattern
        pure (TypePattern loc innerPattern typeSyntax, type_, envTrans)
    OrPattern{} -> undefined

check :: (TypeCheck es) => Env -> Effect -> Type -> Expr Renamed -> Eff es (Expr Typed)
check env ambientEffect expectedType expr = withTrace TypeCheck ("check:" <+> showHeadConstructor expr <+> keyword "<=" <+> pretty expectedType <> keyword " | " <> pretty ambientEffect) do
    let deferToInference = do
            (actualType, expr) <- infer env ambientEffect expr
            subsumes (getLoc expr) env actualType expectedType
            pure expr
    case expr of
        Var{} -> deferToInference
        DataConstructor{} -> deferToInference
        Application{} -> deferToInference
        -- TODO: not entirely sure if this is correct or if we should try to stay in check mode
        VisibleTypeApplication{} -> deferToInference
        Lambda loc typeParameters parameters body -> do
            (env, typeWithoutBoundParameters) <- bindTypeParameters loc env typeParameters expectedType

            -- Any type variables *not* bound above are not going to be available in the body
            -- and so are just skolemized away here
            resultingType <- skolemize loc env typeWithoutBoundParameters
            (parameterTypes, expectedEffect, returnType, parameterMismatch) <- splitFunctionType loc env (length parameters) resultingType

            case parameterMismatch of
                Nothing -> pure ()
                Just actualParameterTypes ->
                    typeError
                        ( LambdaDefinedWithIncorrectNumberOfArguments
                            { loc
                            , expectedType
                            , expected = length actualParameterTypes
                            , actual = length parameters
                            }
                        )

            let checkParameter parameter parameterType = do
                    checkPattern env parameterType parameter
            (parameters, envTransformers) <- Seq.unzip <$> zipWithSeqM checkParameter parameters parameterTypes
            body <- check (compose envTransformers env) expectedEffect returnType body
            pure (Lambda loc typeParameters parameters body)
        StringLiteral{} -> deferToInference
        IntLiteral{} -> deferToInference
        DoubleLiteral{} -> deferToInference
        If{loc, condition, thenBranch, elseBranch} -> do
            (condition) <- check env ambientEffect Builtins.boolType condition
            (thenBranch) <- check env ambientEffect expectedType thenBranch
            (elseBranch) <- check env ambientEffect expectedType elseBranch

            pure (If{loc, condition, thenBranch, elseBranch})
        SequenceBlock{loc, statements} -> do
            case statements of
                (realStatements :|> Run lastLoc lastExpression) -> do
                    (env, realStatements) <- checkStatements env ambientEffect realStatements
                    (lastExpression) <- check env ambientEffect expectedType lastExpression
                    pure (SequenceBlock{loc, statements = realStatements :|> Run lastLoc lastExpression})
                _ -> deferToInference
        TupleLiteral loc elements -> do
            elementTypes <-
                followMetas expectedType >>= \case
                    Tuple elementTypes -> pure elementTypes
                    _ -> do
                        elementTypes <- for elements \_ -> do
                            MetaVar <$> freshTypeMeta "t"
                        subsumes loc env (Tuple elementTypes) expectedType
                        pure elementTypes
            when (length elementTypes /= length elements) do
                typeError
                    TupleLiteralOfIncorrectNumberOfArgs
                        { loc
                        , expected = length elementTypes
                        , actual = length elements
                        , expectedType
                        }

            elements <- for (Seq.zip elements elementTypes) \(element, elementType) -> do
                check env ambientEffect elementType element

            pure (TupleLiteral loc elements)
        PartialApplication{} -> deferToInference
        BinaryOperator{} -> deferToInference
        Match{loc, scrutinee, cases} -> do
            (scrutineeType, scrutinee) <- infer env ambientEffect scrutinee
            cases <- for cases \MkMatchCase{loc, pattern_, body} -> do
                (pattern_, envTrans) <- checkPattern env scrutineeType pattern_
                body <- check (envTrans env) ambientEffect expectedType body
                pure (MkMatchCase{loc, pattern_, body})
            pure (Match{loc, scrutinee, cases})

infer :: (TypeCheck es) => Env -> Effect -> Expr Renamed -> Eff es (Type, Expr Typed)
infer env ambientEffect expr = do
    (type_, expr) <- withTrace TypeCheck ("infer " <> showHeadConstructor expr <> keyword " | " <> pretty ambientEffect) go
    trace TypeCheck ("infer" <> showHeadConstructor expr <> keyword " => " <> pretty type_)
    pure (type_, expr)
  where
    go = case expr of
        Var loc name -> do
            type_ <- instantiate loc env =<< varType env name
            pure (type_, Var loc name)
        DataConstructor loc () name -> do
            type_ <- instantiate loc env =<< varType env name
            representation <- representationOfType loc env type_
            pure (type_, DataConstructor loc representation name)
        Application{loc, functionExpr, arguments} -> do
            (functionType, functionExpr) <- infer env ambientEffect functionExpr
            (argumentTypes, functionEffect, returnType, parameterMismatch) <- splitFunctionType loc env (length arguments) functionType

            case parameterMismatch of
                Nothing -> pure ()
                Just actualArgumentTypes ->
                    typeError $
                        FunctionAppliedToIncorrectNumberOfArgs
                            { loc
                            , expected = length actualArgumentTypes
                            , actual = length arguments
                            , functionType
                            }
            subsumesEffect functionEffect ambientEffect

            let checkArguments argumentExpr argumentType = do
                    check env ambientEffect argumentType argumentExpr
            arguments <- zipWithSeqM checkArguments arguments argumentTypes

            returnRepresentation <- representationOfType loc env returnType
            pure (returnType, Application{loc, functionExpr, arguments, representation = returnRepresentation})
        VisibleTypeApplication{loc, varName, typeArguments = typeArgumentSyntax} -> do
            type_ <- varType env varName

            let visibleBinders = case normalizeForalls type_ of
                    Forall binders _ -> fromList [binder | binder@MkForallBinder{visibility = Visible} <- toList binders]
                    _ -> []

            when (length visibleBinders < length typeArgumentSyntax) do
                typeError
                    ( TypeApplicationWithTooFewParameters
                        { loc
                        , typeArgumentCount = length typeArgumentSyntax
                        , instantiatedType = type_
                        , parameterCount = length visibleBinders
                        }
                    )

            -- If we have fewer arguments than the type has parameters, that is okay.
            -- `zip` will ignore the binders of excess parameters
            (typeArguments, typeArgumentSyntax) <-
                Seq.unzip <$> for (Seq.zip typeArgumentSyntax visibleBinders) \(argument, binder) -> do
                    checkType env binder.monomorphization binder.kind argument

            type_ <- instantiate loc env =<< instantiateWith loc env type_ typeArguments
            pure (type_, VisibleTypeApplication{loc, varName, typeArguments = typeArgumentSyntax})
        Lambda loc typeParameters parameters body -> do
            case typeParameters of
                [] -> pure ()
                _ -> undefined -- error? I don't think we can handle type parameters in infer mode
            (parameters, parameterTypes, envTransformers) <- unzip3Seq <$> traverse (inferPattern env) parameters

            bodyEffect <- MetaVar <$> freshMeta "e" Effect
            (bodyType, body) <- infer (compose envTransformers env) bodyEffect body

            pure (Function parameterTypes bodyEffect bodyType, Lambda loc typeParameters parameters body)
        StringLiteral loc literal -> pure (Builtins.stringType, StringLiteral loc literal)
        IntLiteral loc literal -> pure (Builtins.intType, IntLiteral loc literal)
        DoubleLiteral loc literal -> pure (Builtins.doubleType, DoubleLiteral loc literal)
        BinaryOperator loc left operator right -> do
            let (leftType, rightType, resultType) = binaryOperatorType operator
            left <- check env ambientEffect leftType left
            right <- check env ambientEffect rightType right
            pure (resultType, BinaryOperator loc left operator right)
        If{loc, condition, thenBranch, elseBranch} -> do
            (condition) <- check env ambientEffect Builtins.boolType condition
            (thenType, thenBranch) <- infer env ambientEffect thenBranch
            (elseType, elseBranch) <- infer env ambientEffect elseBranch
            subsumes loc env thenType elseType
            subsumes loc env elseType thenType
            pure (thenType, If{loc, condition, thenBranch, elseBranch})
        SequenceBlock{loc, statements} ->
            case statements of
                (realStatements :|> Run lastLoc lastExpression) -> do
                    (env, realStatements) <- checkStatements env ambientEffect realStatements
                    (type_, lastExpression) <- infer env ambientEffect lastExpression
                    pure (type_, SequenceBlock{loc, statements = realStatements :|> Run lastLoc lastExpression})
                _ -> do
                    (_env, statements) <- checkStatements env ambientEffect statements
                    pure (Tuple [], SequenceBlock{loc, statements})
        PartialApplication{} -> undefined
        TupleLiteral loc elements -> do
            (elementTypes, elements) <- Seq.unzip <$> for elements (infer env ambientEffect)
            pure (Tuple elementTypes, TupleLiteral loc elements)
        Match{loc, scrutinee, cases} -> do
            (scrutineeType, scrutinee) <- infer env ambientEffect scrutinee
            resultType <- MetaVar <$> freshTypeMeta "a"

            cases <- for cases \MkMatchCase{loc, pattern_, body} -> do
                (pattern_, envTrans) <- checkPattern env scrutineeType pattern_
                body <- check (envTrans env) ambientEffect resultType body
                pure (MkMatchCase{loc, pattern_, body})
            pure (resultType, Match{loc, scrutinee, cases})

checkStatements :: (TypeCheck es) => Env -> Effect -> Seq (Statement Renamed) -> Eff es (Env, Seq (Statement Typed))
checkStatements env ambientEffect statements = mapAccumLM (\env -> checkStatement env ambientEffect) env statements

checkStatement :: (TypeCheck es) => Env -> Effect -> Statement Renamed -> Eff es (Env, Statement Typed)
checkStatement env ambientEffect statement = withTrace TypeCheck ("checkStatement " <> showHeadConstructor statement) $ case statement of
    Run loc expr -> do
        expr <- check env ambientEffect (Tuple []) expr
        pure (env, Run loc expr)
    Let loc pattern_ body -> do
        (pattern_, type_, envTrans) <- inferPattern env pattern_
        body <- check env ambientEffect type_ body
        pure (envTrans env, Let loc pattern_ body)
    LetFunction{loc, name, typeSignature, parameters, body} -> do
        (functionType, typeSignature) <- case typeSignature of
            Just typeSignature -> do
                (functionType, typeSignature) <- checkType env Parametric (Type functionRepresentation) typeSignature
                pure (functionType, Just typeSignature)
            Nothing -> do
                type_ <- MetaVar <$> freshTypeMeta "r"
                pure (type_, Nothing)

        env <- pure $ bindVarType name functionType env

        -- TODO: local functions should be able to bind type parameters as well
        -- (env, remainingType) <- bindTypeParameters loc env declaredTypeParameters functionType

        -- We bound the declared type parameters above and the rest are not accessible in the body
        -- so we can just skolemize them away here
        remainingType <- skolemize loc env functionType
        (parameterTypes, effect, returnType, parameterMismatch) <- splitFunctionType loc env (length parameters) remainingType

        case parameterMismatch of
            Nothing -> pure ()
            Just actualParameterTypes ->
                typeError
                    ( FunctionDefinedWithIncorrectNumberOfArguments
                        { loc
                        , functionName = Local name
                        , expectedType = functionType
                        , expectedNumberOfArguments = length actualParameterTypes
                        , numberOfDefinedParameters = length parameters
                        }
                    )

        let checkParameter (pattern_, ()) type_ = do
                (pattern_, envTrans) <- checkPattern env type_ pattern_
                representation <- representationOfType (getLoc pattern_) env type_
                pure ((pattern_, representation), envTrans)

        (parameters, transformers) <- Seq.unzip <$> zipWithSeqM checkParameter parameters parameterTypes
        innerEnv <- pure (compose transformers env)

        body <- check innerEnv effect returnType body

        -- TODO: include this in the generated core
        -- TODO: add metadata for error messages in case this fails (i think it should have thrown earlier in that case though)
        let typeSignatureLoc = case typeSignature of
                Nothing -> loc
                Just typeSignature -> getLoc typeSignature
        returnRepresentation <- representationOfType typeSignatureLoc innerEnv returnType

        pure (env, LetFunction{ext = MkLetFunctionTypedExt{returnRepresentation}, loc, name, typeSignature, parameters, body})
    Use{} -> undefined

bindTypeParameters :: (TypeCheck es) => Loc -> Env -> Seq (Loc, LocalName) -> Type -> Eff es (Env, Type)
bindTypeParameters loc env initialParameters polytype = fmap swap $ evalState (toList initialParameters) $ runState env do
    let onVisible _loc _env MkForallBinder{varName = _typeSignatureVarName, visibility = _, monomorphization, kind} = do
            parameters <- get @(List (Loc, LocalName))
            env <- get @Env
            case parameters of
                [] -> pure StopInstantiating
                (_loc, parameterVarName) : rest -> do
                    skolem <- Skolem <$> freshSkolem parameterVarName monomorphization kind

                    put (bindTypeVariable parameterVarName skolem kind monomorphization env)
                    put rest
                    case rest of
                        [] -> pure (LastInstantiation skolem)
                        _ -> pure (InstantiateWith skolem)
    remainingType <-
        instantiateGeneric
            MkGenericInstantiation
                { onInferred = skolemizeStrategy
                , onVisible = onVisible
                , onExistential = instantiateExistentialToMetaStrategy
                }
            loc
            env
            polytype
    parameters <- get @(List (Loc, LocalName))
    case parameters of
        [] -> pure remainingType
        _ -> do
            let actualCount = case normalizeForalls polytype of
                    Forall binders _ -> length binders
                    _ -> 0
            typeError (TryingToBindTooManyTypeParameters{loc, boundCount = length initialParameters, actualCount, type_ = polytype})
            pure remainingType

{- | Extend the length of a seq of types to the required length by appending
fresh meta variables.
This is useful in cases where we know that the number of parameters is too large
(e.g. in a lambda or function definition) but we don't want to throw a fatal type error
-}
padWithMetas :: (TypeCheck es) => Int -> Seq Type -> Eff es (Seq Type)
padWithMetas expectedLength types
    | expectedLength > length types = do
        metas <- Seq.replicateM (expectedLength - length types) (MetaVar <$> freshTypeMeta "e")
        pure (types <> metas)
    | otherwise = pure types

varType :: (HasCallStack) => (TypeCheck es) => Env -> Name -> Eff es Type
varType env name = case name of
    Global globalName -> getGlobalType globalName
    Local localName -> do
        case lookup localName env.localTypes of
            Just type_ -> pure type_
            Nothing -> error ("variable not found in type checker: " <> show name)

constructorKind :: (TypeCheck es) => Env -> Name -> Eff es Kind
constructorKind env name = case name of
    Global name -> globalConstructorKind name
    Local name -> case lookup name env.localTypeConstructors of
        Nothing -> error $ "local type constructor " <> show name <> " not found in type checker"
        Just kind -> pure kind

checkType :: (TypeCheck es) => Env -> Monomorphization -> Kind -> TypeSyntax Renamed -> Eff es (Type, TypeSyntax Typed)
checkType env expectedMonomorphizability expectedKind syntax = withTrace KindCheck ("checkType: " <> showHeadConstructor syntax <> keyword " <= " <> pretty expectedKind) do
    (kind, type_, syntax) <- inferType env syntax
    subsumes (getLoc syntax) env kind expectedKind
    assertMonomorphizability (getLoc syntax) env type_ expectedMonomorphizability
    pure (type_, syntax)

inferType :: (TypeCheck es) => Env -> TypeSyntax Renamed -> Eff es (Kind, Type, TypeSyntax Typed)
inferType env syntax = do
    (kind, type_, syntax) <- withTrace KindCheck ("inferType: " <> showHeadConstructor syntax) go
    trace KindCheck ("inferType: " <> showHeadConstructor syntax <+> keyword "=>" <+> pretty kind <+> keyword "~>" <+> pretty type_)
    pure (kind, type_, syntax)
  where
    go = case syntax of
        TypeConstructorS loc name -> do
            kind <- constructorKind env name
            pure (kind, TypeConstructor name, TypeConstructorS loc name)
        TypeApplicationS loc typeConstructorSyntax argumentsSyntax -> do
            (constructorKind, typeConstructor, typeConstructorSyntax) <- inferType env typeConstructorSyntax
            followMetas constructorKind >>= \case
                TypeFunction argumentKinds resultKind
                    | length argumentKinds == length argumentsSyntax -> do
                        (arguments, argumentsSyntax) <- Seq.unzip <$> zipWithSeqM (checkType env Parametric) argumentKinds argumentsSyntax
                        pure
                            ( resultKind
                            , TypeApplication typeConstructor arguments
                            , TypeApplicationS loc typeConstructorSyntax argumentsSyntax
                            )
                    | otherwise -> do
                        dummyKind <- MetaVar <$> freshMeta "k" Kind
                        dummyResult <- MetaVar <$> freshMeta "err" dummyKind
                        typeError
                            ( TypeConstructorAppliedToIncorrectNumberOfArguments
                                { loc
                                , type_ = typeConstructor
                                , kind = constructorKind
                                , expectedNumber = length argumentKinds
                                , actualNumber = length argumentsSyntax
                                }
                            )
                        -- if the types don't match, we can't really check arguments so we infer them to
                        -- get the correct type/Typed syntax out and catch further errors inside them
                        -- but we don't actually check their kinds against anything
                        (_, arguments, argumentsSyntax) <- unzip3Seq <$> for argumentsSyntax \syntax -> inferType env syntax
                        pure (dummyResult, TypeApplication typeConstructor arguments, TypeApplicationS loc typeConstructorSyntax argumentsSyntax)
                constructorKind -> do
                    (argumentKinds, arguments, argumentsSyntax) <-
                        unzip3Seq <$> for argumentsSyntax \argumentSyntax -> do
                            inferType env argumentSyntax
                    resultKindKind <- MetaVar <$> freshMeta "k" Kind
                    resultKind <- MetaVar <$> freshMeta "r" resultKindKind
                    subsumes (getLoc typeConstructorSyntax) env constructorKind (TypeFunction argumentKinds resultKind)

                    pure (resultKind, TypeApplication typeConstructor arguments, TypeApplicationS loc typeConstructorSyntax argumentsSyntax)
        TypeVarS loc localName -> do
            let (actualType, kind, _mono) = lookupTypeVariable localName env
            pure (kind, actualType, TypeVarS loc localName)
        ForallS loc typeVarBinders body -> do
            (env, typeVarBindersAndSyntax) <- mapAccumLM applyForallBinder env typeVarBinders
            let (typeVarBinders, typeVarBinderSyntax) = NonEmpty.unzip typeVarBindersAndSyntax

            (kind, body, bodySyntax) <- inferType env body

            pure
                -- TODO: uhhhh i don't think this is correct?
                -- we will need to introduce kind level foralls here... sometimes??
                ( kind
                , forall_ (fold typeVarBinders) body
                , ForallS loc typeVarBinderSyntax bodySyntax
                )
        ExistsS loc binders body -> do
            let applyExistentialBinder env (name, kindSyntax) = do
                    (kind, kindSyntax) <- checkType env Parametric Kind kindSyntax
                    pure (bindTypeVariable name (TypeVar name) kind Parametric env, (name, kind, kindSyntax))
            (env, binders) <- mapAccumLM applyExistentialBinder env binders
            (bodyKind, body, bodySyntax) <- inferType env body
            pure
                -- TODO: If the program is well-typed, this is definitely okay since the body kind cannot mention any of the variables
                -- bound by the existential anyway (they're parametric). If it isn't, this might cause panics about unresolved type variables
                -- later on though.
                ( bodyKind
                , Exists (fmap (\(name, kind, _) -> (name, kind)) binders) body
                , ExistsS loc (fmap (\(name, _, kindSyntax) -> (name, kindSyntax)) binders) bodySyntax
                )
        PureFunctionS loc parameters result -> do
            (_parameterReps, parameterTypes, parameterTypeSyntax) <- unzip3Seq <$> traverse (inferTypeRep env) parameters
            (_resultRep, resultType, resultTypeSyntax) <- inferTypeRep env result
            pure (Type functionRepresentation, Function parameterTypes Pure resultType, PureFunctionS loc parameterTypeSyntax resultTypeSyntax)
        FunctionS loc parameters effect result -> do
            (_parameterReps, parameterTypes, parameterTypeSyntax) <- unzip3Seq <$> traverse (inferTypeRep env) parameters
            (effect, effectSyntax) <- checkType env Parametric Effect effect
            (_resultRep, resultType, resultTypeSyntax) <- inferTypeRep env result
            pure (Type functionRepresentation, Function parameterTypes effect resultType, FunctionS loc parameterTypeSyntax effectSyntax resultTypeSyntax)
        TypeFunctionS loc parameters result -> do
            (parameterTypes, parameterTypeSyntax) <- Seq.unzip <$> traverse (checkType env Monomorphized Kind) parameters
            (resultType, resultTypeSyntax) <- checkType env Monomorphized Kind result
            pure (Kind, TypeFunction parameterTypes resultType, TypeFunctionS loc parameterTypeSyntax resultTypeSyntax)
        TupleS loc elements -> do
            (elementReps, elementTypes, elementTypeSyntax) <- unzip3Seq <$> traverse (inferType env) elements
            pure (Type (ProductRep elementReps), Tuple elementTypes, TupleS loc elementTypeSyntax)
        RepS loc -> pure (Kind, Rep, RepS loc)
        TypeS loc repSyntax -> do
            (rep, repSyntax) <- checkType env Parametric Rep repSyntax
            pure (Kind, Type rep, TypeS loc repSyntax)
        EffectS loc -> pure (Kind, Effect, EffectS loc)
        SumRepS loc elementSyntax -> do
            (elements, elementSyntax) <- Seq.unzip <$> traverse (checkType env Parametric Rep) elementSyntax
            pure (Rep, SumRep elements, SumRepS loc elementSyntax)
        ProductRepS loc elementSyntax -> do
            (elements, elementSyntax) <- Seq.unzip <$> traverse (checkType env Parametric Rep) elementSyntax
            pure (Rep, ProductRep elements, ProductRepS loc elementSyntax)
        ArrayRepS loc inner -> do
            (inner, innerSyntax) <- checkType env Parametric Rep inner
            pure (Rep, ArrayRep inner, ArrayRepS loc innerSyntax)
        PrimitiveRepS loc rep -> pure (Rep, PrimitiveRep rep, PrimitiveRepS loc rep)
        KindS loc -> pure (Kind, Kind, KindS loc)

inferTypeRep :: (TypeCheck es) => Env -> TypeSyntax Renamed -> Eff es (Kind, Type, TypeSyntax Typed)
inferTypeRep env typeSyntax = do
    rep <- MetaVar <$> freshMeta "r" Rep
    -- We don't need a 'monomorphized' constraint on rep here. It might seem like we would, but
    -- since we check against (Type rep), we will only unify `rep` if the infererd kind has
    -- the form ̀`Type _` and in that case the argument to Type will have to
    -- have been checked for monomorphizability already.
    --
    -- Skipping the extra constraint here reduces the number of duplicated error messages
    -- for the same issue.
    (type_, typeSyntax) <- checkType env Parametric (Type rep) typeSyntax
    pure (rep, type_, typeSyntax)

kindOf :: (TypeCheck es) => Loc -> Env -> Type -> Eff es Kind
-- It's okay to match on the type directly here since we don't need to
-- follow meta variables: they already have their kind cached
-- In fact, in some cases this might be more efficient than computing the kinds
-- of their bound types
kindOf loc env = \case
    TypeConstructor name -> constructorKind env name
    TypeApplication funType arguments -> do
        -- We can assume that the kinds here are correct so we only need to pick out the result
        funType <- followMetas funType
        kindOf loc env funType >>= \case
            TypeFunction _parameters result -> do
                pure result
            -- TODO: this shouldn't really happen but somehow it still does?
            functionKind -> do
                argumentKinds <- for arguments (kindOf loc env)
                resultKindKind <- MetaVar <$> freshMeta "k" Kind
                resultKind <- MetaVar <$> freshMeta "r" resultKindKind
                subsumes loc env functionKind (TypeFunction argumentKinds resultKind)
                pure resultKind
    TypeVar name -> pure $ typeVariableKind name env
    Forall bindings body -> do
        -- See NOTE [Kinds of foralls]
        let applyBinding MkForallBinder{varName, visibility = _, kind, monomorphization} env = do
                bindTypeVariable varName (TypeVar varName) kind monomorphization env
        let innerEnv = foldr applyBinding env bindings
        kindOf loc innerEnv body
    Exists binders body -> do
        let innerEnv = foldr (\(name, kind) env -> bindTypeVariable name (TypeVar name) kind Parametric env) env binders
        kindOf loc innerEnv body
    Function{} -> pure (Type functionRepresentation)
    TypeFunction{} -> pure Kind
    Tuple elements -> Type . ProductRep <$> traverse (kindOf loc env) elements
    MetaVar meta -> pure meta.kind
    Skolem skolem -> pure skolem.kind
    Pure -> pure Effect
    Rep -> pure Kind
    Type{} -> pure Kind
    Effect -> pure Kind
    SumRep{} -> pure Rep
    ProductRep{} -> pure Rep
    ArrayRep{} -> pure Rep
    PrimitiveRep{} -> pure Rep
    Kind -> pure Kind

-- | Like checkType but on evaluated `Type`s rather than TypeSyntax
checkEvaluatedType :: (TypeCheck es) => Loc -> Env -> Kind -> Type -> Eff es ()
checkEvaluatedType loc env expectedKind type_ = withTrace KindCheck ("checkEvaluatedType: " <> pretty type_ <+> keyword "<=" <+> pretty expectedKind) do
    actualKind <- kindOf loc env type_
    subsumes loc env actualKind expectedKind

applyForallBinder :: (TypeCheck es) => Env -> ForallBinderS Renamed -> Eff es (Env, (Seq ForallBinder, ForallBinderS Typed))
applyForallBinder env = \case
    UnspecifiedBinderS{loc, varName, monomorphization} -> do
        -- TODO: god this is going to mess up error messages
        let representationVarName = varName{name = "r$" <> varName.name} :: LocalName

        let kind = Type (TypeVar representationVarName)

        pure
            ( env
                & bindTypeVariable representationVarName (TypeVar representationVarName) Rep Monomorphized
                & bindTypeVariable varName (TypeVar varName) kind monomorphization
            ,
                (
                    [ MkForallBinder{varName = representationVarName, kind = Rep, visibility = Inferred, monomorphization = Monomorphized}
                    , MkForallBinder{varName, monomorphization, kind = Type (TypeVar representationVarName), visibility = Visible}
                    ]
                , UnspecifiedBinderS{loc, varName, monomorphization}
                )
            )
    TypeVarBinderS{loc, visibility, monomorphization, varName, kind = kindSyntax} -> do
        (kind, kindSyntax) <- checkType env Parametric Kind kindSyntax
        -- TODO: not entirely sure if this is the right place for this
        monomorphized loc env kind
        pure
            ( bindTypeVariable varName (TypeVar varName) kind monomorphization env
            , ([MkForallBinder{varName, visibility, monomorphization, kind}], TypeVarBinderS{loc, visibility, monomorphization, varName, kind = kindSyntax})
            )

{- | Split an (expected) function type into its parameters, effect and return type.
In case the function isn't known to be a function type ahead of time, this takes
the expected number of parameters and switches to unification.

If the actual number of parameters does not match up with the expected one, it pads the parameters
with meta variables and additionally returns the actual parameters so that calling code
can generate a good error message
-}
splitFunctionType ::
    (TypeCheck es) =>
    Loc ->
    Env ->
    Int ->
    Type ->
    Eff es (Seq Type, Effect, Type, Maybe (Seq Type))
splitFunctionType loc env expectedParameterCount type_ = do
    followMetas type_ >>= \case
        Function parameters effect result
            | length parameters == expectedParameterCount -> pure (parameters, effect, result, Nothing)
            | otherwise -> do
                paddedParameters <- padWithMetas expectedParameterCount parameters
                pure (paddedParameters, effect, result, Just parameters)
        type_ -> do
            parameters <- Seq.replicateM expectedParameterCount (MetaVar <$> freshTypeMeta "a")
            effect <- MetaVar <$> freshMeta "e" Effect
            result <- MetaVar <$> freshTypeMeta "b"
            subsumes loc env type_ (Function parameters effect result)
            pure (parameters, effect, result, Nothing)

representationOfType :: (TypeCheck es) => Loc -> Env -> Type -> Eff es Kind
representationOfType loc env type_ =
    kindOf loc env type_ >>= \case
        Type repr -> pure repr
        kind -> do
            representationMeta <- MetaVar <$> freshMeta "r" Rep
            unify loc env kind (Type representationMeta)
            pure representationMeta

substituteTypeVariables :: (TypeCheck es) => (HashMap LocalName Type) -> Type -> Eff es Type
substituteTypeVariables substitution type_ =
    followMetas type_ >>= \case
        type_@TypeConstructor{} -> pure type_
        TypeApplication typeConstructor arguments -> do
            typeConstructor <- substituteTypeVariables substitution typeConstructor
            arguments <- traverse (substituteTypeVariables substitution) arguments
            pure (TypeApplication typeConstructor arguments)
        type_@(TypeVar name) -> case lookup name substitution of
            Just substituted -> pure substituted
            Nothing -> pure type_
        Forall binders body -> do
            binders <- for binders \MkForallBinder{varName, visibility, kind, monomorphization} -> do
                kind <- substituteTypeVariables substitution kind
                pure (MkForallBinder{varName, visibility, kind, monomorphization})
            body <- substituteTypeVariables substitution body
            pure (Forall binders body)
        Exists binders body -> do
            binders <- for binders \(name, kind) -> do
                kind <- substituteTypeVariables substitution kind
                pure (name, kind)
            body <- substituteTypeVariables substitution body
            pure (Exists binders body)
        Function parameters effect result -> do
            parameters <- traverse (substituteTypeVariables substitution) parameters
            effect <- substituteTypeVariables substitution effect
            result <- substituteTypeVariables substitution result
            pure (Function parameters effect result)
        TypeFunction parameters result -> do
            parameters <- traverse (substituteTypeVariables substitution) parameters
            result <- substituteTypeVariables substitution result
            pure (TypeFunction parameters result)
        Tuple elements -> do
            elements <- traverse (substituteTypeVariables substitution) elements
            pure (Tuple elements)
        -- Because we ran followMetas on type_, this has to be an unsubstituted MetaVar
        type_@MetaVar{} -> pure type_
        type_@Skolem{} -> pure type_
        type_@Pure -> pure type_
        type_@Rep -> pure type_
        Type rep -> do
            rep <- substituteTypeVariables substitution rep
            pure (Type rep)
        type_@Effect -> pure type_
        SumRep elements -> do
            elements <- traverse (substituteTypeVariables substitution) elements
            pure (SumRep elements)
        ProductRep elements -> do
            elements <- traverse (substituteTypeVariables substitution) elements
            pure (ProductRep elements)
        ArrayRep inner -> do
            inner <- substituteTypeVariables substitution inner
            pure (ArrayRep inner)
        type_@PrimitiveRep{} -> pure type_
        type_@Kind -> pure type_

binaryOperatorType :: BinaryOperator -> (Type, Type, Type)
binaryOperatorType = \case
    Add -> (intType, intType, intType)
    Subtract -> (intType, intType, intType)
    Multiply -> (intType, intType, intType)
    Divide -> (intType, intType, intType)
    And -> (boolType, boolType, boolType)
    Or -> (boolType, boolType, boolType)
    Less -> (intType, intType, boolType)
    LessEqual -> (intType, intType, boolType)
    Equal -> (intType, intType, boolType)
    NotEqual -> (intType, intType, boolType)
    GreaterEqual -> (intType, intType, boolType)
    Greater -> (intType, intType, boolType)

data InstantiationResult
    = -- | Stop instantiating and keep the affected binder intact
      StopInstantiating
    | -- | Instantiate this parameter with the given type but stop after it
      LastInstantiation Type
    | -- | Instantiate this type parameter with the given type and keep going
      InstantiateWith Type

instantiateToMetaStrategy :: (TypeCheck es) => Loc -> Env -> ForallBinder -> Eff es InstantiationResult
instantiateToMetaStrategy loc env MkForallBinder{varName, visibility = _, kind, monomorphization} = do
    meta <- MetaVar <$> freshMeta varName.name kind
    assertMonomorphizability loc env meta monomorphization
    pure (InstantiateWith meta)

instantiateExistentialToMetaStrategy :: (TypeCheck es) => Loc -> Env -> LocalName -> Kind -> Eff es InstantiationResult
instantiateExistentialToMetaStrategy _loc _env varName kind = do
    meta <- MetaVar <$> freshMeta varName.name kind
    pure (InstantiateWith meta)

skolemizeStrategy :: (TypeCheck es) => Loc -> Env -> ForallBinder -> Eff es InstantiationResult
skolemizeStrategy _loc _env MkForallBinder{varName, visibility = _, kind, monomorphization} = do
    skolem <- Skolem <$> freshSkolem varName monomorphization kind
    pure (InstantiateWith skolem)

skolemizeExistentialStrategy :: (TypeCheck es) => Loc -> Env -> LocalName -> Kind -> Eff es InstantiationResult
skolemizeExistentialStrategy _loc _env varName kind = do
    skolem <- Skolem <$> freshSkolem varName Parametric kind
    pure (InstantiateWith skolem)

data GenericInstantiation es = MkGenericInstantiation
    { onInferred :: Loc -> Env -> ForallBinder -> Eff es InstantiationResult
    , onVisible :: Loc -> Env -> ForallBinder -> Eff es InstantiationResult
    , onExistential :: Loc -> Env -> LocalName -> Kind -> Eff es InstantiationResult
    }

instantiateGeneric ::
    forall es.
    (TypeCheck es) =>
    GenericInstantiation es ->
    Loc ->
    Env ->
    Type ->
    Eff es Type
instantiateGeneric instantiation loc env type_ = do
    let (binders, body) = collectPrenexBinders type_

    case binders of
        [] -> pure type_
        _ -> do
            let substituteForallBinder substitution MkForallBinder{varName, visibility, kind, monomorphization} = do
                    kind <- substituteTypeVariables substitution kind
                    pure (MkForallBinder{varName, visibility, kind, monomorphization})

            let substituteExistentialBinder substitution (varName, kind) = do
                    kind <- substituteTypeVariables substitution kind
                    pure (varName, kind)

            let go substitution = \case
                    Empty -> substituteTypeVariables substitution body
                    binder :<| remainingBinders -> do
                        (varName, result) <- case binder of
                            Left forallBinder -> do
                                forallBinder <- substituteForallBinder substitution forallBinder

                                result <- case forallBinder.visibility of
                                    Inferred -> instantiation.onInferred loc env forallBinder
                                    Visible -> instantiation.onVisible loc env forallBinder
                                pure (forallBinder.varName, result)
                            Right existentialBinder -> do
                                (varName, kind) <- substituteExistentialBinder substitution existentialBinder
                                result <- instantiation.onExistential loc env varName kind
                                pure (varName, result)
                        case result of
                            StopInstantiating -> substituteTypeVariables substitution (reAddBinders (binder :<| remainingBinders) body)
                            LastInstantiation type_ -> substituteTypeVariables (insert varName type_ substitution) (reAddBinders remainingBinders body)
                            InstantiateWith type_ -> go (insert varName type_ substitution) remainingBinders
            go mempty binders

collectPrenexBinders :: Type -> (Seq (Either ForallBinder (LocalName, Kind)), Type)
collectPrenexBinders type_ = go [] type_
  where
    go foundBinders (Forall binders body) = go (foundBinders <> fmap Left (toSeq binders)) body
    go foundBinders (Exists binders body) = go (foundBinders <> fmap Right (toSeq binders)) body
    go foundBinders rhoType = (foundBinders, rhoType)

reAddBinders :: Seq (Either ForallBinder (LocalName, Kind)) -> Type -> Type
reAddBinders binders body = case binders of
    Empty -> body
    (Left forallBinder :<| remainingBinders) -> do
        let (remainingPrefix, rest) = Util.spanMaybe (\case Left forallBinder -> Just forallBinder; Right _ -> Nothing) remainingBinders
        forall_ (forallBinder :<| remainingPrefix) (reAddBinders rest body)
    (Right existentialBinder :<| remainingBinders) -> do
        let (remainingPrefix, rest) = Util.spanMaybe (\case Right existentialBinder -> Just existentialBinder; Left _ -> Nothing) remainingBinders
        Exists (existentialBinder :<|| remainingPrefix) (reAddBinders rest body)

instantiateWith :: (TypeCheck es) => Loc -> Env -> Type -> Seq Type -> Eff es Type
instantiateWith loc env polytype initialArguments = evalState initialArguments do
    let onVisible _loc _env _forallBinder = do
            arguments <- get @(Seq Type)
            case arguments of
                Empty -> pure StopInstantiating
                (argument :<| Empty) -> do
                    put @(Seq Type) Empty
                    pure (LastInstantiation argument)
                (argument :<| rest) -> do
                    put rest
                    pure (InstantiateWith argument)

    type_ <-
        instantiateGeneric
            MkGenericInstantiation
                { onInferred = instantiateToMetaStrategy
                , onVisible
                , onExistential = skolemizeExistentialStrategy
                }
            loc
            env
            polytype
    remainingArguments <- get @(Seq Type)
    case remainingArguments of
        Empty -> pure type_
        _ -> do
            let parameterCount = case normalizeForalls polytype of
                    Forall binders _ -> length binders
                    _ -> 0
            -- TODO: this might not be a type application
            typeError
                ( TypeApplicationWithTooFewParameters
                    { loc
                    , parameterCount
                    , typeArgumentCount = length initialArguments
                    , instantiatedType = polytype
                    }
                )
            pure type_

instantiate :: (TypeCheck es) => Loc -> Env -> Type -> Eff es Type
instantiate loc env type_ =
    instantiateGeneric
        MkGenericInstantiation
            { onInferred = instantiateToMetaStrategy
            , onVisible = instantiateToMetaStrategy
            , onExistential = skolemizeExistentialStrategy
            }
        loc
        env
        type_

skolemize :: (TypeCheck es) => Loc -> Env -> Type -> Eff es Type
skolemize loc env type_ =
    instantiateGeneric
        MkGenericInstantiation
            { onInferred = skolemizeStrategy
            , onVisible = skolemizeStrategy
            , onExistential = instantiateExistentialToMetaStrategy
            }
        loc
        env
        type_

{- | Collect repeated foralls into a single one.
For example, this will turn `forall a b. forall c d. Int` into `forall a b c d. Int`

This is a very cheap operation (O(#foralls))
-}
normalizeForalls :: Type -> Type
normalizeForalls = go []
  where
    go totalBinders (Forall binders body) = go (totalBinders <> toSeq binders) body
    go totalBinders type_ = forall_ totalBinders type_

subsumes :: (TypeCheck es) => Loc -> Env -> Type -> Type -> Eff es ()
subsumes loc env subtype supertype = do
    subtype <- instantiate loc env subtype
    supertype <- skolemize loc env supertype
    unify loc env subtype supertype

unify :: (HasCallStack, TypeCheck es) => Loc -> Env -> Type -> Type -> Eff es ()
unify loc env type1 type2 = withTrace Unify (pretty type1 <+> keyword "~" <+> pretty type2) $ go type1 type2
  where
    go type1 type2 = do
        let unificationFailure = typeError (UnableToUnify{loc, expectedType = type2, actualType = type1})
        type1 <- followMetas type1
        type2 <- followMetas type2
        trace UnifyAll (pretty type1 <+> keyword "~" <+> pretty type2)
        case (type1, type2) of
            (!type1, !type2) | isTrue# (reallyUnsafePtrEquality type1 type2) -> pure ()
            (MetaVar meta1, _) -> bindMeta loc env meta1 type2
            (_, MetaVar meta2) -> bindMeta loc env meta2 type1
            _ ->
                case type1 of
                    TypeConstructor name1 -> case type2 of
                        TypeConstructor name2
                            | name1 == name2 -> pure ()
                        _ -> unificationFailure
                    TypeApplication typeConstructor1 arguments1 -> case type2 of
                        TypeApplication typeConstructor2 arguments2
                            | length arguments1 == length arguments2 -> do
                                go typeConstructor1 typeConstructor2
                                _ <- zipWithSeqM go arguments1 arguments2
                                pure ()
                        _ -> unificationFailure
                    TypeVar name -> error $ "unsubstituted type variable in unification: " <> show name
                    Forall binders1 body1 -> case type2 of
                        Forall binders2 body -> do
                            undefined
                        _ -> unificationFailure
                    Exists binders1 body1 -> do
                        -- To unify two existentials, we have to check that they are
                        -- mutual subtypes
                        unifyExistentialSubtype loc env type1 type2
                        unifyExistentialSubtype loc env type2 type1
                    Function parameters1 effect1 result1 -> case type2 of
                        Function parameters2 effect2 result2
                            | length parameters1 == length parameters2 -> do
                                _ <- zipWithSeqM go parameters1 parameters2
                                go effect1 effect2
                                go result1 result2
                        _ -> unificationFailure
                    TypeFunction parameters1 result1 -> case type2 of
                        TypeFunction parameters2 result2
                            | length parameters1 == length parameters2 -> do
                                _ <- zipWithSeqM go parameters1 parameters2
                                go result1 result2
                        _ -> unificationFailure
                    Tuple elements1 -> case type2 of
                        Tuple elements2
                            | length elements1 == length elements2 -> do
                                _ <- zipWithSeqM go elements1 elements2
                                pure ()
                        _ -> unificationFailure
                    Skolem skolem1 -> case type2 of
                        Skolem skolem2
                            | skolem1 == skolem2 -> pure ()
                        _ -> unificationFailure
                    Pure -> case type2 of
                        Pure -> pure ()
                        _ -> unificationFailure
                    Rep -> case type2 of
                        Rep -> pure ()
                        _ -> unificationFailure
                    Type rep1 -> case type2 of
                        Type rep2 -> go rep1 rep2
                        _ -> unificationFailure
                    Effect -> case type2 of
                        Effect -> pure ()
                        _ -> unificationFailure
                    SumRep elements1 -> case type2 of
                        SumRep elements2
                            | length elements1 == length elements2 -> do
                                _ <- zipWithSeqM go elements1 elements2
                                pure ()
                        _ -> unificationFailure
                    ProductRep elements1 -> case type2 of
                        ProductRep elements2
                            | length elements1 == length elements2 -> do
                                _ <- zipWithSeqM go elements1 elements2
                                pure ()
                        _ -> unificationFailure
                    ArrayRep rep1 -> case type2 of
                        ArrayRep rep2 -> go rep1 rep2
                        _ -> unificationFailure
                    PrimitiveRep rep1 -> case type2 of
                        PrimitiveRep rep2
                            | rep1 == rep2 -> pure ()
                        _ -> unificationFailure
                    Kind -> case type2 of
                        Kind -> pure ()
                        _ -> unificationFailure

{- | Ensure that the first type is a subtype of the second one, only considering existential quantifiers.
Notably, this will *not* take Foralls into account
-}
unifyExistentialSubtype :: (TypeCheck es) => Loc -> Env -> Type -> Type -> Eff es ()
unifyExistentialSubtype loc env subtype supertype =
    followMetas subtype >>= \case
        Exists{} -> do
            subtype <- instantiate loc env subtype
            unifyExistentialSubtype loc env subtype supertype
        type1 ->
            followMetas supertype >>= \case
                Exists{} -> do
                    supertype <- skolemize loc env supertype
                    unifyExistentialSubtype loc env subtype supertype
                type2 -> unify loc env type1 type2

bindMeta :: (TypeCheck es) => Loc -> Env -> MetaVar -> Type -> Eff es ()
bindMeta loc env meta boundType = withTrace Unify (pretty meta <+> keyword ":=" <+> pretty boundType) do
    followMetas (MetaVar meta) >>= \case
        MetaVar meta -> do
            followMetas boundType >>= \case
                MetaVar meta2
                    -- ?a ~ ?a constraints are technically harmless but cause problems for the type checker
                    -- so we need to handle them separately
                    | meta == meta2 -> pure ()
                boundType -> do
                    -- TODO: include some sort of note to make it clear where the kind came from
                    checkEvaluatedType loc env meta.kind boundType
                    occursAndAdjust meta boundType >>= \case
                        True -> do
                            -- This will make more sense once we have more context to the unification
                            -- TODO: until then, the order doesn't really make sense here
                            typeError OccursCheckViolation{loc, actualType = boundType, expectedType = MetaVar meta, meta}
                        False -> bindMetaUnchecked meta boundType
        _ -> error $ "Trying to bind unbound meta variable"

occursAndAdjust :: (TypeCheck es) => MetaVar -> Type -> Eff es Bool
occursAndAdjust meta type_ = do
    -- TODO: adjust levels
    runErrorNoCallStack (go type_) >>= \case
        Left () -> pure True
        Right () -> pure False
  where
    go type_ =
        followMetas type_ >>= \case
            TypeConstructor{} -> pure ()
            TypeApplication typeConstructor arguments -> do
                go typeConstructor
                for_ arguments go
            TypeVar{} -> pure ()
            Forall _typeVarBinders body -> do
                -- TODO: do we need to look into kinds here? (and likewise for existentials)
                go body
            Exists _binders body -> go body
            Function parameters effect result -> do
                for_ parameters go
                go effect
                go result
            TypeFunction parameters result -> do
                for_ parameters go
                go result
            Tuple elements -> for_ elements go
            MetaVar foundMeta
                | meta == foundMeta ->
                    throwError_ ()
                -- Because we ran followMetas on type_, this is an unbound meta var that we don't need to look into further
                | otherwise -> pure ()
            Skolem{} -> pure ()
            Pure -> pure ()
            Rep -> pure ()
            Type rep -> go rep
            Effect -> pure ()
            SumRep elements -> for_ elements go
            ProductRep elements -> for_ elements go
            ArrayRep inner -> go inner
            PrimitiveRep{} -> pure ()
            Kind -> pure ()

subsumesEffect :: (TypeCheck es) => Effect -> Effect -> Eff es ()
subsumesEffect eff1 eff2 = do
    eff1 <- followMetas eff1
    eff2 <- followMetas eff2
    case (eff1, eff2) of
        (Pure, _) -> pure ()
        -- stubbed out for now while we figure out what exactly to do
        _ -> pure ()

union :: (TypeCheck es) => Effect -> Effect -> Eff es Effect
union Pure eff = pure eff
union eff Pure = pure eff
union _ _ = undefined

unionM :: (TypeCheck es) => Eff es Effect -> Eff es Effect -> Eff es Effect
unionM eff1M eff2M = do
    eff1 <- eff1M
    eff2 <- eff2M
    eff1 `union` eff2

unionAll :: (TypeCheck es) => Seq Effect -> Eff es Effect
unionAll Empty = pure Pure
unionAll (eff :<| rest) = pure eff `unionM` unionAll rest

-- | Creates a fresh meta variable of kind (Type ?r) where ?r is another fresh meta variable
freshTypeMeta :: (TypeCheck es) => Text -> Eff es MetaVar
freshTypeMeta name = do
    rep <- MetaVar <$> freshMeta "r" Rep
    freshMeta name (Type rep)

dummyMetaOfUnknownKind :: (TypeCheck es) => Eff es Type
dummyMetaOfUnknownKind = do
    metaKind <- MetaVar <$> freshMeta "k" Kind
    dummyMeta <- MetaVar <$> freshMeta "err" metaKind
    trace TypeCheck $ "dummyMetaOfUnknownKind" <+> keyword "~>" <+> pretty dummyMeta <+> keyword ":" <+> pretty metaKind
    pure dummyMeta

freshSkolem :: (TypeCheck es) => LocalName -> Monomorphization -> Kind -> Eff es Skolem
freshSkolem originalName monomorphization kind = do
    identity <- newUnique
    pure $ MkSkolem{identity, originalName, monomorphization, kind}

assertMonomorphizability :: (TypeCheck es) => Loc -> Env -> Type -> Monomorphization -> Eff es ()
assertMonomorphizability loc env type_ = \case
    Monomorphized -> monomorphized loc env type_
    Parametric -> pure ()

monomorphized :: (TypeCheck es) => Loc -> Env -> Type -> Eff es ()
monomorphized loc env type_ = do
    trace TypeCheck $ emphasis "mono" <+> pretty type_
    solveMonomorphized (\meta -> output (AssertMonomorphized loc env (MetaVar meta))) loc env type_

solveMonomorphized :: (TypeCheckCore es) => (MetaVar -> Eff es ()) -> Loc -> Env -> Type -> Eff es ()
solveMonomorphized onMetaVar loc env type_ =
    go type_
  where
    go type_ =
        followMetas type_ >>= \case
            -- the interesting cases
            TypeVar varName -> do
                case typeVariableMonomorphization varName env of
                    Monomorphized -> pure ()
                    Parametric -> typeError (ParametricVariableInMono{loc, varName, fullType = Nothing})
            Skolem skolem -> do
                case skolem.monomorphization of
                    Monomorphized -> pure ()
                    -- TODO: should we use a separate error message for skolems?
                    Parametric -> typeError (ParametricVariableInMono{loc, varName = skolem.originalName, fullType = Nothing})
            MetaVar meta -> onMetaVar meta
            -- recursive boilerplate
            TypeConstructor{} -> pure ()
            TypeApplication constructor arguments -> do
                go constructor
                for_ arguments go
            Forall binders body -> do
                for_ binders \MkForallBinder{kind} -> go kind
                go body
            Exists binders body -> do
                for_ binders \(_, kind) -> go kind
                go body
            Function parameters effect result -> do
                for_ parameters go
                go effect
                go result
            TypeFunction parameters result -> do
                for_ parameters go
                go result
            Tuple elements -> do
                for_ elements go
            Pure -> pure ()
            Rep -> pure ()
            Type rep -> go rep
            Effect -> pure ()
            SumRep elements -> for_ elements go
            ProductRep elements -> for_ elements go
            ArrayRep inner -> go inner
            PrimitiveRep{} -> pure ()
            Kind -> pure ()

type SolveConstraints es = (Error TypeError :> es, Output TypeError :> es, Trace :> es, ReadMeta :> es, BindMeta :> es)

solveConstraints :: (SolveConstraints es) => List DeferredConstraint -> Eff es ()
solveConstraints = \case
    [] -> pure ()
    (AssertMonomorphized loc env type_ : rest) -> do
        solveMonomorphized
            ( \_meta ->
                -- If this gets called, we know that the meta variable was definitely unused and so we could default it to
                -- whatever we want, including () which is monomorphizable and satisfies this constraint.
                -- (Note that we don't *literally* assign the meta variable since we don't want to mess up error messages.
                -- Instead, Core generation gives unbound unification variables a `Unit` representation, which accomplishes
                -- the same goal.)
                pure ()
            )
            loc
            env
            type_
        solveConstraints rest

{- NOTE [Kinds of foralls]:
------------------------------
What should the kind of `forall (a : k). t` be? In any situation where this question actually makes sense to ask,
the forall will only bind parametric type variables that cannot end up in t's kind, so the kind is just the kind of `t`.
But in *top level definitions*, we may have monomorphizable bindings that may very well end up in their respective kinds
(e.g. in the definition of `Nil`).
In these cases, we still defer to the representation of the kinds body, since we know that there will never be any
sensible operation performed on the result.

Should this ever cause problems (for example because the skolems in the resulting kind escape their scope), we
may need to give the result a dummy kind like `MonomorphizableForall` instead.
-}
