{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Vega.TypeCheck (checkDeclaration) where

import Vega.Syntax

import Effectful hiding (Effect)
import Relude hiding (State, Type, evalState, get, put, runState, trace)
import Relude.Extra

import Vega.Error (TypeError (..), TypeErrorSet (MkTypeErrorSet))
import Vega.Util (compose, mapAccumLM, unzip3Seq, viaList, zipWithSeqM)

import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Data.Unique (Unique, newUnique)
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError, throwError_)
import Effectful.State.Static.Local (State, evalState, get, put, runState)
import GHC.Generics qualified as Generics
import GHC.List (List)
import Vega.Debug (showHeadConstructor)
import Vega.Effect.Output.Static.Local (Output, output, runOutputList, runOutputSeq)
import Vega.Effect.Trace (Category (..), Trace, trace, withTrace)
import Vega.Loc (HasLoc (getLoc), Loc)
import Vega.Pretty (emphasis, errorText, keyword, pretty, (<+>))
import Vega.TypeCheck.Zonk (zonk)
import Vega.Util (assert)
import Vega.Util qualified as Util
import qualified Vega.Seq.NonEmpty as NonEmpty
import Vega.Seq.NonEmpty (toSeq)

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
    , IOE :> es
    , Output TypeError :> es
    , Error TypeError :> es
    )

-- TODO: factor out the reference/unique bits so you don't need full IOE
type TypeCheck es =
    ( GraphPersistence :> es
    , Output DeferredConstraint :> es
    , Output TypeError :> es
    , Error TypeError :> es
    , Trace :> es
    , IOE :> es
    )

-- TODO: does it make sense to return the declaration anyway even if we have errors?
-- We already have the *renamed* syntax so I'm not sure if this is really beneficial
-- (in any case, we can't just compile it if it has type errors so there isn't that much
-- we could do with it anyway. it might help the LSP though)
checkDeclaration :: (GraphPersistence :> es, Trace :> es, IOE :> es) => Declaration Renamed -> Eff es (Either TypeErrorSet (Declaration Typed))
checkDeclaration (MkDeclaration{loc, name, syntax}) = withTrace TypeCheck ("Declaration: " <> pretty name) do
    ((syntaxOrFatalError, deferredConstraints), nonFatalDirectErrors) <-
        runOutputSeq @TypeError $
            runOutputList @DeferredConstraint $
                runErrorNoCallStack @TypeError $
                    checkDeclarationSyntax loc syntax

    (fatalSolverError, nonFatalSolverErrors) <- runOutputSeq @TypeError $ runErrorNoCallStack @TypeError $ solveConstraints deferredConstraints

    let nonFatalErrors = nonFatalDirectErrors <> nonFatalSolverErrors
    let fatalErrorsOrSyntax = case (syntaxOrFatalError, fatalSolverError) of
            (Left error1, Left error2) -> Left [error1, error2]
            (Left error1, Right ()) -> Left [error1]
            (Right _, Left error2) -> Left [error2]
            (Right syntax, Right ()) -> Right syntax

    case fatalErrorsOrSyntax of
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
    GraphPersistence.getGlobalType name >>= \case
        Left cachedType -> do
            trace TypeCheck $ "cached ~> " <> pretty cachedType
            pure cachedType
        Right syntax -> do
            (_rep, type_, _) <- inferTypeRep emptyEnv syntax
            GraphPersistence.cacheGlobalType name type_
            pure type_

globalConstructorKind :: (TypeCheck es) => GlobalName -> Eff es Kind
globalConstructorKind name = do
    GraphPersistence.getGlobalKind name >>= \case
        Left cachedKind -> pure cachedKind
        Right syntax -> do
            (kind, _synax) <- checkType emptyEnv Parametric Kind syntax
            GraphPersistence.cacheGlobalKind name kind
            pure kind

checkDeclarationSyntax :: (TypeCheck es) => Loc -> DeclarationSyntax Renamed -> Eff es (DeclarationSyntax Typed)
checkDeclarationSyntax loc = \case
    DefineFunction{name, typeSignature, declaredTypeParameters, parameters, body} -> do
        let env = emptyEnv
        (functionType, typeSignature) <- checkType env Parametric (Type BoxedRep) typeSignature

        (env, remainingType) <- bindTypeParameters loc env declaredTypeParameters functionType

        -- We bound the declared type parameters above and the rest are not accessible in the body
        -- so we can just skolemize them away here
        remainingType <- skolemize loc env remainingType
        (parameterTypes, effect, returnType) <- splitFunctionType loc env (length parameters) remainingType

        when (length parameters /= length parameterTypes) $ do
            typeError
                ( FunctionDefinedWithIncorrectNumberOfArguments
                    { loc
                    , functionName = name
                    , expectedType = functionType
                    , expectedNumberOfArguments = length parameterTypes
                    , numberOfDefinedParameters = length parameters
                    }
                )

        let checkParameter pattern_ type_ = do
                checkPattern env type_ pattern_

        (parameters, transformers) <- Seq.unzip <$> zipWithSeqM checkParameter parameters parameterTypes
        env <- pure (compose transformers env)

        (body, bodyEffect) <- check env returnType body
        subsumesEffect bodyEffect effect

        pure DefineFunction{name, typeSignature, declaredTypeParameters, parameters, body}
    DefineVariantType{name, typeParameters, constructors} -> do
        let env = emptyEnv
        (env, binders) <- mapAccumLM applyForallBinder env typeParameters
        let typeParameters = fmap (\(_, binder) -> binder) binders

        constructors <- for constructors \(name, loc, parameters) -> do
            -- TODO: we need the representations, right??
            (representations, _, parameters) <- unzip3Seq <$> traverse (inferTypeRep env) parameters
            pure (name, loc, parameters)
        pure (DefineVariantType{name, typeParameters, constructors})

checkPattern :: (TypeCheck es) => Env -> Type -> Pattern Renamed -> Eff es (Pattern Typed, Env -> Env)
checkPattern env expectedType = \case
    VarPattern loc var -> pure (VarPattern loc var, bindVarType var expectedType)
    AsPattern loc pattern_ name -> do
        (pattern_, innerTrans) <- checkPattern env expectedType pattern_
        pure (AsPattern loc pattern_ name, bindVarType name expectedType . innerTrans)
    ConstructorPattern{} -> undefined
    TypePattern loc innerPattern innerTypeSyntax -> do
        (_typeRep, innerType, innerTypeSyntax) <- inferTypeRep env innerTypeSyntax
        (innerPattern, innerTrans) <- checkPattern env innerType innerPattern
        subsumes loc env innerType expectedType
        pure (TypePattern loc innerPattern innerTypeSyntax, innerTrans)
    OrPattern{} -> undefined
    _ -> undefined

inferPattern :: (TypeCheck es) => Env -> Pattern Renamed -> Eff es (Pattern Typed, Type, Env -> Env)
inferPattern env = \case
    VarPattern loc varName -> do
        type_ <- MetaVar <$> freshTypeMeta loc env (varName.name)
        pure (VarPattern loc varName, type_, bindVarType varName type_)
    AsPattern loc innerPattern name -> do
        (innerPattern, innerType, innerTrans) <- inferPattern env innerPattern
        pure (AsPattern loc innerPattern name, innerType, bindVarType name innerType . innerTrans)
    _ -> undefined

check :: (TypeCheck es) => Env -> Type -> Expr Renamed -> Eff es (Expr Typed, Effect)
check env expectedType expr = withTrace TypeCheck ("check:" <+> showHeadConstructor expr <+> keyword "<=" <+> pretty expectedType) do
    let deferToInference = do
            (actualType, expr, effect) <- infer env expr
            subsumes (getLoc expr) env actualType expectedType
            pure (expr, effect)
    case expr of
        Var{} -> deferToInference
        DataConstructor{} -> undefined
        Application{} -> deferToInference
        -- TODO: not entirely sure if this is correct or if we should try to stay in check mode
        VisibleTypeApplication{} -> deferToInference
        Lambda loc typeParameters parameters body -> do
            (env, typeWithoutBoundParameters) <- bindTypeParameters loc env typeParameters expectedType

            -- Any type variables *not* bound above are not going to be available in the body
            -- and so are just skolemized away here
            resultingType <- skolemize loc env typeWithoutBoundParameters
            (parameterTypes, expectedEffect, returnType) <- splitFunctionType loc env (length parameters) resultingType
            when (length parameters /= length parameterTypes) do
                typeError
                    ( LambdaDefinedWithIncorrectNumberOfArguments
                        { loc
                        , expectedType
                        , expected = length parameterTypes
                        , actual = length parameters
                        }
                    )

            let checkParameter parameter parameterType = do
                    checkPattern env parameterType parameter
            (parameters, envTransformers) <- Seq.unzip <$> zipWithSeqM checkParameter parameters parameterTypes
            (body, bodyEffect) <- check (compose envTransformers env) returnType body
            subsumesEffect bodyEffect expectedEffect
            pure (Lambda loc typeParameters parameters body, Pure)
        StringLiteral{} -> deferToInference
        IntLiteral{} -> deferToInference
        DoubleLiteral{} -> deferToInference
        If{loc, condition, thenBranch, elseBranch} -> do
            (condition, conditionEffect) <- check env boolType condition
            (thenBranch, thenEffect) <- check env expectedType thenBranch
            (elseBranch, elseEffect) <- check env expectedType elseBranch

            effect <- unionAll [conditionEffect, thenEffect, elseEffect]
            pure (If{loc, condition, thenBranch, elseBranch}, effect)
        SequenceBlock{loc, statements} -> do
            undefined
        TupleLiteral loc elements -> do
            elementTypes <-
                followMetas expectedType >>= \case
                    Tuple elementTypes -> pure elementTypes
                    _ -> do
                        elementTypes <- for elements \_ -> do
                            MetaVar <$> freshTypeMeta loc env "t"
                        subsumes loc env (Tuple elementTypes) expectedType
                        pure elementTypes
            when (length elementTypes /= length elements) do
                undefined

            (elements, effects) <- fmap Seq.unzip $ for (Seq.zip elements elementTypes) \(element, elementType) -> do
                check env elementType element

            effect <- unionAll effects
            pure (TupleLiteral loc elements, effect)
        PartialApplication{} -> undefined
        BinaryOperator{} -> undefined
        Match{} -> undefined

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
    remainingType <- instantiateGeneric skolemizeStrategy onVisible loc env polytype
    parameters <- get @(List (Loc, LocalName))
    case parameters of
        [] -> pure remainingType
        _ -> do
            let actualCount = case normalizeForalls polytype of
                    Forall binders _ -> length binders
                    _ -> 0
            typeError (TryingToBindTooManyTypeParameters{loc, boundCount = length initialParameters, actualCount, type_ = polytype})
            pure remainingType

varType :: (HasCallStack) => (TypeCheck es) => Env -> Name -> Eff es Type
varType env name = case name of
    Global globalName -> getGlobalType globalName
    Local localName -> do
        case lookup localName env.localTypes of
            Just type_ -> pure type_
            Nothing -> error ("variable not found in renamer: " <> show name)

infer :: (TypeCheck es) => Env -> Expr Renamed -> Eff es (Type, Expr Typed, Effect)
infer env expr = do
    (type_, expr, effect) <- withTrace TypeCheck ("infer " <> showHeadConstructor expr) go
    trace TypeCheck ("infer" <> showHeadConstructor expr <> keyword " => " <> pretty type_ <> keyword " | " <> pretty effect)
    pure (type_, expr, effect)
  where
    go = case expr of
        Var loc name -> do
            type_ <- instantiate loc env =<< varType env name
            pure (type_, Var loc name, Pure)
        Application{loc, functionExpr, arguments} -> do
            (functionType, functionExpr, functionExprEffect) <- infer env functionExpr
            (argumentTypes, functionEffect, returnType) <- splitFunctionType loc env (length arguments) functionType
            when (length argumentTypes /= length arguments) do
                typeError $
                    FunctionAppliedToIncorrectNumberOfArgs
                        { loc
                        , expected = length argumentTypes
                        , actual = length arguments
                        , functionType
                        }
            let checkArguments argumentExpr argumentType = do
                    check env argumentType argumentExpr
            (arguments, argumentEffects) <- Seq.unzip <$> zipWithSeqM checkArguments arguments argumentTypes
            finalEffect <- pure functionExprEffect `unionM` unionAll argumentEffects `unionM` pure functionEffect
            pure (returnType, Application{loc, functionExpr, arguments}, finalEffect)
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
            pure (type_, VisibleTypeApplication{loc, varName, typeArguments = typeArgumentSyntax}, Pure)
        Lambda loc typeParameters parameters body -> do
            case typeParameters of
                [] -> pure ()
                _ -> undefined -- error? I don't think we can handle type parameters in infer mode
            (parameters, parameterTypes, envTransformers) <- unzip3Seq <$> traverse (inferPattern env) parameters

            (bodyType, body, bodyEffect) <- infer (compose envTransformers env) body

            pure (Function parameterTypes bodyEffect bodyType, Lambda loc typeParameters parameters body, Pure)
        StringLiteral loc literal -> pure (stringType, StringLiteral loc literal, Pure)
        IntLiteral loc literal -> pure (intType, IntLiteral loc literal, Pure)
        DoubleLiteral loc literal -> pure (doubleType, DoubleLiteral loc literal, Pure)
        BinaryOperator{} -> undefined
        If{loc, condition, thenBranch, elseBranch} -> do
            (condition, conditionEffect) <- check env boolType condition
            (thenType, thenBranch, thenEffect) <- infer env thenBranch
            (elseType, elseBranch, elseEffect) <- infer env elseBranch
            subsumes loc env thenType elseType
            subsumes loc env elseType thenType
            effect <- unionAll [conditionEffect, thenEffect, elseEffect]
            pure (thenType, If{loc, condition, thenBranch, elseBranch}, effect)
        _ -> undefined

stringType :: Type
stringType = TypeConstructor (Global (internalName "String"))

intType :: Type
intType = TypeConstructor (Global (internalName "Int"))

doubleType :: Type
doubleType = TypeConstructor (Global (internalName "Double"))

boolType :: Type
boolType = TypeConstructor (Global (internalName "Bool"))

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
    trace KindCheck ("inferType: " <> showHeadConstructor syntax <+> keyword ">=" <+> pretty kind <+> keyword "~>" <+> pretty type_)
    pure (kind, type_, syntax)
  where
    go = case syntax of
        TypeConstructorS loc name -> do
            kind <- constructorKind env name
            pure (kind, TypeConstructor name, TypeConstructorS loc name)
        TypeApplicationS loc typeConstructorSyntax argumentsSyntax -> do
            (constructorKind, typeConstructor, typeConstructorSyntax) <- inferType env typeConstructorSyntax
            case constructorKind of
                Function argumentKinds Pure resultKind
                    | length argumentKinds == length argumentsSyntax -> do
                        (arguments, argumentsSyntax) <- Seq.unzip <$> zipWithSeqM (checkType env Parametric) argumentKinds argumentsSyntax
                        pure
                            ( resultKind
                            , TypeApplication typeConstructor arguments
                            , TypeApplicationS loc typeConstructorSyntax argumentsSyntax
                            )
                    | otherwise -> do
                        -- TODO: make this non-fatal. This will probably involve using some sort of 'Bottom' type we insert
                        -- for kinds we couldn't determine to suppress further spurious kind errors.
                        fatalTypeError
                            ( TypeConstructorAppliedToIncorrectNumberOfArguments
                                { loc
                                , type_ = typeConstructor
                                , kind = constructorKind
                                , expectedNumber = length argumentKinds
                                , actualNumber = length argumentsSyntax
                                }
                            )
                kind -> do
                    undefined
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
                , Forall typeVarBinders body
                , ForallS loc typeVarBinderSyntax bodySyntax
                )
        PureFunctionS loc parameters result -> do
            (_parameterReps, parameterTypes, parameterTypeSyntax) <- unzip3Seq <$> traverse (inferTypeRep env) parameters
            (_resultRep, resultType, resultTypeSyntax) <- inferTypeRep env result
            pure (Type BoxedRep, Function parameterTypes Pure resultType, PureFunctionS loc parameterTypeSyntax resultTypeSyntax)
        FunctionS loc parameters effect result -> do
            (_parameterReps, parameterTypes, parameterTypeSyntax) <- unzip3Seq <$> traverse (inferTypeRep env) parameters
            (effect, effectSyntax) <- checkType env Parametric Effect effect
            (_resultRep, resultType, resultTypeSyntax) <- inferTypeRep env result
            pure (Type BoxedRep, Function parameterTypes effect resultType, FunctionS loc parameterTypeSyntax effectSyntax resultTypeSyntax)
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
        UnitRepS loc -> pure (Rep, UnitRep, UnitRepS loc)
        EmptyRepS loc -> pure (Rep, EmptyRep, EmptyRepS loc)
        BoxedRepS loc -> pure (Rep, BoxedRep, BoxedRepS loc)
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

kindOf :: (TypeCheck es) => Env -> Type -> Eff es Kind
-- It's okay to match on the type directly here since we don't need to
-- follow meta variables: they already have their kind cached
-- In fact, in some cases this might be more efficient than computing the kinds
-- of their bound types
kindOf env = \case
    TypeConstructor name -> constructorKind env name
    TypeApplication funType _arguments -> do
        -- We can assume that the kinds here are correct so we only need to pick out the result
        kindOf env funType >>= \case
            Function _parameters _effect result -> do
                pure result
            _ -> undefined
    TypeVar name -> pure $ typeVariableKind name env
    Forall _bindings body -> do
        undefined
    Function{} -> pure (Type BoxedRep)
    Tuple elements -> Type . ProductRep <$> traverse (kindOf env) elements
    MetaVar meta -> pure meta.kind
    Skolem skolem -> pure skolem.kind
    Pure -> pure Effect
    Rep -> pure Kind
    Type{} -> pure Kind
    Effect -> pure Kind
    SumRep{} -> pure Rep
    ProductRep{} -> pure Rep
    UnitRep -> pure Rep
    EmptyRep -> pure Rep
    BoxedRep -> pure Rep
    Kind -> pure Kind

-- | Like checkType but on evaluated `Type`s rather than TypeSyntax
checkEvaluatedType :: (TypeCheck es) => Loc -> Env -> Kind -> Type -> Eff es ()
checkEvaluatedType loc env expectedKind type_ = do
    actualKind <- kindOf env type_
    subsumes loc env actualKind expectedKind

applyForallBinder :: (TypeCheck es) => Env -> ForallBinderS Renamed -> Eff es (Env, (ForallBinder, ForallBinderS Typed))
applyForallBinder env = \case
    UnspecifiedBinderS{loc, varName, monomorphization} -> undefined
    TypeVarBinderS{loc, visibility, monomorphization, varName, kind = kindSyntax} -> do
        (kind, kindSyntax) <- checkType env Parametric Kind kindSyntax
        -- TODO: not entirely sure if this is the right place for this
        monomorphized loc env kind
        pure
            ( bindTypeVariable varName (TypeVar varName) kind monomorphization env
            , (MkForallBinder{varName, visibility, monomorphization, kind}, TypeVarBinderS{loc, visibility, monomorphization, varName, kind = kindSyntax})
            )

splitFunctionType :: (TypeCheck es) => Loc -> Env -> Int -> Type -> Eff es (Seq Type, Effect, Type)
splitFunctionType loc env parameterCount type_ = do
    followMetas type_ >>= \case
        Function parameters effect result
            | length parameters == parameterCount -> pure (parameters, effect, result)
            | otherwise -> undefined
        type_ -> do
            parameters <- fromList . map MetaVar <$> replicateM parameterCount (freshTypeMeta loc env "a")
            effect <- MetaVar <$> freshTypeMeta loc env "e"
            result <- MetaVar <$> freshTypeMeta loc env "b"
            subsumes loc env type_ (Function parameters effect result)
            pure (parameters, effect, result)

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
        Function parameters effect result -> do
            parameters <- traverse (substituteTypeVariables substitution) parameters
            effect <- substituteTypeVariables substitution effect
            result <- substituteTypeVariables substitution result
            pure (Function parameters effect result)
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
        type_@UnitRep -> pure type_
        type_@EmptyRep -> pure type_
        type_@BoxedRep -> pure type_
        type_@Kind -> pure type_

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

skolemizeStrategy :: (TypeCheck es) => Loc -> Env -> ForallBinder -> Eff es InstantiationResult
skolemizeStrategy loc env MkForallBinder{varName, visibility = _, kind, monomorphization} = do
    skolem <- Skolem <$> freshSkolem varName monomorphization kind
    pure (InstantiateWith skolem)

instantiateGeneric ::
    forall es.
    (TypeCheck es) =>
    (Loc -> Env -> ForallBinder -> Eff es InstantiationResult) ->
    (Loc -> Env -> ForallBinder -> Eff es InstantiationResult) ->
    Loc ->
    Env ->
    Type ->
    Eff es Type
instantiateGeneric onInferred onVisible loc env type_ = case normalizeForalls type_ of
    Forall binders body -> do
        let substituteBinder substitution MkForallBinder{varName, visibility, kind, monomorphization} = do
                kind <- substituteTypeVariables substitution kind
                pure (MkForallBinder{varName, visibility, kind, monomorphization})

        let go substitution = \case
                Empty -> substituteTypeVariables substitution body
                binder :<| remainingBinders -> do
                    binder <- substituteBinder substitution binder

                    result <- case binder.visibility of
                        Inferred -> onInferred loc env binder
                        Visible -> onVisible loc env binder
                    case result of
                        StopInstantiating -> substituteTypeVariables substitution (forall_ (binder :<| remainingBinders) body)
                        LastInstantiation type_ -> substituteTypeVariables (insert binder.varName type_ substitution) (forall_ remainingBinders body)
                        InstantiateWith type_ -> go (insert binder.varName type_ substitution) remainingBinders
        go mempty (toSeq binders)
    type_ -> pure type_

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

    type_ <- instantiateGeneric instantiateToMetaStrategy onVisible loc env polytype
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
instantiate loc env type_ = instantiateGeneric instantiateToMetaStrategy instantiateToMetaStrategy loc env type_

skolemize :: (TypeCheck es) => Loc -> Env -> Type -> Eff es Type
skolemize loc env type_ = instantiateGeneric skolemizeStrategy skolemizeStrategy loc env type_

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
        case (type1, type2) of
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
                    Forall binders1 body1 -> undefined
                    Function parameters1 effect1 result1 -> case type2 of
                        Function parameters2 effect2 result2
                            | length parameters1 == length parameters2 -> do
                                _ <- zipWithSeqM go parameters1 parameters2
                                go effect1 effect2
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
                    UnitRep -> case type2 of
                        UnitRep -> pure ()
                        _ -> unificationFailure
                    EmptyRep -> case type2 of
                        EmptyRep -> pure ()
                        _ -> unificationFailure
                    BoxedRep -> case type2 of
                        BoxedRep -> pure ()
                        _ -> unificationFailure
                    Kind -> case type2 of
                        Kind -> pure ()
                        _ -> unificationFailure

bindMeta :: (TypeCheck es) => Loc -> Env -> MetaVar -> Type -> Eff es ()
bindMeta loc env meta boundType =
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
                    occursAndAdjust loc env meta boundType >>= \case
                        True -> undefined
                        False -> writeIORef meta.underlying (Just boundType)
        _ -> error $ "Trying to bind unbound meta variable"

occursAndAdjust :: (TypeCheck es) => Loc -> Env -> MetaVar -> Type -> Eff es Bool
occursAndAdjust loc env meta type_ = do
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
                go body
            Function parameters effect result -> do
                for_ parameters go
                go effect
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
            UnitRep -> pure ()
            EmptyRep -> pure ()
            BoxedRep -> pure ()
            Kind -> pure ()

subsumesEffect :: (TypeCheck es) => Effect -> Effect -> Eff es ()
subsumesEffect eff1 eff2 = do
    eff1 <- followMetas eff1
    eff2 <- followMetas eff2
    case (eff1, eff2) of
        (Pure, _) -> pure ()
        _ -> undefined

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

freshMeta :: (TypeCheck es) => Text -> Kind -> Eff es MetaVar
freshMeta name kind = do
    identity <- liftIO newUnique
    underlying <- newIORef Nothing
    pure $ MkMetaVar{underlying, identity, name, kind}

-- | Creates a fresh meta variable of kind (Type ?r) where ?r is another fresh meta variable
freshTypeMeta :: (TypeCheck es) => Loc -> Env -> Text -> Eff es MetaVar
freshTypeMeta loc env name = do
    rep <- MetaVar <$> freshMeta "r" Rep
    -- TODO: I'm not sure if we actually need this?
    monomorphized loc env rep
    freshMeta name (Type rep)

freshSkolem :: (TypeCheck es) => LocalName -> Monomorphization -> Kind -> Eff es Skolem
freshSkolem originalName monomorphization kind = do
    identity <- liftIO newUnique
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
            Forall{} -> undefined -- not entirely sure about this
            Function parameters effect result -> do
                for_ parameters go
                go effect
                go result
            Tuple elements -> do
                for_ elements go
            Pure -> pure ()
            Rep -> pure ()
            Type rep -> go rep
            Effect -> pure ()
            SumRep elements -> for_ elements go
            ProductRep elements -> for_ elements go
            UnitRep -> pure ()
            EmptyRep -> pure ()
            BoxedRep -> pure ()
            Kind -> pure ()

type SolveConstraints es = (Error TypeError :> es, Output TypeError :> es, Trace :> es, IOE :> es)

solveConstraints :: (SolveConstraints es) => List DeferredConstraint -> Eff es ()
solveConstraints = \case
    [] -> pure ()
    (AssertMonomorphized loc env type_ : rest) -> do
        solveMonomorphized (\meta -> typeError (AmbiguousMono{loc, type_ = MetaVar meta})) loc env type_
        solveConstraints rest
