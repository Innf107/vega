{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Vega.TypeCheck (checkDeclaration) where

import Vega.Syntax

import Effectful hiding (Effect)
import Relude hiding (Type, trace)
import Relude.Extra

import Vega.Error (TypeError (..), TypeErrorSet (MkTypeErrorSet))
import Vega.Util (compose, mapAccumLM, unzip3Seq, viaList, zipWithSeqM)

import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Data.Unique (newUnique)
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError, throwError_)
import Effectful.Writer.Static.Local (runWriter, tell)
import Vega.Debug (showHeadConstructor)
import Vega.Effect.Output.Static.Local (Output, output, runOutputSeq)
import Vega.Effect.Trace (Category (..), Trace, trace, withTrace)
import Vega.Loc (HasLoc (getLoc), Loc)
import Vega.Pretty (emphasis, errorText, keyword, pretty, (<+>))
import Vega.Util (assert)
import Vega.Util qualified as Util

data Env = MkEnv
    { localTypes :: HashMap LocalName Type
    , localTypeVariables :: HashMap LocalName (Type, Kind, Monomorphization)
    , localTypeConstructors :: HashMap LocalName Kind
    }

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

-- TODO: factor out the reference/unique bits so you don't need full IOE
type TypeCheck es = (GraphPersistence :> es, Output TypeError :> es, Error TypeError :> es, Trace :> es, IOE :> es)

checkDeclaration :: (GraphPersistence :> es, Trace :> es, IOE :> es) => Declaration Renamed -> Eff es (Either TypeErrorSet (Declaration Typed))
checkDeclaration (MkDeclaration{loc, name, syntax}) = withTrace TypeCheck ("Declaration: " <> pretty name) do
    (syntaxOrFatalError, nonFatalErrors) <-
        runOutputSeq $
            runErrorNoCallStack $
                checkDeclarationSyntax loc syntax

    case syntaxOrFatalError of
        Left fatalError -> pure (Left (MkTypeErrorSet (nonFatalErrors <> [fatalError])))
        Right syntax ->
            case nonFatalErrors of
                [] -> pure (Right (MkDeclaration{loc, name, syntax}))
                errors -> pure (Left (MkTypeErrorSet errors))

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
            (kind, _synax) <- checkType emptyEnv Kind syntax
            GraphPersistence.cacheGlobalKind name kind
            pure kind

checkDeclarationSyntax :: (TypeCheck es) => Loc -> DeclarationSyntax Renamed -> Eff es (DeclarationSyntax Typed)
checkDeclarationSyntax loc = \case
    DefineFunction{name, typeSignature, declaredTypeParameters, parameters, body} -> do
        let env = emptyEnv
        (functionType, typeSignature) <- checkType env (Type BoxedRep) typeSignature

        (envTransformer, remainingType) <- bindTypeParameters loc env declaredTypeParameters functionType
        env <- pure (envTransformer env)

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

inferPattern :: (TypeCheck es) => Pattern Renamed -> Eff es (Pattern Typed, Type, Env -> Env)
inferPattern = \case
    VarPattern loc varName -> do
        type_ <- MetaVar <$> freshTypeMeta (varName.name) Parametric
        pure (VarPattern loc varName, type_, bindVarType varName type_)
    AsPattern loc innerPattern name -> do
        (innerPattern, innerType, innerTrans) <- inferPattern innerPattern
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
            (envTrans, typeWithoutBoundParameters) <- bindTypeParameters loc env typeParameters expectedType
            env <- pure (envTrans env)

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
            undefined
        PartialApplication{} -> undefined
        BinaryOperator{} -> undefined
        Match{} -> undefined

bindTypeParameters :: (TypeCheck es) => Loc -> Env -> Seq (Loc, LocalName) -> Type -> Eff es (Env -> Env, Type)
bindTypeParameters loc env parameters type_ = do
    (type_, boundVariables) <-
        instantiateWith
            SkolemizeInferred
            SkolemizeRemaining
            ( \binder argument -> [(argument, binder.kind, binder.monomorphization)]
            )
            loc
            env
            []
            type_

    -- If length boundVariables > length parameters, we deliberately ignore
    -- the remaining variables since the programmer didn't bind them here
    let envTransformers =
            Seq.zipWith
                (\(_, name) (argument, kind, monomorphization) -> bindTypeVariable name argument kind monomorphization)
                parameters
                boundVariables
    pure (Util.compose envTransformers, type_)

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
        VisibleTypeApplication{loc, varName, typeArguments} -> do
            type_ <- varType env varName

            -- TODO: we're currently inferring the arguments first and then calling into instantiate.
            -- It probably makes more sense to check the arguments directly against their kinds
            -- but if we want to do that, we need to duplicate the instantiateWith logic again.
            (_kinds, typeArguments, typeArgumentSyntax) <- unzip3Seq <$> for typeArguments (inferType env)
            (type_, ()) <- instantiateWith InstantiateInferredToMeta InstantiateRemainingToMeta (\_ _ -> ()) loc env typeArguments type_
            pure (type_, VisibleTypeApplication{loc, varName, typeArguments = typeArgumentSyntax}, Pure)
        Lambda loc typeParameters parameters body -> do
            case typeParameters of
                [] -> pure ()
                _ -> undefined -- error? I don't think we can handle type parameters in infer mode
            (parameters, parameterTypes, envTransformers) <- unzip3Seq <$> traverse inferPattern parameters

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

checkType :: (TypeCheck es) => Env -> Kind -> TypeSyntax Renamed -> Eff es (Type, TypeSyntax Typed)
checkType env expectedKind syntax = withTrace KindCheck ("checkType: " <> showHeadConstructor syntax <> keyword " <= " <> pretty expectedKind) do
    (kind, type_, syntax) <- inferType env syntax
    subsumes (getLoc syntax) env kind expectedKind
    pure (type_, syntax)

inferType :: (TypeCheck es) => Env -> TypeSyntax Renamed -> Eff es (Kind, Type, TypeSyntax Typed)
inferType env syntax = do
    (kind, type_, syntax) <- withTrace KindCheck ("inferType: " <> showHeadConstructor syntax) go
    trace KindCheck ("inferType: " <> showHeadConstructor syntax <+> keyword "<=" <+> pretty kind <+> keyword "~>" <+> pretty type_)
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
                        (arguments, argumentsSyntax) <- Seq.unzip <$> zipWithSeqM (checkType env) argumentKinds argumentsSyntax
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
                -- TODO: make this non-fatal
                kind -> fatalTypeError (ApplicationOfNonFunctionKind{loc, kind})
        TypeVarS loc localName -> do
            let (actualType, kind, _mono) = lookupTypeVariable localName env
            pure (kind, actualType, TypeVarS loc localName)
        ForallS loc typeVarBinders body -> do
            (env, typeVarBindersAndSyntax) <- mapAccumLM applyForallBinder env typeVarBinders
            let (typeVarBinders, typeVarBinderSyntax) = Seq.unzip typeVarBindersAndSyntax

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
            (effect, effectSyntax) <- checkType env Effect effect
            (_resultRep, resultType, resultTypeSyntax) <- inferTypeRep env result
            pure (Type BoxedRep, Function parameterTypes effect resultType, FunctionS loc parameterTypeSyntax effectSyntax resultTypeSyntax)
        TupleS loc elements -> do
            (elementReps, elementTypes, elementTypeSyntax) <- unzip3Seq <$> traverse (inferType env) elements
            pure (Type (ProductRep elementReps), Tuple elementTypes, TupleS loc elementTypeSyntax)
        RepS loc -> pure (Kind, Rep, RepS loc)
        TypeS loc repSyntax -> do
            (rep, repSyntax) <- checkType env Rep repSyntax
            pure (Kind, Type rep, TypeS loc repSyntax)
        EffectS loc -> pure (Kind, Effect, EffectS loc)
        SumRepS loc elementSyntax -> do
            (elements, elementSyntax) <- Seq.unzip <$> traverse (checkType env Rep) elementSyntax
            pure (Rep, SumRep elements, SumRepS loc elementSyntax)
        ProductRepS loc elementSyntax -> do
            (elements, elementSyntax) <- Seq.unzip <$> traverse (checkType env Rep) elementSyntax
            pure (Rep, ProductRep elements, ProductRepS loc elementSyntax)
        UnitRepS loc -> pure (Rep, UnitRep, UnitRepS loc)
        EmptyRepS loc -> pure (Rep, EmptyRep, EmptyRepS loc)
        BoxedRepS loc -> pure (Rep, BoxedRep, BoxedRepS loc)
        KindS loc -> pure (Kind, Kind, KindS loc)

inferTypeRep :: (TypeCheck es) => Env -> TypeSyntax Renamed -> Eff es (Kind, Type, TypeSyntax Typed)
inferTypeRep env type_ = do
    rep <- MetaVar <$> freshMeta "r" Monomorphized Rep
    (type_, typeSyntax) <- checkType env (Type rep) type_
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
        (kind, kindSyntax) <- checkType env Kind kindSyntax
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
            parameters <- fromList . map MetaVar <$> replicateM parameterCount (freshTypeMeta "a" Parametric)
            effect <- MetaVar <$> freshTypeMeta "e" Parametric
            result <- MetaVar <$> freshTypeMeta "b" Parametric
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

data OnInferred
    = -- | Instantiate inferred parameters to fresh meta variables
      InstantiateInferredToMeta
    | -- | Turn inferred parameters into fresh skolems
      SkolemizeInferred
    | -- | Instantiate inferred parameters with the given arguments
      -- as if they were visible
      ApplyInferred

data OnRemaining
    = -- | Instantiate remaining parameters (visible or inferred) to fresh meta variables
      InstantiateRemainingToMeta
    | -- | Turn remaining parameters (visible or inferred) into fresh skolems
      SkolemizeRemaining
    | -- | Leave any remaining type parameters after the last one that was applied as they are
      IgnoreRemaining

{- | Fill in the type parameters of a polytype with the given argument types.

The 'OnInferred' argument specifies what to do with inferred type parameters leading up to the
last applied parameter.

The 'OnRemaining' argument specifies what to do with remaining type parameters after all 'arguments' have been applied.

The third argument can be used to get a side output from bound type parameters. In particular, with m ~ Endo Env this can
be used to build up an environment transformer that binds type variables
-}
instantiateWith ::
    (TypeCheck es, Monoid m) =>
    OnInferred ->
    OnRemaining ->
    (ForallBinder -> Type -> m) ->
    Loc ->
    Env ->
    Seq Type ->
    Type ->
    Eff es (Type, m)
instantiateWith onInferred onRemaining makeOutput loc env arguments type_ = runWriter case normalizeForalls type_ of
    Forall binders body -> do
        -- We take the kind as a second parameter here since we need to apply the substitution to it
        -- and we don't want to duplicate that work if we have already done so before calling this.
        --
        -- Notably, this function does *NOT* apply the substitution itself, so make sure you apply it yourself
        -- before calling this
        let applyArgument binder@MkForallBinder{varName, monomorphization, visibility = _} kind argument substitution = do
                checkEvaluatedType loc env kind argument
                assertMonomorphizability loc env argument monomorphization

                tell (makeOutput binder{kind} argument)
                pure (insert varName argument substitution)

        let go substitution Empty Empty = substituteTypeVariables substitution body
            go substitution Empty _ = undefined
            go substitution (binder@MkForallBinder{varName, kind, monomorphization, visibility = _} :<| binders) Empty = case onRemaining of
                InstantiateRemainingToMeta -> do
                    kind <- substituteTypeVariables substitution kind
                    meta <- freshMeta varName.name monomorphization kind
                    substitution <- applyArgument binder kind (MetaVar meta) substitution
                    go substitution binders Empty
                SkolemizeRemaining -> do
                    kind <- substituteTypeVariables substitution kind
                    skolem <- freshSkolem varName monomorphization kind
                    substitution <- applyArgument binder kind (Skolem skolem) substitution
                    go substitution binders Empty
                IgnoreRemaining -> substituteTypeVariables substitution (Forall (binder :<| binders) body)
            go substitution (binder@MkForallBinder{visibility = Visible, kind} :<| binders) (argument :<| arguments) = do
                kind <- substituteTypeVariables substitution kind
                substitution <- applyArgument binder kind argument substitution
                go substitution binders arguments
            go substitution (binder@MkForallBinder{visibility = Inferred, varName, kind, monomorphization} :<| binders) (argument :<| arguments) = case onInferred of
                ApplyInferred -> do
                    kind <- substituteTypeVariables substitution kind
                    substitution <- applyArgument binder kind argument substitution
                    go substitution binders arguments
                InstantiateInferredToMeta -> do
                    kind <- substituteTypeVariables substitution kind
                    meta <- freshMeta varName.name monomorphization kind
                    substitution <- applyArgument binder kind (MetaVar meta) substitution
                    go substitution binders arguments
                SkolemizeInferred -> do
                    kind <- substituteTypeVariables substitution kind
                    skolem <- freshSkolem varName monomorphization kind
                    substitution <- applyArgument binder kind (Skolem skolem) substitution
                    go substitution binders arguments
        go mempty binders arguments
    _ -> case arguments of
        Empty -> pure type_
        _ -> undefined

instantiate :: (TypeCheck es) => Loc -> Env -> Type -> Eff es Type
instantiate loc env type_ = fst <$> instantiateWith InstantiateInferredToMeta InstantiateRemainingToMeta (\_ _ _ -> ()) loc env [] type_

skolemize :: (TypeCheck es) => Loc -> Env -> Type -> Eff es Type
skolemize loc env type_ = fst <$> instantiateWith SkolemizeInferred SkolemizeRemaining (\_ _ _ -> ()) loc env [] type_

{- | Collect repeated foralls into a single one.
For example, this will turn `forall a b. forall c d. Int` into `forall a b c d. Int`

This is a very cheap operation (O(#foralls))
-}
normalizeForalls :: Type -> Type
normalizeForalls = go []
  where
    go totalBinders (Forall binders body) = go (totalBinders <> binders) body
    go totalBinders type_ = Forall totalBinders type_

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
                | otherwise ->
                    case (meta.monomorphization, foundMeta.monomorphization) of
                        (Monomorphized, Parametric) -> do
                            -- This is a parametric meta variable but it's really supposed to be monomorphized, so
                            -- we "strengthen" it by binding it to a monomorphized unification variable

                            -- TODO: we only ever really call this when binding our monomorphized meta variable
                            -- to the result so we could really just swap the order of the meta variables and
                            -- avoid the extra meta variable and unification
                            newMeta <- freshMeta foundMeta.name Monomorphized foundMeta.kind
                            bindMeta loc env foundMeta (MetaVar newMeta)
                        _ -> pure ()
            Skolem skolem -> case (meta.monomorphization, skolem.monomorphization) of
                (Monomorphized, Parametric) -> do
                    typeError ParametricVariableInMono{loc, varName = skolem.originalName, fullType = Just type_}
                _ -> pure ()
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
subsumesEffect Pure _ = pure ()
subsumesEffect _ _ = undefined

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

freshMeta :: (TypeCheck es) => Text -> Monomorphization -> Kind -> Eff es MetaVar
freshMeta name monomorphization kind = do
    identity <- liftIO newUnique
    underlying <- newIORef Nothing
    pure $ MkMetaVar{underlying, identity, name, monomorphization, kind}

-- | Creates a fresh meta variable of kind (Type ?r) where ?r is another fresh meta variable
freshTypeMeta :: (TypeCheck es) => Text -> Monomorphization -> Eff es MetaVar
freshTypeMeta name monomorphization = do
    rep <- MetaVar <$> freshMeta "r" Monomorphized Rep
    freshMeta name monomorphization (Type rep)

freshSkolem :: (TypeCheck es) => LocalName -> Monomorphization -> Kind -> Eff es Skolem
freshSkolem originalName monomorphization kind = do
    identity <- liftIO newUnique
    pure $ MkSkolem{identity, originalName, monomorphization, kind}

followMetas :: (TypeCheck es) => Type -> Eff es Type
followMetas = \case
    type_@(MetaVar meta) -> do
        readIORef meta.underlying >>= \case
            Nothing -> pure type_
            Just substitution -> do
                actualType <- followMetas substitution
                -- path compression
                writeIORef meta.underlying (Just actualType)

                pure actualType
    type_ -> pure type_

assertMonomorphizability :: (TypeCheck es) => Loc -> Env -> Type -> Monomorphization -> Eff es ()
assertMonomorphizability loc env type_ = \case
    Monomorphized -> monomorphized loc env type_
    Parametric -> pure ()

monomorphized :: (TypeCheck es) => Loc -> Env -> Type -> Eff es ()
monomorphized loc env type_ = do
    trace TypeCheck $ emphasis "mono" <+> pretty type_
    go type_
  where
    go = \case
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
        MetaVar{} -> do
            undefined
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
