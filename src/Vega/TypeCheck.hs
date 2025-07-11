module Vega.TypeCheck (checkDeclaration) where

import Vega.Syntax

import Effectful hiding (Effect)
import Relude hiding (Type, trace)
import Relude.Extra

import Vega.Error (TypeError (..), TypeErrorSet (MkTypeErrorSet))
import Vega.Util (compose, mapAccumLM, unzip3Seq, viaList, zipWithSeqM)

import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence

import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Data.Unique (newUnique)
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError, throwError_)
import Vega.Debug (showHeadConstructor)
import Vega.Effect.Output.Static.Local (Output, output, runOutputSeq)
import Vega.Effect.Trace (Category (..), Trace, trace, withTrace)
import Vega.Loc (HasLoc (getLoc), Loc)
import Vega.Pretty (errorText, keyword, pretty, (<+>))

data Env = MkEnv
    { localTypes :: HashMap LocalName Type
    , localTypeVariables :: HashMap LocalName Kind
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

bindTypeVariable :: LocalName -> Kind -> Env -> Env
bindTypeVariable name type_ env@MkEnv{localTypeVariables} = env{localTypeVariables = insert name type_ localTypeVariables}

typeVariableKind :: (HasCallStack) => LocalName -> Env -> Kind
typeVariableKind name env =
    case lookup name env.localTypeVariables of
        Nothing -> error $ "type variable not found in type checker: " <> show name
        Just kind -> kind

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
            (type_, _) <- checkType emptyEnv Type syntax
            GraphPersistence.cacheGlobalType name type_
            pure type_

globalConstructorKind :: (TypeCheck es) => GlobalName -> Eff es Kind
globalConstructorKind name = do
    GraphPersistence.getGlobalKind name >>= \case
        Left cachedKind -> pure cachedKind
        Right syntax -> do
            (kind, _synax) <- evalKind syntax
            GraphPersistence.cacheGlobalKind name kind
            pure kind

checkDeclarationSyntax :: (TypeCheck es) => Loc -> DeclarationSyntax Renamed -> Eff es (DeclarationSyntax Typed)
checkDeclarationSyntax loc = \case
    DefineFunction{name, typeSignature, declaredTypeParameters, parameters, body} -> do
        let env = emptyEnv
        (functionType, typeSignature) <- checkType env Type typeSignature

        (parameterTypes, effect, returnType, env, declaredTypeParameters) <- case declaredTypeParameters of
            Nothing -> do
                -- TODO: i don't think this works correctly with foralls?
                functionType <- skolemize functionType
                (parameterTypes, effect, returnType) <- splitFunctionType loc (length parameters) functionType
                pure (parameterTypes, effect, returnType, env, Nothing)
            Just typeParameters -> do
                undefined

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
        let env = compose transformers emptyEnv

        (body, bodyEffect) <- check env returnType body
        subsumesEffect bodyEffect effect

        pure DefineFunction{name, typeSignature, declaredTypeParameters, parameters, body}
    DefineVariantType{name, typeParameters, constructors} -> do
        let env = emptyEnv
        (env, binders) <- mapAccumLM applyTypeVarBinder env typeParameters
        let typeParameters = fmap (\(_, _, binder) -> binder) binders

        constructors <- for constructors \(name, loc, parameters) -> do
            (_, parameters) <- Seq.unzip <$> traverse (checkType env Type) parameters
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
        (innerType, innerTypeSyntax) <- checkType env Type innerTypeSyntax
        (innerPattern, innerTrans) <- checkPattern env innerType innerPattern
        subsumes loc innerType expectedType
        pure (TypePattern loc innerPattern innerTypeSyntax, innerTrans)
    OrPattern{} -> undefined
    _ -> undefined

inferPattern :: (TypeCheck es) => Pattern Renamed -> Eff es (Pattern Typed, Type, Env -> Env)
inferPattern = \case
    VarPattern loc varName -> do
        meta <- freshMeta (varName.name)
        let type_ = MetaVar meta
        pure (VarPattern loc varName, type_, bindVarType varName type_)
    AsPattern loc innerPattern name -> do
        (innerPattern, innerType, innerTrans) <- inferPattern innerPattern
        pure (AsPattern loc innerPattern name, innerType, bindVarType name innerType . innerTrans)
    _ -> undefined

check :: (TypeCheck es) => Env -> Type -> Expr Renamed -> Eff es (Expr Typed, Effect)
check env expectedType expr = withTrace TypeCheck ("check:" <+> showHeadConstructor expr <+> keyword "<=" <+> pretty expectedType) do
    let deferToInference = do
            (actualType, expr, effect) <- infer env expr
            subsumes (getLoc expr) actualType expectedType
            pure (expr, effect)
    case expr of
        Var{} -> deferToInference
        DataConstructor{} -> undefined
        Application{} -> deferToInference
        VisibleTypeApplication{} -> undefined
        Lambda loc parameters body -> do
            (parameterTypes, expectedEffect, returnType) <- splitFunctionType loc (length parameters) expectedType
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
            pure (Lambda loc parameters body, Pure)
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

infer :: (TypeCheck es) => Env -> Expr Renamed -> Eff es (Type, Expr Typed, Effect)
infer env expr = do
    (type_, expr, effect) <- withTrace TypeCheck ("infer " <> showHeadConstructor expr) go
    trace TypeCheck ("infer" <> showHeadConstructor expr <> keyword " => " <> pretty type_ <> keyword " | " <> pretty effect)
    pure (type_, expr, effect)
  where
    go = case expr of
        Var loc name -> case name of
            Global globalName -> do
                type_ <- instantiate =<< getGlobalType globalName
                pure (type_, Var loc name, Pure)
            Local localName -> do
                case lookup localName env.localTypes of
                    Just type_ -> do
                        type_ <- instantiate type_
                        pure (type_, Var loc name, Pure)
                    Nothing -> error ("variable not found in renamer: " <> show name)
        Application{loc, functionExpr, arguments} -> do
            (functionType, functionExpr, functionExprEffect) <- infer env functionExpr
            (argumentTypes, functionEffect, returnType) <- splitFunctionType loc (length arguments) functionType
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
        VisibleTypeApplication{} ->
            undefined
        Lambda loc parameters body -> do
            (parameters, parameterTypes, envTransformers) <- unzip3Seq <$> traverse inferPattern parameters

            (bodyType, body, bodyEffect) <- infer (compose envTransformers env) body

            pure (Function parameterTypes bodyEffect bodyType, Lambda loc parameters body, Pure)
        StringLiteral loc literal -> pure (stringType, StringLiteral loc literal, Pure)
        IntLiteral loc literal -> pure (intType, IntLiteral loc literal, Pure)
        DoubleLiteral loc literal -> pure (doubleType, DoubleLiteral loc literal, Pure)
        BinaryOperator{} -> undefined
        If{loc, condition, thenBranch, elseBranch} -> do
            (condition, conditionEffect) <- check env boolType condition
            (thenType, thenBranch, thenEffect) <- infer env thenBranch
            (elseType, elseBranch, elseEffect) <- infer env elseBranch
            subsumes loc thenType elseType
            subsumes loc elseType thenType
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

evalKind :: (TypeCheck es) => KindSyntax Renamed -> Eff es (Kind, KindSyntax Typed)
evalKind = \case
    TypeS loc -> pure (Type, TypeS loc)
    EffectS loc -> pure (Effect, EffectS loc)
    ArrowKindS loc argumentKindsSyntax resultKindSyntax -> do
        (argumentKinds, argumentKindsSyntax) <- Seq.unzip <$> traverse evalKind argumentKindsSyntax
        (resultKind, resultKindSyntax) <- evalKind resultKindSyntax
        pure (ArrowKind argumentKinds resultKind, ArrowKindS loc argumentKindsSyntax resultKindSyntax)

checkType :: (TypeCheck es) => Env -> Kind -> TypeSyntax Renamed -> Eff es (Type, TypeSyntax Typed)
checkType env expectedKind syntax = withTrace KindCheck ("checkType: " <> showHeadConstructor syntax <> keyword " <= " <> pretty expectedKind) do
    (kind, type_, syntax) <- inferType env syntax
    unifyKind (getLoc syntax) expectedKind kind
    pure (type_, syntax)

inferType :: (TypeCheck es) => Env -> TypeSyntax Renamed -> Eff es (Kind, Type, TypeSyntax Typed)
inferType env syntax = do
    (kind, type_, syntax) <- withTrace KindCheck ("inferType: " <> showHeadConstructor syntax) go
    trace KindCheck ("inferType: " <> showHeadConstructor syntax <+> keyword "<=" <+> pretty kind <+> keyword "~>" <+> pretty type_)
    pure (kind, type_, syntax)
  where
    go = case syntax of
        TypeConstructorS loc name -> do
            kind <- case name of
                Global name -> globalConstructorKind name
                Local name -> case lookup name env.localTypeConstructors of
                    Nothing -> error $ "local type constructor " <> show name <> " not found in type checker"
                    Just kind -> pure kind
            pure (kind, TypeConstructor name, TypeConstructorS loc name)
        TypeApplicationS loc typeConstructorSyntax argumentsSyntax -> do
            (constructorKind, typeConstructor, typeConstructorSyntax) <- inferType env typeConstructorSyntax
            case constructorKind of
                ArrowKind argumentKinds resultKind
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
            let kind = typeVariableKind localName env
            pure (kind, TypeVar localName, TypeVarS loc localName)
        ForallS loc typeVarBinders body -> do
            (env, typeVarBinders) <- mapAccumLM applyTypeVarBinder env typeVarBinders

            (body, bodySyntax) <- checkType env Type body

            pure
                ( Type
                , Forall (fmap (\(name, kind, _) -> (name, kind)) typeVarBinders) body
                , ForallS loc (fmap (\(_, _, binder) -> binder) typeVarBinders) bodySyntax
                )
        PureFunctionS loc parameters result -> do
            (parameterTypes, parameterTypeSyntax) <- Seq.unzip <$> traverse (checkType env Type) parameters
            (resultType, resultTypeSyntax) <- checkType env Type result
            pure (Type, Function parameterTypes Pure resultType, PureFunctionS loc parameterTypeSyntax resultTypeSyntax)
        FunctionS loc parameters effect result -> do
            (parameterTypes, parameterTypeSyntax) <- Seq.unzip <$> traverse (checkType env Type) parameters
            (effect, effectSyntax) <- checkType env Effect effect
            (resultType, resultTypeSyntax) <- checkType env Type result
            pure (Type, Function parameterTypes effect resultType, FunctionS loc parameterTypeSyntax effectSyntax resultTypeSyntax)
        TupleS loc elements -> do
            (elementTypes, elementTypeSyntax) <- Seq.unzip <$> traverse (checkType env Type) elements
            pure (Type, Tuple elementTypes, TupleS loc elementTypeSyntax)

applyTypeVarBinder :: (TypeCheck es) => Env -> ForallBinderS Renamed -> Eff es (Env, (LocalName, Kind, ForallBinderS Typed))
applyTypeVarBinder env = \case
    UnspecifiedBinderS{loc, varName} -> undefined
    TypeVarBinderS{loc, varName, kind = kindSyntax} -> do
        (kind, kindSyntax) <- evalKind kindSyntax
        pure (bindTypeVariable varName kind env, (varName, kind, TypeVarBinderS{loc, varName, kind = kindSyntax}))
    KindVarBinderS{} -> undefined

splitFunctionType :: (TypeCheck es) => Loc -> Int -> Type -> Eff es (Seq Type, Effect, Type)
splitFunctionType loc parameterCount type_ = do
    followMetas type_ >>= \case
        Function parameters effect result
            | length parameters == parameterCount -> pure (parameters, effect, result)
            | otherwise -> undefined
        type_ -> do
            parameters <- fromList . map MetaVar <$> replicateM parameterCount (freshMeta "a")
            effect <- MetaVar <$> freshMeta "e"
            result <- MetaVar <$> freshMeta "a"
            subsumes loc type_ (Function parameters effect result)
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
            -- The variable binders can't contain further types (only kinds) and local names are unique
            -- so we don't need to worry about capture avoiding substitution or anything like that here
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

instantiateWith :: (TypeCheck es) => (Seq Type) -> Type -> Eff es Type
instantiateWith arguments = \case
    Forall params body
        | length params == length arguments -> do
            substituteTypeVariables (viaList (Seq.zipWith (\(param, _kind) argument -> (param, argument)) params arguments)) body
        | otherwise -> undefined
    _ -> undefined

instantiate :: (TypeCheck es) => Type -> Eff es Type
instantiate type_ = case collectAllPrenexBinders type_ of
    ([], _) -> pure type_
    (binders, _) -> do
        metas <- for binders \(name, _kind) -> do
            MetaVar <$> freshMeta name.name
        instantiateWith metas type_

skolemize :: (TypeCheck es) => Type -> Eff es Type
skolemize type_ = case collectAllPrenexBinders type_ of
    ([], _) -> pure type_
    (binders, _) -> do
        skolems <- for binders \(name, _kind) -> do
            Skolem <$> freshSkolem name
        instantiateWith skolems type_

collectAllPrenexBinders :: Type -> (Seq (LocalName, Kind), Type)
collectAllPrenexBinders = \case
    Forall binders body -> do
        let (rest, monoBody) = collectAllPrenexBinders body
        (binders <> rest, monoBody)
    type_ -> ([], type_)

subsumes :: (TypeCheck es) => Loc -> Type -> Type -> Eff es ()
subsumes loc subtype supertype = do
    subtype <- instantiate subtype
    supertype <- skolemize supertype
    unify loc subtype supertype

unify :: (TypeCheck es) => Loc -> Type -> Type -> Eff es ()
unify loc type1 type2 = withTrace Unify (pretty type1 <+> keyword "~" <+> pretty type2) do
    let unificationFailure = typeError (UnableToUnify{loc, expectedType = type2, actualType = type1})
    type1 <- followMetas type1
    type2 <- followMetas type2
    case (type1, type2) of
        (MetaVar meta1, _) -> bindMeta meta1 type2
        (_, MetaVar meta2) -> bindMeta meta2 type1
        _ ->
            case type1 of
                TypeConstructor name1 -> case type2 of
                    TypeConstructor name2
                        | name1 == name2 -> pure ()
                    _ -> unificationFailure
                TypeApplication typeConstructor1 arguments1 -> case type2 of
                    TypeApplication typeConstructor2 arguments2
                        | length arguments1 == length arguments2 -> do
                            unify loc typeConstructor1 typeConstructor2
                            _ <- zipWithSeqM (unify loc) arguments1 arguments2
                            pure ()
                    _ -> unificationFailure
                TypeVar name -> error $ "unsubstituted type variable in unification: " <> show name
                Forall binders1 body1 -> undefined
                Function parameters1 effect1 result1 -> case type2 of
                    Function parameters2 effect2 result2
                        | length parameters1 == length parameters2 -> do
                            _ <- zipWithSeqM (unify loc) parameters1 parameters2
                            unify loc effect1 effect2
                            unify loc result1 result2
                    _ -> unificationFailure
                Tuple elements1 -> case type2 of
                    Tuple elements2
                        | length elements1 == length elements2 -> do
                            _ <- zipWithSeqM (unify loc) elements1 elements2
                            pure ()
                    _ -> unificationFailure
                Skolem skolem1 -> case type2 of
                    Skolem skolem2
                        | skolem1 == skolem2 -> pure ()
                    _ -> unificationFailure
                Pure -> case type2 of
                    Pure -> pure ()
                    _ -> unificationFailure

bindMeta :: (TypeCheck es) => MetaVar -> Type -> Eff es ()
bindMeta meta boundType =
    followMetas (MetaVar meta) >>= \case
        MetaVar meta -> do
            followMetas boundType >>= \case
                MetaVar meta2
                    -- ?a ~ ?a constraints are technically harmless but cause problems for the type checker
                    -- so we need to handle them separately
                    | meta == meta2 -> pure ()
                boundType ->
                    occursAndAdjust meta boundType >>= \case
                        True -> undefined
                        False -> writeIORef meta.underlying (Just boundType)
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

freshMeta :: (TypeCheck es) => Text -> Eff es MetaVar
freshMeta name = do
    identity <- liftIO newUnique
    underlying <- newIORef Nothing
    pure $ MkMetaVar{underlying, identity, name}

freshSkolem :: (TypeCheck es) => LocalName -> Eff es Skolem
freshSkolem originalName = do
    identity <- liftIO newUnique
    pure $ MkSkolem{identity, originalName}

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

unifyKind :: (TypeCheck es) => Loc -> Kind -> Kind -> Eff es ()
unifyKind loc expected actual = do
    let kindMismatch = do
            typeError (KindMismatch{loc, expectedKind = expected, actualKind = actual})
    case expected of
        Type -> case actual of
            Type -> pure ()
            _ -> kindMismatch
        Effect -> case actual of
            Effect -> pure ()
            _ -> kindMismatch
        ArrowKind parameters1 result1 -> case actual of
            ArrowKind parameters2 result2
                | length parameters1 == length parameters2 -> do
                    _ <- zipWithSeqM (unifyKind loc) parameters1 parameters2
                    unifyKind loc result1 result2
            _ -> kindMismatch
