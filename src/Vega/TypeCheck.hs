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
import Vega.Pretty (emphasis, errorText, keyword, pretty, (<+>))
import Vega.Util qualified as Util
import qualified Data.HashMap.Strict as HashMap

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

        (envTransformer, remainingType) <- bindTypeParameters declaredTypeParameters functionType
        env <- pure (envTransformer env)

        -- We bound the declared type parameters above and the rest are not accessible in the body
        -- so we can just skolemize them away here
        remainingType <- skolemize remainingType
        (parameterTypes, effect, returnType) <- splitFunctionType loc (length parameters) remainingType

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
        let typeParameters = fmap (\(_, _, binder) -> binder) binders

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
        subsumes loc innerType expectedType
        pure (TypePattern loc innerPattern innerTypeSyntax, innerTrans)
    OrPattern{} -> undefined
    _ -> undefined

inferPattern :: (TypeCheck es) => Pattern Renamed -> Eff es (Pattern Typed, Type, Env -> Env)
inferPattern = \case
    VarPattern loc varName -> do
        meta <- freshMeta (varName.name) Parametric
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
        -- TODO: not entirely sure if this is correct or if we should try to stay in check mode
        VisibleTypeApplication{} -> deferToInference
        Lambda loc typeParameters parameters body -> do
            (envTrans, typeWithoutBoundParameters) <- bindTypeParameters typeParameters expectedType
            env <- pure (envTrans env)

            -- Any type variables *not* bound above are not going to be available in the body
            -- and so are just skolemized away here
            resultingType <- skolemize typeWithoutBoundParameters
            (parameterTypes, expectedEffect, returnType) <- splitFunctionType loc (length parameters) resultingType
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

bindTypeParameters :: (TypeCheck es) => Seq (Loc, LocalName) -> Type -> Eff es (Env -> Env, Type)
bindTypeParameters parameters type_ = do
    (remainingType, transformers) <- mapAccumLM (\type_ (loc, parameter) -> swap <$> bindTypeParameter loc parameter type_) type_ parameters
    pure (Util.compose transformers, remainingType)

bindTypeParameter :: (TypeCheck es) => Loc -> LocalName -> Type -> Eff es (Env -> Env, Type)
bindTypeParameter loc parameter = \case
    type_@(Forall ((_name, kind, monomorphization) :<| _) _) -> do
        trace TypeCheck $ "binding type parameter" <+> prettyLocal VarKind parameter
        skolem <- Skolem <$> freshSkolem parameter monomorphization
        -- It would be nice to avoid calling instantiateWith over and over again,
        -- but we can't just defer all the variables until the end since binders
        -- might depend on previous binders
        remainingType <- instantiateWith [skolem] type_
        pure (bindTypeVariable parameter skolem kind monomorphization, remainingType)
    type_ -> do
        -- TODO: try to make this non-fatal.
        -- This is a lot harder than it looks. If we just return (id, type_), we
        -- never bind the parameter so we will panic because the type variable is unbound,
        -- but we also can't bind the parameter to anything since we don't know its type or
        -- monomorphization
        fatalTypeError (TryingToBindTypeParameterOfMonotype{loc, parameter, type_})

varType :: HasCallStack => TypeCheck es => Env -> Name -> Eff es Type
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
            type_ <- instantiate =<< varType env name
            pure (type_, Var loc name, Pure)
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
        VisibleTypeApplication{loc, varName, typeArguments} -> do
            type_ <- varType env varName  
            case normalizeForalls type_ of
                Forall binders _body
                    | length binders >= length typeArguments -> do
                        (arguments, argumentSyntax) <-
                            Seq.unzip <$> for (Seq.zip typeArguments binders) \(argumentSyntax, (_varName, expectedKind, monomorphization)) -> do
                                (argumentType, argumentSyntax) <- checkType env expectedKind argumentSyntax
                                case monomorphization of
                                    Parametric -> pure ()
                                    Monomorphized -> monomorphized loc env argumentType
                                pure (argumentType, argumentSyntax)
                        resultingType <- instantiate =<< instantiateWith arguments type_
                        pure (resultingType, VisibleTypeApplication{loc, varName, typeArguments = argumentSyntax}, Pure)
                    | otherwise -> do
                        -- TODO: try to make this non-fatal. That's going to be quite difficult though, since
                        -- returning anything else is going to cause a ton of false-positives
                        fatalTypeError (TypeApplicationWithTooFewParameters{loc, typeArgumentCount = length typeArguments, instantiatedType = type_, parameterCount = length binders})
                _ -> do
                    fatalTypeError (TypeApplicationToMonoType{loc, instantiatedType = type_, typeArgumentCount = length typeArguments})
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

checkType :: (TypeCheck es) => Env -> Kind -> TypeSyntax Renamed -> Eff es (Type, TypeSyntax Typed)
checkType env expectedKind syntax = withTrace KindCheck ("checkType: " <> showHeadConstructor syntax <> keyword " <= " <> pretty expectedKind) do
    (kind, type_, syntax) <- inferType env syntax
    subsumes (getLoc syntax) kind expectedKind
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
            (env, typeVarBinders) <- mapAccumLM applyForallBinder env typeVarBinders

            (typeRep, body, bodySyntax) <- inferTypeRep env body

            pure
                -- TODO: uhhhh i don't think this is correct?
                -- we will need to introduce kind level foralls here... sometimes??
                ( Type typeRep
                , -- TODO: this doesn't work with unspecified binders (we need to desugar the binders manually in that case)
                  Forall (fmap (\(name, kind, binder) -> (name, kind, binder.monomorphization)) typeVarBinders) body
                , ForallS loc (fmap (\(_, _, binder) -> binder) typeVarBinders) bodySyntax
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
    rep <- MetaVar <$> freshMeta "r" Parametric
    (type_, typeSyntax) <- checkType env (Type rep) type_
    pure (rep, type_, typeSyntax)

applyForallBinder :: (TypeCheck es) => Env -> ForallBinderS Renamed -> Eff es (Env, (LocalName, Kind, ForallBinderS Typed))
applyForallBinder env = \case
    UnspecifiedBinderS{loc, varName} -> undefined
    TypeVarBinderS{loc, monomorphization, varName, kind = kindSyntax} -> do
        (kind, kindSyntax) <- checkType env Kind kindSyntax
        -- TODO: not entirely sure if this is the right place for this
        monomorphized loc env kind
        pure (bindTypeVariable varName (TypeVar varName) kind monomorphization env, (varName, kind, TypeVarBinderS{loc, monomorphization, varName, kind = kindSyntax}))

splitFunctionType :: (TypeCheck es) => Loc -> Int -> Type -> Eff es (Seq Type, Effect, Type)
splitFunctionType loc parameterCount type_ = do
    followMetas type_ >>= \case
        Function parameters effect result
            | length parameters == parameterCount -> pure (parameters, effect, result)
            | otherwise -> undefined
        type_ -> do
            parameters <- fromList . map MetaVar <$> replicateM parameterCount (freshMeta "a" Parametric)
            effect <- MetaVar <$> freshMeta "e" Parametric
            result <- MetaVar <$> freshMeta "b" Parametric
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

instantiateWith :: (TypeCheck es) => (Seq Type) -> Type -> Eff es Type
instantiateWith arguments type_ = case normalizeForalls type_ of
    Forall params body
        | length arguments <= length params -> do
            forall_ (Seq.drop (length arguments) params) <$> substituteTypeVariables (viaList (Seq.zipWith (\(param, _kind, _) argument -> (param, argument)) params arguments)) body
        | otherwise -> undefined
    _ -> undefined

{- | Collect repeated foralls into a single one.
This will turn e.g. `forall a b. forall c d. Int` into `forall a b c d. Int`

This is a very cheap operation (O(#foralls))
-}
normalizeForalls :: Type -> Type
normalizeForalls = go []
  where
    go totalBinders (Forall binders body) = go (totalBinders <> binders) body
    go totalBinders type_ = Forall totalBinders type_

instantiate :: (TypeCheck es) => Type -> Eff es Type
instantiate type_ = case collectAllPrenexBinders type_ of
    ([], _) -> pure type_
    (binders, _) -> do
        metas <- for binders \(name, _kind, monomorphization) -> do
            MetaVar <$> freshMeta name.name monomorphization
        instantiateWith metas type_

skolemize :: (TypeCheck es) => Type -> Eff es Type
skolemize type_ = case collectAllPrenexBinders type_ of
    ([], _) -> pure type_
    (binders, _) -> do
        skolems <- for binders \(name, _kind, monomorphization) -> do
            Skolem <$> freshSkolem name monomorphization
        instantiateWith skolems type_

collectAllPrenexBinders :: Type -> (Seq (LocalName, Kind, Monomorphization), Type)
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
        (MetaVar meta1, _) -> bindMeta loc meta1 type2
        (_, MetaVar meta2) -> bindMeta loc meta2 type1
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
                Rep -> case type2 of
                    Rep -> pure ()
                    _ -> unificationFailure
                Type rep1 -> case type2 of
                    Type rep2 -> unify loc rep1 rep2
                    _ -> unificationFailure
                Effect -> case type2 of
                    Effect -> pure ()
                    _ -> unificationFailure
                SumRep elements1 -> case type2 of
                    SumRep elements2
                        | length elements1 == length elements2 -> do
                            _ <- zipWithSeqM (unify loc) elements1 elements2
                            pure ()
                    _ -> unificationFailure
                ProductRep elements1 -> case type2 of
                    ProductRep elements2
                        | length elements1 == length elements2 -> do
                            _ <- zipWithSeqM (unify loc) elements1 elements2
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

bindMeta :: (TypeCheck es) => Loc -> MetaVar -> Type -> Eff es ()
bindMeta loc meta boundType =
    followMetas (MetaVar meta) >>= \case
        MetaVar meta -> do
            followMetas boundType >>= \case
                MetaVar meta2
                    -- ?a ~ ?a constraints are technically harmless but cause problems for the type checker
                    -- so we need to handle them separately
                    | meta == meta2 -> pure ()
                boundType ->
                    occursAndAdjust loc meta boundType >>= \case
                        True -> undefined
                        False -> writeIORef meta.underlying (Just boundType)
        _ -> error $ "Trying to bind unbound meta variable"

occursAndAdjust :: (TypeCheck es) => Loc -> MetaVar -> Type -> Eff es Bool
occursAndAdjust loc meta type_ = do
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
                            newMeta <- freshMeta foundMeta.name Monomorphized
                            bindMeta loc foundMeta (MetaVar newMeta)
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

freshMeta :: (TypeCheck es) => Text -> Monomorphization -> Eff es MetaVar
freshMeta name monomorphization = do
    identity <- liftIO newUnique
    underlying <- newIORef Nothing
    pure $ MkMetaVar{underlying, identity, name, monomorphization}

freshSkolem :: (TypeCheck es) => LocalName -> Monomorphization -> Eff es Skolem
freshSkolem originalName monomorphization = do
    identity <- liftIO newUnique
    pure $ MkSkolem{identity, originalName, monomorphization}

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
