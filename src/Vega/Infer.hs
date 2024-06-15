module Vega.Infer (typecheck, TypeError (..)) where

import Vega.Prelude
import Vega.Syntax

import Vega.Eval (
    CoreDeclaration,
    CoreExpr,
    Eval,
    EvalContext,
    HasContext (getContext),
    Value,
    define,
    defineSkolem,
    emptyEvalContext,
    eval,
    freshSkolem,
    runEval,
    skolemizeClosure,
    quote
 )
import Vega.Eval qualified as Eval
import Vega.Primop

import Vega.Debug
import Vega.LazyM
import Vega.Loc (HasLoc)
import Vega.Monad.Ref
import Vega.Pattern qualified as Pattern
import Vega.Pretty hiding (quote)
import Vega.Trace
import Vega.Util

import Data.Foldable (foldrM)
import Data.Sequence qualified as Seq
import Data.Vector qualified as Vector

import Control.Monad.Base (MonadBase (liftBase))
import Control.Monad.Fix
import Control.Monad.Writer.Strict (MonadWriter (tell), WriterT (runWriterT))
import Data.These (These (That, These, This))
import Vega.Difflist (Difflist)
import Vega.Monad.Unique (MonadUnique (..))
import Vega.Name (ident)
import Vega.Name qualified as Name

data TypeError
    = UnableToUnify Loc CoreExpr CoreExpr
    | OccursCheckViolation Loc MetaVar CoreExpr
    | Impredicative Loc Type Type
    | InvalidConstructorReturnType Loc Name Type
    deriving (Generic)
instance HasLoc TypeError

instance Pretty TypeError where
    pretty (UnableToUnify _ type1 type2) =
        "Unable to unify types "
            <> pretty type1
            <> "\n"
            <> "                  and "
            <> pretty type2
    pretty (OccursCheckViolation _ metavar type_) =
        "Unable to construct an infinite type satisfying\n    " <> pretty (StuckMeta metavar []) <> keyword " ~ " <> pretty type_
    pretty (Impredicative _ type1 type2) =
        "Impredicative instantiation attempted\n"
            <> "    "
            <> pretty type1
            <> keyword " ~ "
            <> pretty type2
    pretty (InvalidConstructorReturnType _ name type_) =
        "Data constructor"
            <+> ident name
            <+> "does not return its enclosing type.\n"
            <> "Invalid return type"
            <+> pretty type_

type Type = Value
type MetaVar = MetaVarF EvalContext

data Env = MkEnv
    { varTypes :: Map Name Type
    , dataConstructors :: Map Name Type
    , evalContext :: EvalContext
    }

instance HasContext Env where
    getContext env = env.evalContext

extendConstructor :: Name -> Type -> Env -> Env
extendConstructor name types env = env{dataConstructors = insert name types env.dataConstructors}

extendVariable :: Name -> Type -> LazyM Eval Value -> Env -> Env
extendVariable name type_ value env =
    env
        { varTypes = insert name type_ env.varTypes
        , evalContext = define name value env.evalContext
        }

data InferState = MkInferState {}

newtype Infer a = MkInfer (ReaderT (TraceAction IO) (ExceptT TypeError (WriterT (Difflist TypeError) (StateT InferState IO))) a)
    deriving newtype (Functor, Applicative, Monad, MonadFix, MonadTrace)

-- Not super happy about this tbh
instance MonadBase Infer Infer where
    liftBase = id

instance MonadUnique Infer where
    freshName text = MkInfer (liftIO (freshName text))
    newUnique = MkInfer (liftIO newUnique)

instance MonadRef Infer where
    type Ref Infer = IORef
    newRef x = MkInfer $ liftIO $ newIORef x
    readRef ref = MkInfer $ liftIO $ readIORef ref
    writeRef ref x = MkInfer $ liftIO $ writeIORef ref x

typeError :: TypeError -> Infer ()
typeError error = MkInfer do
    tell [error]
    trace Types (errorDoc "TYPE ERROR")

-- | Raise an irrecoverable type error that aborts the remaining execution
fatalTypeError :: TypeError -> Infer a
fatalTypeError error = MkInfer $ throwError error

liftEval :: Eval a -> Infer a
liftEval eval = MkInfer do
    traceAction <- ask
    let ?traceAction = traceAction
    liftIO (runEval eval)

modifyContext :: (EvalContext -> EvalContext) -> Env -> Env
modifyContext f env = env{evalContext = f env.evalContext}

runInfer :: (?traceAction :: TraceAction IO) => Infer a -> IO (These (Difflist TypeError) a)
runInfer (MkInfer infer) =
    flip evalStateT initialInferState (runWriterT (runExceptT (runReaderT infer ?traceAction))) >>= \case
        (Left fatalError, nonFatalErrors) -> pure (This (nonFatalErrors <> [fatalError]))
        (Right result, []) -> pure $ That result
        (Right result, nonFatalErrors) -> pure $ These nonFatalErrors result
  where
    initialInferState = MkInferState{}

freshMeta :: Name -> Infer MetaVar
freshMeta name = MkInfer $ liftIO do
    ref <- newIORef Nothing
    unique <- newUnique
    pure (MkMeta name unique ref)

freshAnonymousMeta :: Infer MetaVar
freshAnonymousMeta = do
    name <- freshName "a"
    freshMeta name

readMetaVar :: MetaVar -> Infer (Maybe Type)
readMetaVar (MkMeta _ _ ref) =
    MkInfer (liftIO (readIORef ref))

setMetaVar :: MetaVar -> Type -> Infer ()
setMetaVar (MkMeta _ _ ref) type_ =
    MkInfer (liftIO (writeIORef ref (Just type_)))

followMetas :: (HasContext context) => context -> Type -> Infer Type
followMetas context type_ = liftEval (Eval.followMetas context type_)

emptyEnv :: Env
emptyEnv =
    MkEnv
        { varTypes = mempty
        , dataConstructors = mempty
        , evalContext = emptyEvalContext
        }

variableType :: Env -> Name -> Type
variableType env name = case lookup name env.varTypes of
    Nothing -> error ("unbound variable in type checker (this should have been caught earlier!): " <> show name)
    Just type_ -> type_

instantiate :: Type -> Infer Type
instantiate = \case
    Forall name _domain (codomainExpr, codomainContext) -> do
        meta <- freshMeta name
        metaValue <- lazyValueM (StuckMeta meta [])
        instantiated <- liftEval $ eval (define name metaValue codomainContext) codomainExpr
        instantiate instantiated
    type_ -> pure type_

skolemize :: Type -> Infer Type
skolemize = \case
    Forall name _domain (codomainExpr, codomainContext) -> do
        skolem <- freshSkolem name
        varValue <- lazyValueM (StuckSkolem skolem [])
        skolemized <- liftEval $ eval (define name varValue codomainContext) codomainExpr
        skolemize skolemized
    type_ -> pure type_

typecheck :: (?traceAction :: TraceAction IO) => Vector (Declaration Renamed) -> IO (These (Difflist TypeError) (Vector CoreDeclaration))
typecheck declarations = runInfer do
    (_env, declarations) <- mapAccumLM checkDeclaration emptyEnv declarations
    pure declarations

checkDeclaration :: Env -> Declaration Renamed -> Infer (Env, CoreDeclaration)
checkDeclaration env decl = withTrace Types ("checkDeclaration: " <> showHeadConstructor decl) $ case decl of
    DefineFunction _loc name typeExpr params body -> do
        typeCore <- check env Type typeExpr
        type_ <- liftEval $ eval (getContext env) typeCore

        innerType <- skolemize type_

        (envTrans, _patternValues, corePatterns, resultType) <- checkParameterPatterns env innerType params

        let addLambdas core = do
                foldrM
                    ( \pattern_ core -> do
                        varName <- freshName "x"
                        body <- Pattern.lowerCase [(pattern_, core)] varName
                        pure $ CLambda varName body
                    )
                    core
                    corePatterns

        -- Recursive definitions are able to mention themselves on the type level
        -- so we need to do this recursive dance with mdo
        mdo
            (core, lazyValue) <- do
                let envWithParams = envTrans env

                value <- lazyM (eval (getContext env) core)
                -- function definitions are recursive
                let bodyEnv = extendVariable name type_ value envWithParams

                core <- addLambdas =<< check bodyEnv resultType body
                pure (core, value)
            -- TODO: If we are immediately forcing the value here anyway, do we even need it to be lazy?
            value <- liftEval $ forceM lazyValue
            pure (extendVariable name type_ lazyValue env, CDefineVar name value)
    DefineGADT loc typeConstructorName kind constructors -> do
        kindCore <- check env Type kind
        kindValue <- liftEval $ eval env.evalContext kindCore
        typeConValue <- liftEval $ lazyValueM $ TypeConstructorApp typeConstructorName []
        let envWithGADT = extendVariable typeConstructorName kindValue typeConValue env

        (env, constructors) <- forAccumL envWithGADT constructors \env (dataConstructorName, sourceType) -> do
            coreType <- check env Type sourceType
            type_ <- liftEval $ eval env.evalContext coreType

            -- We need to check that the constructor actually returns the type we are defining.
            -- To make this robust, we need to use unification though since someone might reasonably
            -- return something that doesn't necessarily look like the type we expect at first glance.
            definedReturnType <- curriedReturnType env type_

            typeConstructorArgumentCount <- numberOfCurriedArguments env kindValue
            expectedReturnType <-
                TypeConstructorApp typeConstructorName
                    . viaList
                    <$> replicateM typeConstructorArgumentCount (fmap (\meta -> StuckMeta meta []) freshAnonymousMeta)
            subsumes env loc definedReturnType expectedReturnType

            value <- lazyValueM $ DataConstructorApp dataConstructorName []

            let envWithConstructorVar = extendVariable dataConstructorName type_ value env
            let envWithConstructor = extendConstructor dataConstructorName type_ envWithConstructorVar

            argCount <- numberOfCurriedArguments env type_
            pure (envWithConstructor, (dataConstructorName, argCount))

        pure (env, CDefineGADT typeConstructorName constructors)

curriedReturnType :: (HasContext context) => context -> Type -> Infer Type
curriedReturnType context type_ =
    followMetas context type_ >>= \case
        Forall name _domain (codomainExpr, codomainContext) -> do
            resultType <- liftEval $ skolemizeClosure (Just name) codomainExpr codomainContext
            curriedReturnType context resultType
        Pi mname _domain (codomainExpr, codomainContext) -> do
            resultType <- liftEval $ skolemizeClosure mname codomainExpr codomainContext
            curriedReturnType context resultType
        type_ -> pure type_

numberOfCurriedArguments :: (HasContext context) => context -> Type -> Infer Int
numberOfCurriedArguments context type_ =
    followMetas context type_ >>= \case
        Forall name _domain (codomainExpr, codomainContext) -> do
            resultType <- liftEval $ skolemizeClosure (Just name) codomainExpr codomainContext
            -- Forall's are erased... for now
            numberOfCurriedArguments context resultType
        Pi mname _domain (codomainExpr, codomainContext) -> do
            resultType <- liftEval $ skolemizeClosure mname codomainExpr codomainContext
            (1 +) <$> numberOfCurriedArguments context resultType
        _ -> pure 0

infer :: Env -> Expr Renamed -> Infer (Type, CoreExpr)
infer env expr = withTrace Types ("infer" <+> showHeadConstructor expr) $ do
    (type_, core) <- case expr of
        Var _loc name -> do
            type_ <- instantiate (variableType env name)
            pure (type_, CVar name)
        App loc function argument -> do
            (functionType, functionCore) <- infer env function
            (parameterName, parameterType, resultClosureExpr, resultClosureContext) <- splitFunctionType env loc functionType

            argumentCore <- check env parameterType argument
            argumentValue <- lazyM $ eval (getContext env) argumentCore

            let updatedContext = case parameterName of
                    Nothing -> resultClosureContext
                    Just name -> define name argumentValue resultClosureContext

            rawResultType <- liftEval $ eval updatedContext resultClosureExpr
            resultType <- instantiate rawResultType
            pure (resultType, CApp functionCore argumentCore)
        Lambda _loc pattern_ body -> do
            (varType, envTrans, bodyPattern) <- inferPattern env pattern_

            (resultType, bodyCore) <- infer (envTrans env) body

            coreName <- freshName "x"

            body <- Pattern.lowerCase [(bodyPattern, bodyCore)] coreName

            pure (Pi Nothing varType (CQuote resultType, getContext env), CLambda coreName body)
        Case _loc scrutinee cases -> do
            (scrutineeType, scrutineeCore) <- infer env scrutinee

            scrutineeVar <- freshName "x"

            resultMeta <- freshAnonymousMeta
            let resultType = StuckMeta resultMeta []
            newCases <- forM cases \(pattern_, body) -> do
                (envTrans, _patternValue, corePattern) <- checkPattern env scrutineeType pattern_
                coreBody <- check (envTrans env) resultType body

                pure (corePattern, coreBody)
            coreCases <- Pattern.lowerCase newCases scrutineeVar
            pure (resultType, CLet scrutineeVar scrutineeCore coreCases)
        TupleLiteral _loc arguments -> do
            (argumentTypes, argumentCores) <- munzip <$> traverse (infer env) arguments
            pure (TupleType argumentTypes, CTupleLiteral argumentCores)
        Literal _loc literal -> pure (type_, CLiteral literal)
          where
            type_ = case literal of
                TypeLit -> Type -- Yes Type : Type, fight me
                IntTypeLit -> Type
                StringTypeLit -> Type
                IntLit _ -> Int
                StringLit _ -> String
        Sequence _loc [] -> pure (TupleType [], CTupleLiteral [])
        Sequence _loc (Vector.unsnoc -> Just (statements, RunExpr _ expr)) -> do
            (env, coreTransformers) <- mapAccumLM checkStatement env statements
            (finalType, finalCore) <- infer env expr
            core <- composeM coreTransformers finalCore
            pure (finalType, core)
        Sequence _loc statements -> do
            (_env, coreTransformers) <- mapAccumLM checkStatement env statements
            core <- composeM coreTransformers (CTupleLiteral [])
            pure (TupleType [], core)
        Ascription _loc expr typeExpr -> do
            typeCore <- check env Type typeExpr
            type_ <- liftEval $ eval (getContext env) typeCore

            coreExpr <- check env type_ expr
            pure (type_, coreExpr)
        EPi _loc maybeName domain codomain -> do
            domainCore <- check env Type domain
            domainValue <- liftEval $ eval (getContext env) domainCore

            codomainEnv <- case maybeName of
                Nothing -> pure env
                Just name -> do
                    skolem <- freshSkolem name
                    varValue <- lazyValueM $ StuckSkolem skolem []

                    pure (extendVariable name domainValue varValue env)

            codomainCore <- check codomainEnv Type codomain

            pure (Type, CPi maybeName domainCore codomainCore)
        EForall _loc name domain codomain -> do
            domainCore <- check env Type domain
            domainValue <- liftEval $ eval (getContext env) domainCore

            skolem <- freshSkolem name

            varValue <- lazyValueM $ StuckSkolem skolem []

            codomainCore <- check (extendVariable name domainValue varValue env) Type codomain

            pure (Type, CForall name domainCore codomainCore)
        ETupleType _loc arguments -> do
            argumentCores <- traverse (check env Type) arguments
            pure (Type, CTupleType argumentCores)
        Primop _loc primop -> do
            let (WrapPrimopType type_) = primopType primop
            pure (type_, CPrimop primop)
    trace Types ("infer:" <+> showHeadConstructor expr <+> keyword "=>" <+> pretty type_)
    pure (type_, core)

check :: Env -> Type -> Expr Renamed -> Infer CoreExpr
check env rawExpectedType expr = withTrace
    Types
    ("check:" <+> showHeadConstructor expr <+> keyword "<=" <+> pretty rawExpectedType)
    do
        expectedType <- skolemize rawExpectedType
        let deferToInference = do
                (actualType, core) <- infer env expr
                subsumes env (getLoc expr) actualType expectedType
                pure core
        case expr of
            Var{} -> deferToInference
            App{} -> deferToInference
            Lambda loc pattern_ body -> do
                (parameterName, parameterType, resultClosureExpr, resultClosureContext) <- splitFunctionType env loc expectedType

                (envTrans, parameterValue, corePattern) <- checkPattern env parameterType pattern_

                let updatedContext = case parameterName of
                        Nothing -> resultClosureContext
                        Just name -> define name parameterValue resultClosureContext

                resultType <- liftEval $ eval updatedContext resultClosureExpr

                bodyCore <- check (envTrans env) resultType body

                varName <- freshName "x"
                body <- Pattern.lowerCase [(corePattern, bodyCore)] varName

                pure (CLambda varName body)
            Case _loc scrutinee cases -> do
                (scrutineeType, scrutineeCore) <- infer env scrutinee

                scrutineeVar <- freshName "x"

                newCases <- forM cases \(pattern_, body) -> do
                    (envTrans, _patternValue, corePattern) <- checkPattern env scrutineeType pattern_
                    coreBody <- check (envTrans env) expectedType body

                    pure (corePattern, coreBody)
                CLet scrutineeVar scrutineeCore <$> Pattern.lowerCase newCases scrutineeVar
            TupleLiteral loc arguments -> do
                argumentTypes <- splitTupleType env loc expectedType (length arguments)

                argumentCore <- Vector.zipWithM (check env) argumentTypes arguments

                pure (CTupleLiteral argumentCore)
            Literal{} -> deferToInference
            Sequence _ (Vector.unsnoc -> Just (statements, RunExpr _ expr)) -> do
                (env, coreTransformers) <- mapAccumLM checkStatement env statements
                finalCore <- check env expectedType expr

                composeM coreTransformers finalCore
            Sequence _ statements -> do
                (_env, coreTransformersM) <- mapAccumLM checkStatement env statements
                composeM coreTransformersM (CTupleLiteral [])
            Ascription{} -> deferToInference
            Primop{} -> deferToInference
            EPi{} -> deferToInference
            EForall{} -> deferToInference
            ETupleType{} -> deferToInference

checkStatement :: Env -> Statement Renamed -> Infer (Env, CoreExpr -> Infer CoreExpr)
checkStatement env = \case
    RunExpr _ expr -> do
        -- TODO: Keep some context to mention in error messages that this was expected to return ()
        -- because it is run as a statement
        coreExpr <- check env (TupleType []) expr
        coreName <- freshName "_"
        pure (env, \coreCont -> pure $ CLet coreName coreExpr coreCont)
    -- we include a special case for variable patterns that are meant to be transparent
    -- TODO: shouldn't non-variable patterns also be transparent?
    Let _loc (VarPat _varLoc varName) body -> do
        mdo
            (bodyCore, value, updatedEnv) <- do
                (type_, bodyCore) <- infer env body
                let updatedEnv = extendVariable varName type_ value env
                value <- lazyM (eval (getContext updatedEnv) bodyCore)
                pure (bodyCore, value, updatedEnv)

            pure (updatedEnv, pure . CLet varName bodyCore)
    Let _loc pattern_ body -> do
        (patternType, envTrans, corePattern) <- inferPattern env pattern_

        -- TODO: dependent type things? ugh i guess just updating the env could do that?
        bodyCore <- check (envTrans env) patternType body

        let coreExpr cont = do
                -- TODO: I'm really not happy about the unnecessary let binding here
                coreVarName <- freshName "x"
                caseCore <- Pattern.lowerCase [(corePattern, cont)] coreVarName
                pure (CLet coreVarName bodyCore caseCore)

        pure (envTrans env, coreExpr)
    LetFunction _ name mtype patterns body -> do
        (ownType, resultType, envTransformer, corePatterns) <- case mtype of
            Just type_ -> do
                core <- check env Type type_
                ownType <- liftEval (eval (getContext env) core)

                innerType <- skolemize ownType

                (envTrans, _patternValues, corePatterns, resultType) <- checkParameterPatterns env innerType patterns

                pure (ownType, resultType, envTrans, viaList corePatterns)
            Nothing -> do
                (patternTypes, envTransformers, corePatterns) <- Vector.unzip3 <$> traverse (inferPattern env) patterns
                resultMeta <- freshAnonymousMeta
                let resultType = StuckMeta resultMeta []
                let ownType = foldr (\domain codomain -> Pi Nothing domain (CQuote codomain, emptyContext)) resultType patternTypes
                pure (ownType, resultType, compose envTransformers, corePatterns)
        let addLambdas core = do
                foldrM
                    ( \pattern_ core -> do
                        varName <- freshName "x"
                        body <- Pattern.lowerCase [(pattern_, core)] varName
                        pure $ CLambda varName body
                    )
                    core
                    corePatterns
        let updatedEnv = envTransformer env
        mdo
            (core, value) <- do
                value <- lazyM (eval (getContext env) core)
                -- function definitions are recursive
                let bodyEnv = extendVariable name ownType value updatedEnv

                core <- addLambdas =<< check bodyEnv resultType body
                pure (core, value)
            pure (extendVariable name ownType value env, pure . CLet name core)

inferPattern :: Env -> Pattern Renamed -> Infer (Type, Env -> Env, CorePattern (Fix CorePattern))
inferPattern env = \case
    VarPat _loc name -> do
        varMeta <- freshAnonymousMeta
        let varType = StuckMeta varMeta []
        varSkolem <- freshSkolem name
        varValue <- lazyValueM $ StuckSkolem varSkolem []
        pure (varType, extendVariable name varType varValue, CVarPat name)
    ConstructorPat _ _ _ -> undefined
    IntPat _loc value -> pure (Int, id, CIntPat value)
    StringPat _loc value -> pure (String, id, CStringPat value)
    TuplePat _loc subpatterns -> do
        (subTypes, subEnvTransformers, subCorePatterns) <- Vector.unzip3 <$> traverse (inferPattern env) subpatterns
        pure (TupleType subTypes, compose subEnvTransformers, CTuplePat (coerce subCorePatterns))
    OrPat{} -> undefined
    TypePat loc pattern_ type_ -> do
        typeCore <- check env Type type_
        type_ <- liftEval $ eval env.evalContext typeCore
        -- TODO: why don't we need the value here?
        (env_trans, _value, corePattern) <- checkPattern env type_ pattern_
        pure (type_, env_trans, corePattern)

checkPattern :: Env -> Type -> Pattern Renamed -> Infer (Env -> Env, LazyM Eval Value, CorePattern (Fix CorePattern))
checkPattern env expectedType = \case
    VarPat _loc name -> do
        skolem <- freshSkolem name
        value <- lazyValueM (StuckSkolem skolem [])
        pure (extendVariable name expectedType value, value, CVarPat name)
    ConstructorPat _loc name subPatterns -> do
        case lookup name env.dataConstructors of
            Nothing -> error $ "unbound data constructor in type checker: " <> show name
            Just constructorType -> do
                constructorType <- instantiate constructorType
                (envTrans, subPatternValues, subPatterns, resultType) <- checkParameterPatterns env constructorType subPatterns

                gadtEqualityEnvTrans <- modifyContext <$> givenEqual env expectedType resultType

                value <- lazyM do
                    values <- traverse forceM subPatternValues
                    pure (DataConstructorApp name values)
                pure (gadtEqualityEnvTrans . envTrans, value, CConstructorPat name (coerce $ viaList @_ @(Vector _) subPatterns))
    IntPat loc n -> do
        subsumes env loc Int expectedType
        value <- lazyValueM (IntV n)
        pure (id, value, CIntPat n)
    StringPat loc literal -> do
        subsumes env loc String expectedType
        value <- lazyValueM (StringV literal)
        pure (id, value, CStringPat literal)
    TuplePat loc subPatterns -> do
        argumentTypes <- splitTupleType env loc expectedType (length subPatterns)
        (subEnvTransformers, subValues, subPatterns) <- Vector.unzip3 <$> Vector.zipWithM (checkPattern env) argumentTypes subPatterns
        value <- lazyM (TupleV <$> traverse forceM subValues)
        pure (compose subEnvTransformers, value, CTuplePat (coerce subPatterns))
    OrPat{} -> undefined
    TypePat loc pattern_ type_ -> do
        typeCore <- check env Type type_
        type_ <- liftEval $ eval env.evalContext typeCore
        (env_trans, value, corePattern) <- checkPattern env type_ pattern_
        subsumes env loc type_ expectedType
        pure (env_trans, value, corePattern)

checkParameterPatterns
    :: (Uncons t (Pattern Renamed))
    => Env
    -> Type
    -> t
    -> Infer (Env -> Env, Seq (LazyM Eval Value), Seq (CorePattern (Fix CorePattern)), Type)
checkParameterPatterns _env type_ Nil = pure (id, [], [], type_)
checkParameterPatterns env type_ (pattern_ ::: restPatterns) = do
    (mTypeParamName, domain, codomainExpr, codomainContext) <- splitFunctionType env (getLoc pattern_) type_
    (envTrans, patternValue, pattern_) <- checkPattern env domain pattern_

    let evalContext = case mTypeParamName of
            Nothing -> codomainContext
            Just typeParamName -> define typeParamName patternValue codomainContext
    codomain <- liftEval $ eval evalContext codomainExpr

    -- We need to apply the environment transformer to the environment for the remaining patterns here to allow the
    -- remaining patterns to depend on the fact that this one has been bound (which is also how lambdas behave).
    -- this is necessary to check definitions like `f n (xs : Vec n Int) = ...`.
    (restTrans, restValues, restPatterns, resultType) <- checkParameterPatterns (envTrans env) codomain restPatterns
    pure (restTrans . envTrans, patternValue :<| restValues, pattern_ :<| restPatterns, resultType)

splitFunctionType
    :: (HasContext context)
    => context
    -> Loc
    -> Type
    -> Infer (Maybe Name, Type, CoreExpr, EvalContext)
splitFunctionType context loc type_ =
    followMetas context type_ >>= \case
        Pi name parameterType (resultClosureExpr, resultClosureContext) ->
            pure (name, parameterType, resultClosureExpr, resultClosureContext)
        type_ -> do
            paramMeta <- freshAnonymousMeta
            resultMeta <- freshAnonymousMeta
            let resultClosureExpr = CMeta resultMeta
            let resultClosureContext = emptyEvalContext

            let paramType = StuckMeta paramMeta []

            subsumes context loc type_ (Pi Nothing paramType (resultClosureExpr, resultClosureContext))
            pure (Nothing, paramType, resultClosureExpr, resultClosureContext)

splitTupleType :: (HasContext context) => context -> Loc -> Type -> Int -> Infer (Vector Type)
splitTupleType context loc type_ expectedArgCount =
    followMetas context type_ >>= \case
        TupleType arguments
            | length arguments == expectedArgCount -> pure arguments
            | otherwise -> undefined
        type_ -> do
            argumentTypes <- Vector.replicateM expectedArgCount (fmap (\x -> StuckMeta x []) freshAnonymousMeta)
            subsumes context loc type_ (TupleType argumentTypes)
            pure argumentTypes

{- | Traverse two types together and call a function on sub type expressions
(usually a recursive call to the calling function that handles the interesting cases before calling this).

This will traverse pi types by alpha-normalizing them (i.e. skolemizing both with the same skolem).

Notably, this does *NOT* recurse into stuck skolem- or unification variable continuations
-}
zipTypes
    :: forall m context infer
     . (Monoid m, HasContext context, MonadBase Infer infer)
    => context
    -> (Type -> Type -> infer m)
    -- ^ recursive calls
    -> (Type -> Type -> infer m)
    -- ^ called if the types differ
    -> Type
    -> Type
    -> infer m
zipTypes context recur onDifferent type1 type2 = do
    type1 <- liftBase $ followMetas context type1
    type2 <- liftBase $ followMetas context type2
    let different = onDifferent type1 type2
    case type1 of
        IntV x -> case type2 of
            IntV y | x == y -> pure mempty
            _ -> different
        StringV x -> case type2 of
            StringV y | x == y -> pure mempty
            _ -> different
        Type -> case type2 of
            Type -> pure mempty
            _ -> different
        Int -> case type2 of
            Int -> pure mempty
            _ -> different
        String -> case type2 of
            String -> pure mempty
            _ -> different
        Pi mname1 domain1 (codomainCore1, codomainContext1) -> case type2 of
            Pi mname2 domain2 (codomainCore2, codomainContext2) -> do
                defaultName <- liftBase $ freshName "a"
                skolem <- liftBase $ freshSkolem (fromMaybe defaultName (mname1 <|> mname2))
                skolemValue <- liftBase $ lazyValueM (StuckSkolem skolem [])

                codomain1 <- case mname1 of
                    Nothing -> liftBase $ liftEval $ eval codomainContext1 codomainCore1
                    Just name1 -> liftBase $ liftEval $ eval (define name1 skolemValue codomainContext1) codomainCore1
                codomain2 <- case mname2 of
                    Nothing -> liftBase $ liftEval $ eval codomainContext2 codomainCore2
                    Just name2 -> liftBase $ liftEval $ eval (define name2 skolemValue codomainContext2) codomainCore2

                (<>)
                    <$> recur domain1 domain2
                    <*> recur codomain1 codomain2
            _ -> different
        Forall name1 domain1 (codomainCore1, codomainContext1) -> case type2 of
            Forall name2 domain2 (codomainCore2, codomainContext2) -> do
                -- We have to pick some name so we arbitrarily pick name1 (not super happy about this tbh)
                skolem <- liftBase $ freshSkolem name1
                skolemValue <- liftBase $ lazyValueM (StuckSkolem skolem [])

                codomain1 <- liftBase $ liftEval $ eval (define name1 skolemValue codomainContext1) codomainCore1
                codomain2 <- liftBase $ liftEval $ eval (define name2 skolemValue codomainContext2) codomainCore2

                (<>)
                    <$> recur domain1 domain2
                    <*> recur codomain1 codomain2
            _ -> different
        StuckMeta metaVar1 _cont1 -> case type2 of
            StuckMeta metaVar2 _cont2 | metaVar1 == metaVar2 -> pure mempty
            _ -> different
        StuckSkolem skolem1 _cont1 -> case type2 of
            StuckSkolem skolem2 _cont2 | skolem1 == skolem2 -> pure mempty
            _ -> different
        ClosureV{} -> undefined
        TupleV arguments1 -> case type2 of
            TupleV arguments2 -> foldMapM (uncurry recur) (mzip arguments1 arguments2)
            _ -> different
        TupleType arguments1 -> case type2 of
            TupleType arguments2 -> foldMapM (uncurry recur) (mzip arguments1 arguments2)
            _ -> different
        TypeConstructorApp name1 arguments1 -> case type2 of
            TypeConstructorApp name2 arguments2 | name1 == name2 -> do
                assertM (length arguments1 == length arguments2)
                foldMapM (uncurry recur) (mzip arguments1 arguments2)
            _ -> different
        DataConstructorApp name1 arguments1 -> case type2 of
            DataConstructorApp name2 arguments2 | name1 == name2 -> do
                assertM (length arguments1 == length arguments2)
                foldMapM (uncurry recur) (mzip arguments1 arguments2)
            _ -> different

givenEqual :: (HasContext context) => context -> Type -> Type -> Infer (EvalContext -> EvalContext)
givenEqual (getContext -> context) type1 type2 = do
    type1 <- followMetas context type1
    type2 <- followMetas context type2
    trace Unify ("[G]" <+> pretty type1 <+> pretty type2)

    let recurAll context args1 args2 = fmap appEndo
            $ flip evalStateT context
            $ flip foldMapM (mzip args1 args2) \(arg1, arg2) -> do
                context <- get
                contextTrans <- lift $ givenEqual context arg1 arg2
                put (contextTrans context)
                pure (Endo contextTrans)

    case (type1, type2) of
        (StuckSkolem skolem1 cont1, StuckSkolem skolem2 cont2) | skolem1 == skolem2 -> undefined
        (StuckSkolem skolem [], type_) -> do
            pure $ defineSkolem skolem type_
        (type_, StuckSkolem skolem []) -> do
            pure $ defineSkolem skolem type_
        (StuckSkolem _skolem1 cont1, _type2) -> do
            -- TODO: No idea how to handle more interesting given equalities yet tbh
            undefined
        (_type1, StuckSkolem _skolem2 _args2) -> undefined
        -- We just ignore equalities on non-skolem types for now since we don't really
        -- have a way of handling them.
        _ ->
            fmap appEndo
                $ flip evalStateT context
                $ zipTypes
                    context
                    ( \type1 type2 -> do
                        context <- get
                        contextTrans <- lift (givenEqual context type1 type2)
                        put (contextTrans context)
                        pure (Endo contextTrans)
                    )
                    (\_ _ -> pure mempty)
                    type1
                    type2

subsumes :: (HasContext context) => context -> Loc -> Type -> Type -> Infer ()
subsumes context loc subtype supertype = do
    subtype <- instantiate subtype
    supertype <- skolemize supertype
    unify context loc subtype supertype

unify :: (HasContext context) => context -> Loc -> Type -> Type -> Infer ()
unify context loc type1 type2 = do
    type1 <- followMetas context type1
    type2 <- followMetas context type2
    trace Unify (pretty type1 <+> keyword "~" <+> pretty type2)

    let unableToUnify type1 type2 = do
            type1 <- liftEval $ quote context type1
            type2 <- liftEval $ quote context type2
            typeError (UnableToUnify loc type1 type2)

    case (type1, type2) of
        (Forall name1 domain1 (codomainCore1, codomainContext1), Forall name2 domain2 (codomainCore2, codomainContext2)) -> do
            skolem <- freshSkolem name1
            skolemValue <- lazyValueM (StuckSkolem skolem [])

            codomain1 <- liftEval $ eval (define name1 skolemValue codomainContext1) codomainCore1
            codomain2 <- liftEval $ eval (define name2 skolemValue codomainContext2) codomainCore2

            unify context loc domain1 domain2
            unify context loc codomain1 codomain2
        -- TODO: produce a more helpful error message
        -- TODO: this might not actually be an impredicative instantiation in all cases
        (Forall{}, _) -> typeError (Impredicative loc type1 type2)
        (_, Forall{}) -> typeError (Impredicative loc type1 type2)
        (StuckMeta metaVar1 cont1, StuckMeta metaVar2 cont2)
            | metaVar1 == metaVar2 ->
                unifyStuckCont context loc cont1 cont2
        (StuckMeta metaVar1 [], type2) -> bind context loc metaVar1 type2
        (type1, StuckMeta metaVar2 []) -> bind context loc metaVar2 type1
        -- See Note [Pattern Unification]
        (StuckMeta metaVar1 arguments1, type2) -> undefined -- patternUnification context metaVar1 arguments1 type2
        -- TODO: Keep track of the change of direction here for the sake of error messages
        (type1, StuckMeta metaVar2 arguments2) -> undefined -- patternUnification context metaVar2 arguments2 type1
        _ -> zipTypes context (unify context loc) unableToUnify type1 type2

unifyStuckCont
    :: (HasContext context)
    => context
    -> Loc
    -> Seq (StuckCont EvalContext)
    -> Seq (StuckCont EvalContext)
    -> Infer ()
-- TODO: something something pattern unification
unifyStuckCont context loc Empty Empty = pure ()
unifyStuckCont context loc (StuckApp argument1 :<| rest1) (StuckApp argument2 :<| rest2) = do
    unify context loc argument1 argument2
    unifyStuckCont context loc rest1 rest2
unifyStuckCont context loc _ _ = undefined

-- See Note [Pattern Unification]
patternUnification :: (HasContext context) => context -> MetaVar -> Seq Type -> Type -> Infer ()
patternUnification env metaVar arguments type2 =
    followMetas env type2 >>= \case
        -- TODO: This is kind of slow. We should figure out something more efficient
        -- TODO: Make sure we catch escaping skolems
        StuckSkolem skolem skolemArguments -> do
            undefined
        _ -> undefined

-- f : forall a. a -> a
-- f x = (x 5) ~ (?a 5) ==> ?a = x (?)

{-  Note [Pattern Unification]
    ~~~~~~~~~~~~~~~~~~~~~~~~~~
    We do pattern unification to infer applications of meta variables.

    Whenever we see (?f a b) ~ (C c d), we know (because type constructors are injective)
    that the only way to solve this is to set ?f := C and emit a ~ c, b ~ d.
    The same reasoning applies to skolems.
    TODO: Does it? Are skolems injective? I don't knooww.... -_-

    If the RHS is not a fully applied constructor or skolem application, we cannot make that kind of assumption.
    For example, if we were to try and solve `?f x y ~ List(x -> y)`, a simple constructor substitution like that
    would be insufficient.
    However, if the application spine consists entirely of *distinct* skolems that all occur in the RHS, there exists
    a single unique solution!
    In the case above, this would be `?f := λx y. List(x -> y)`.
-}

-- TODO: This also needs to update levels.
occursCheck :: (HasContext context) => context -> MetaVar -> Type -> Infer Bool
occursCheck context meta type_ =
    runExceptT (go type_) >>= \case
        Left () -> pure True
        Right () -> pure False
  where
    go :: Type -> ExceptT () Infer ()
    go type_ = do
        lift (followMetas context type_) >>= \case
            IntV _ -> pure ()
            StringV _ -> pure ()
            ClosureV (MkClosure name body context) -> do
                value <- lift $ liftEval $ skolemizeClosure (Just name) body context
                go value
            ClosureV (PrimopClosure _primop arguments) ->
                traverse_ go arguments
            TupleV arguments -> traverse_ go arguments
            DataConstructorApp _name arguments -> traverse_ go arguments
            TypeConstructorApp _name arguments -> traverse_ go arguments
            Type -> pure ()
            Int -> pure ()
            String -> pure ()
            TupleType arguments -> traverse_ go arguments
            Pi name domain (codomainCore, codomainContext) -> do
                go domain
                -- TODO: Rather than recomputing the codomain applied at a skolem at every occurs check,
                -- maybe we should lazily store this in the data type and keep the cached results?
                codomain <- lift $ liftEval $ skolemizeClosure name codomainCore codomainContext
                go codomain
            Forall name domain (codomainCore, codomainContext) -> do
                go domain

                codomain <- lift $ liftEval $ skolemizeClosure (Just name) codomainCore codomainContext
                go codomain
            StuckSkolem _ stuckCont -> do
                goCont stuckCont
            StuckMeta otherMeta stuckCont -> do
                if (meta == otherMeta)
                    then throwError ()
                    else goCont stuckCont

    goCont :: Seq (StuckCont EvalContext) -> ExceptT () Infer ()
    goCont = \case
        Empty -> pure ()
        (StuckApp argument :<| rest) -> do
            go argument
            goCont rest
        (StuckCase closureContext cases :<| rest) -> do
            -- TODO: I'm *not* happy about this
            for_ cases \case
                (CVarPat name, body) -> do
                    bodyValue <- lift $ liftEval $ skolemizeClosure (Just name) body closureContext
                    go bodyValue
                    goCont rest
                (_pattern, body) -> do
                    bodyValue <- lift $ liftEval $ skolemizeClosure Nothing body closureContext
                    go bodyValue
                    goCont rest

bind :: (HasContext context) => context -> Loc -> MetaVar -> Type -> Infer ()
bind context loc metaVar type_ = do
    readMetaVar metaVar >>= \case
        Just substituted -> do
            unify context loc substituted type_
        Nothing -> do
            trace Subst (pretty (StuckMeta metaVar []) <+> keyword ":=" <+> pretty type_)
            followMetas context type_ >>= \case
                StuckMeta metaVar2 [] | metaVar == metaVar2 -> pure ()
                type_ -> do
                    occursCheck context metaVar type_ >>= \case
                        True -> do
                            type_ <- liftEval $ quote context type_
                            typeError (OccursCheckViolation loc metaVar type_)
                        False -> setMetaVar metaVar type_
