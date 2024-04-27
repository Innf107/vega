module Vega.Infer (typecheck, TypeError (..)) where

import Vega.Prelude
import Vega.Syntax

import Vega.Eval (CoreDeclaration, CoreExpr, Eval, EvalContext, Value, applyClosure, define, emptyEvalContext, eval, runEval)
import Vega.Primop

import Vega.Debug
import Vega.LazyM
import Vega.Loc (HasLoc)
import Vega.Monad.Ref
import Vega.Pattern qualified as Pattern
import Vega.Pretty
import Vega.Trace
import Vega.Util

import Data.Foldable (foldrM)
import Data.Sequence qualified as Seq
import Data.Vector qualified as Vector

import Control.Monad.Fix
import Control.Monad.Writer.Strict (MonadWriter (tell), WriterT (runWriterT))
import Vega.Difflist (Difflist)
import Vega.Monad.Unique (MonadUnique (..))
import Vega.Name qualified as Name

data TypeError
    = UnableToUnify Loc CoreExpr CoreExpr
    | OccursCheckViolation Loc MetaVar CoreExpr
    | Impredicative Loc Type Type
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
        "Unable to construct an infinite type satisfying\n    " <> pretty (MetaApp metavar []) <> keyword " ~ " <> pretty type_
    pretty (Impredicative _ type1 type2) =
        "Impredicative instantiation attempted\n"
            <> "    "
            <> pretty type1
            <> keyword " ~ "
            <> pretty type2

type Type = Value
type MetaVar = MetaVarF EvalContext

data Env = MkEnv
    { varTypes :: Map Name Type
    , dataConstructors :: Map Name Type
    , evalContext :: EvalContext
    }

evalContext :: Env -> EvalContext
evalContext env = env.evalContext

extendVariable :: Name -> Type -> LazyM Eval Value -> Env -> Env
extendVariable name type_ value env =
    env
        { varTypes = insert name type_ env.varTypes
        , evalContext = define name value env.evalContext
        }

data InferState = MkInferState {}

newtype Infer a = MkInfer (ReaderT (TraceAction IO) (WriterT (Difflist TypeError) (StateT InferState IO)) a)
    deriving newtype (Functor, Applicative, Monad, MonadFix, MonadTrace)

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

liftEval :: Eval a -> Infer a
liftEval eval = MkInfer (liftIO (runEval eval))

runInfer :: (?traceAction :: TraceAction IO) => Infer a -> IO (a, Difflist TypeError)
runInfer (MkInfer exceptT) = evalStateT (runWriterT (runReaderT exceptT ?traceAction)) initialInferState
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

followMetas :: Type -> Infer Type
followMetas type_ = case type_ of
    MetaApp meta arguments ->
        readMetaVar meta >>= \case
            Nothing -> pure type_
            Just replacement -> do
                replacement <- followMetas replacement

                -- We do path compression.
                -- If a meta variable points to another substituted meta variable,
                -- we skip the indirection and bend the first one to point to the target directly.
                -- This means that further followMetas calls will only need to traverse one level of indirection
                -- rather than re-traversing the entire chain.
                -- Plus, this is extremely easy and fast to do so it's not like we're losing anything by doing path compression.
                setMetaVar meta replacement

                liftEval $ applyReplacement replacement arguments
              where
                applyReplacement replacement arguments = case replacement of
                    MetaApp meta replacedArguments ->
                        pure $ MetaApp meta (replacedArguments <> arguments)
                    SkolemApp skolem replacedArguments ->
                        pure $ SkolemApp skolem (replacedArguments <> arguments)
                    ClosureV closure ->
                        case arguments of
                            Empty -> pure (ClosureV closure)
                            (argument :<| rest) -> do
                                argument <- lazyValueM argument
                                applied <- applyClosure closure argument
                                applyReplacement applied rest
                    type_ -> case arguments of
                        Empty -> pure type_
                        arguments ->
                            error
                                $ "Meta variable substituted with non-application or closure type: "
                                <> prettyPlain
                                    ( pretty type_
                                        <> "\n   arguments: "
                                        <> sep (fmap pretty arguments)
                                    )
    type_ -> pure type_

freshSkolem :: (MonadUnique m) => Name -> m Skolem
freshSkolem name = do
    unique <- newUnique
    pure (MkSkolem name unique)

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
        metaValue <- lazyValueM (MetaApp meta [])
        instantiated <- liftEval $ eval (define name metaValue codomainContext) codomainExpr
        instantiate instantiated
    type_ -> pure type_

skolemize :: Type -> Infer Type
skolemize = \case
    Forall name _domain (codomainExpr, codomainContext) -> do
        skolem <- freshSkolem name
        varValue <- lazyValueM (SkolemApp skolem [])
        skolemized <- liftEval $ eval (define name varValue codomainContext) codomainExpr
        skolemize skolemized
    type_ -> pure type_

typecheck :: (?traceAction :: TraceAction IO) => Vector (Declaration Renamed) -> IO (Vector CoreDeclaration, Difflist TypeError)
typecheck declarations = runInfer do
    (_env, declarations) <- mapAccumLM checkDeclaration emptyEnv declarations
    pure declarations

checkDeclaration :: Env -> Declaration Renamed -> Infer (Env, CoreDeclaration)
checkDeclaration env decl = withTrace Types ("checkDeclaration: " <> showHeadConstructor decl) $ case decl of
    DefineFunction _loc name typeExpr params body -> do
        typeCore <- check env Type typeExpr
        type_ <- liftEval $ eval (evalContext env) typeCore

        innerType <- skolemize type_

        (envTrans, corePatterns, resultType) <- checkParameterPatterns env innerType params

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
            (core, value) <- do
                let envWithParams = envTrans env

                value <- lazyM (eval (evalContext env) core)
                -- function definitions are recursive
                let bodyEnv = extendVariable name type_ value envWithParams

                core <- addLambdas =<< check bodyEnv resultType body
                pure (core, value)
            pure (extendVariable name type_ value env, CDefineVar name core)
    DefineGADT loc name kind constructors -> do
        kindCore <- check env Type kind
        kindValue <- liftEval $ eval env.evalContext kindCore
        typeConValue <- liftEval $ lazyValueM $ TypeConstructorApp name []
        let envWithGADT = extendVariable name kindValue typeConValue env

        constructors <- forAccumL envWithGADT constructors \env (name, sourceType) -> do
            coreType <- check env Type sourceType
            type_ <- liftEval $ eval env.evalContext coreType
            -- TODO: Somehow check that the core type actually ends in `$name ...`

            undefined

        undefined

infer :: Env -> Expr Renamed -> Infer (Type, CoreExpr)
infer env expr = withTrace Types ("infer" <+> showHeadConstructor expr) $ do
    (type_, core) <- case expr of
        Var _loc name -> do
            type_ <- instantiate (variableType env name)
            pure (type_, CVar name)
        App loc function argument -> do
            (functionType, functionCore) <- infer env function
            (parameterName, parameterType, resultClosureExpr, resultClosureContext) <- splitFunctionType loc functionType

            argumentCore <- check env parameterType argument
            argumentValue <- lazyM $ eval (evalContext env) argumentCore

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

            pure (Pi Nothing varType (CQuote resultType, evalContext env), CLambda coreName body)
        Case _loc scrutinee cases -> do
            (scrutineeType, scrutineeCore) <- infer env scrutinee

            scrutineeVar <- freshName "x"

            resultType <- MetaApp <$> freshAnonymousMeta <*> pure []
            newCases <- forM cases \(pattern_, body) -> do
                (envTrans, _patternValue, corePattern) <- checkPattern env scrutineeType pattern_
                coreBody <- check (envTrans env) resultType body

                pure (corePattern, coreBody)
            coreCases <- Pattern.lowerCase newCases scrutineeVar
            pure (resultType, CLet scrutineeVar scrutineeCore coreCases)
        TupleLiteral _loc arguments -> do
            (argumentTypes, argumentCores) <- munzip <$> traverse (infer env) arguments
            pure (Tuple argumentTypes, CTupleLiteral argumentCores)
        Literal _loc literal -> pure (type_, CLiteral literal)
          where
            type_ = case literal of
                TypeLit -> Type -- Yes Type : Type, fight me
                IntTypeLit -> Type
                StringTypeLit -> Type
                IntLit _ -> Int
                StringLit _ -> String
        Sequence _loc [] -> pure (Tuple [], CTupleLiteral [])
        Sequence _loc (Vector.unsnoc -> Just (statements, RunExpr _ expr)) -> do
            (env, coreTransformers) <- mapAccumLM checkStatement env statements
            (finalType, finalCore) <- infer env expr
            core <- composeM coreTransformers finalCore
            pure (finalType, core)
        Sequence _loc statements -> do
            (_env, coreTransformers) <- mapAccumLM checkStatement env statements
            core <- composeM coreTransformers (CTupleLiteral [])
            pure (Tuple [], core)
        Ascription _loc expr typeExpr -> do
            typeCore <- check env Type typeExpr
            type_ <- liftEval $ eval (evalContext env) typeCore

            coreExpr <- check env type_ expr
            pure (type_, coreExpr)
        EPi _loc maybeName domain codomain -> do
            domainCore <- check env Type domain
            domainValue <- liftEval $ eval (evalContext env) domainCore

            codomainEnv <- case maybeName of
                Nothing -> pure env
                Just name -> do
                    skolem <- freshSkolem name
                    varValue <- lazyValueM $ SkolemApp skolem []

                    pure (extendVariable name domainValue varValue env)

            codomainCore <- check codomainEnv Type codomain

            pure (Type, CPi maybeName domainCore codomainCore)
        EForall _loc name domain codomain -> do
            domainCore <- check env Type domain
            domainValue <- liftEval $ eval (evalContext env) domainCore

            skolem <- freshSkolem name

            varValue <- lazyValueM $ SkolemApp skolem []

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
                subsumes (getLoc expr) actualType expectedType
                pure core
        case expr of
            Var{} -> deferToInference
            App{} -> deferToInference
            Lambda loc pattern_ body -> do
                (parameterName, parameterType, resultClosureExpr, resultClosureContext) <- splitFunctionType loc expectedType

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
                argumentTypes <- splitTupleType loc expectedType (length arguments)

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
        coreExpr <- check env (Tuple []) expr
        coreName <- freshName "_"
        pure (env, \coreCont -> pure $ CLet coreName coreExpr coreCont)
    -- we include a special case for variable patterns that are meant to be transparent
    -- TODO: shouldn't non-variable patterns also be transparent?
    Let _loc (VarPat _varLoc varName) body -> do
        mdo
            (bodyCore, value, updatedEnv) <- do
                (type_, bodyCore) <- infer env body
                let updatedEnv = extendVariable varName type_ value env
                value <- lazyM (eval (evalContext updatedEnv) bodyCore)
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
                ownType <- liftEval (eval (evalContext env) core)

                innerType <- skolemize ownType

                (envTrans, corePatterns, resultType) <- checkParameterPatterns env innerType patterns

                pure (ownType, resultType, envTrans, viaList corePatterns)
            Nothing -> do
                (patternTypes, envTransformers, corePatterns) <- Vector.unzip3 <$> traverse (inferPattern env) patterns
                resultMeta <- freshAnonymousMeta
                let resultType = MetaApp resultMeta []
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
                value <- lazyM (eval (evalContext env) core)
                -- function definitions are recursive
                let bodyEnv = extendVariable name ownType value updatedEnv

                core <- addLambdas =<< check bodyEnv resultType body
                pure (core, value)
            pure (extendVariable name ownType value env, pure . CLet name core)

inferPattern :: Env -> Pattern Renamed -> Infer (Type, Env -> Env, CorePattern (Fix CorePattern))
inferPattern env = \case
    VarPat _loc name -> do
        varMeta <- freshAnonymousMeta
        let varType = MetaApp varMeta []
        varSkolem <- freshSkolem name
        varValue <- lazyValueM $ SkolemApp varSkolem []
        pure (varType, extendVariable name varType varValue, CVarPat name)
    ConstructorPat _ _ _ -> undefined
    IntPat _loc value -> pure (Int, id, CIntPat value)
    StringPat _loc value -> pure (String, id, CStringPat value)
    TuplePat _loc subpatterns -> do
        (subTypes, subEnvTransformers, subCorePatterns) <- Vector.unzip3 <$> traverse (inferPattern env) subpatterns
        pure (Tuple subTypes, compose subEnvTransformers, CTuplePat (coerce subCorePatterns))
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
        value <- lazyValueM (SkolemApp skolem [])
        pure (extendVariable name expectedType value, value, CVarPat name)
    ConstructorPat _ _ _ -> undefined
    IntPat loc n -> do
        subsumes loc Int expectedType
        value <- lazyValueM (IntV n)
        pure (id, value, CIntPat n)
    StringPat loc literal -> do
        subsumes loc String expectedType
        value <- lazyValueM (StringV literal)
        pure (id, value, CStringPat literal)
    TuplePat loc subPatterns -> do
        argumentTypes <- splitTupleType loc expectedType (length subPatterns)
        (subEnvTransformers, subValues, subPatterns) <- Vector.unzip3 <$> Vector.zipWithM (checkPattern env) argumentTypes subPatterns
        value <- lazyM (TupleV <$> traverse forceM subValues)
        pure (compose subEnvTransformers, value, CTuplePat (coerce subPatterns))
    OrPat{} -> undefined
    TypePat loc pattern_ type_ -> do
        typeCore <- check env Type type_
        type_ <- liftEval $ eval env.evalContext typeCore
        (env_trans, value, corePattern) <- checkPattern env type_ pattern_
        subsumes loc type_ expectedType
        pure (env_trans, value, corePattern)

checkParameterPatterns :: (Uncons t (Pattern Renamed)) => Env -> Type -> t -> Infer (Env -> Env, Seq (CorePattern (Fix CorePattern)), Type)
checkParameterPatterns _env type_ Nil = pure (id, [], type_)
checkParameterPatterns env type_ (pattern_ ::: restPatterns) = do
    (mTypeParamName, domain, codomainExpr, codomainContext) <- splitFunctionType (getLoc pattern_) type_
    (envTrans, patternValue, pattern_) <- checkPattern env domain pattern_

    let evalContext = case mTypeParamName of
            Nothing -> codomainContext
            Just typeParamName -> define typeParamName patternValue codomainContext
    codomain <- liftEval $ eval evalContext codomainExpr

    -- We need to apply the environment transformer to the environment for the remaining pattenrs here since to allow the
    -- remaining patterns to depend on the fact that this one has been bound (which is also how lambdas behave).
    -- this is necessary to check definitions like `f n (xs : Vec n Int) = ...`.
    (restTrans, restPatterns, resultType) <- checkParameterPatterns (envTrans env) codomain restPatterns
    pure (restTrans . envTrans, pattern_ :<| restPatterns, resultType)

splitFunctionType :: Loc -> Type -> Infer (Maybe Name, Type, CoreExpr, EvalContext)
splitFunctionType loc type_ =
    followMetas type_ >>= \case
        Pi name parameterType (resultClosureExpr, resultClosureContext) ->
            pure (name, parameterType, resultClosureExpr, resultClosureContext)
        type_ -> do
            paramMeta <- freshAnonymousMeta
            resultMeta <- freshAnonymousMeta
            let resultClosureExpr = CMeta resultMeta
            let resultClosureContext = emptyEvalContext

            let paramType = MetaApp paramMeta []

            subsumes loc type_ (Pi Nothing paramType (resultClosureExpr, resultClosureContext))
            pure (Nothing, paramType, resultClosureExpr, resultClosureContext)

splitTupleType :: Loc -> Type -> Int -> Infer (Vector Type)
splitTupleType loc type_ expectedArgCount =
    followMetas type_ >>= \case
        Tuple arguments
            | length arguments == expectedArgCount -> pure arguments
            | otherwise -> undefined
        type_ -> do
            argumentTypes <- Vector.replicateM expectedArgCount (fmap (\x -> MetaApp x []) freshAnonymousMeta)
            subsumes loc type_ (Tuple argumentTypes)
            pure argumentTypes

subsumes :: Loc -> Type -> Type -> Infer ()
subsumes loc subtype supertype = do
    subtype <- instantiate subtype
    supertype <- skolemize supertype
    unify loc subtype supertype

unify :: Loc -> Type -> Type -> Infer ()
unify loc type1 type2 = do
    type1 <- followMetas type1
    type2 <- followMetas type2
    trace Unify (pretty type1 <+> keyword "~" <+> pretty type2)

    let unableToUnify = do
            type1 <- quoteFully type1
            type2 <- quoteFully type2
            typeError (UnableToUnify loc type1 type2)

    case (type1, type2) of
        (Forall name1 domain1 (codomainCore1, codomainContext1), Forall name2 domain2 (codomainCore2, codomainContext2)) -> do
            skolem <- freshSkolem name1
            skolemValue <- lazyValueM (SkolemApp skolem [])

            codomain1 <- liftEval $ eval (define name1 skolemValue codomainContext1) codomainCore1
            codomain2 <- liftEval $ eval (define name2 skolemValue codomainContext2) codomainCore2

            unify loc domain1 domain2
            unify loc codomain1 codomain2
        -- TODO: produce a more helpful error message
        -- TODO: this might not actually be an impredicative instantiation in all cases
        (Forall{}, _) -> typeError (Impredicative loc type1 type2)
        (_, Forall{}) -> typeError (Impredicative loc type1 type2)
        (MetaApp metaVar1 [], type2) -> bind loc metaVar1 type2
        (type1, MetaApp metaVar2 []) -> bind loc metaVar2 type1
        -- See Note [Pattern Unification]
        (MetaApp metaVar1 arguments1, type2) -> patternUnification metaVar1 arguments1 type2
        -- TODO: Keep track of the change of direction here for the sake of error messages
        (type1, MetaApp metaVar2 arguments2) -> patternUnification metaVar2 arguments2 type1
        _ -> case type1 of
            IntV x -> case type2 of
                IntV y | x == y -> pure ()
                _ -> unableToUnify
            StringV x -> case type2 of
                StringV y | x == y -> pure ()
                _ -> unableToUnify
            Type -> case type2 of
                Type -> pure ()
                _ -> unableToUnify
            Int -> case type2 of
                Int -> pure ()
                _ -> unableToUnify
            String -> case type2 of
                String -> pure ()
                _ -> unableToUnify
            Pi mname1 domain1 (codomainCore1, codomainContext1) -> case type2 of
                Pi mname2 domain2 (codomainCore2, codomainContext2) -> do
                    defaultName <- freshName "a"
                    skolem <- freshSkolem (fromMaybe defaultName (mname1 <|> mname2))
                    skolemValue <- lazyValueM (SkolemApp skolem [])

                    codomain1 <- case mname1 of
                        Nothing -> liftEval $ eval codomainContext1 codomainCore1
                        Just name1 -> liftEval $ eval (define name1 skolemValue codomainContext1) codomainCore1
                    codomain2 <- case mname2 of
                        Nothing -> liftEval $ eval codomainContext2 codomainCore2
                        Just name2 -> liftEval $ eval (define name2 skolemValue codomainContext2) codomainCore2

                    unify loc domain1 domain2
                    unify loc codomain1 codomain2
                _ -> unableToUnify
            SkolemApp skolem1 args1 -> case type2 of
                SkolemApp skolem2 args2 | skolem1 == skolem2 && length args1 == length args2 -> do
                    traverse_ (uncurry (unify loc)) (Seq.zip args1 args2)
                _ -> unableToUnify
            ClosureV{} -> undefined
            TupleV arguments1 -> case type2 of
                TupleV arguments2 -> Vector.zipWithM_ (unify loc) arguments1 arguments2
                _ -> unableToUnify
            Tuple arguments1 -> case type2 of
                Tuple arguments2 -> Vector.zipWithM_ (unify loc) arguments1 arguments2
                _ -> unableToUnify
            TypeConstructorApp name1 arguments1 -> case type2 of
                TypeConstructorApp name2 arguments2 | name1 == name2 -> do
                    assertM (length arguments1 == length arguments2)
                    zipWithM_ (unify loc) (toList arguments1) (toList arguments2)
                _ -> unableToUnify

-- See Note [Pattern Unification]
patternUnification :: MetaVar -> Seq Type -> Type -> Infer ()
patternUnification metaVar arguments type2 = case type2 of
    -- TODO: This is kind of slow. We should figure out something more efficient
    -- TODO: Make sure we catch escaping skolems
    SkolemApp skolem skolemArguments -> do
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
occursCheck :: MetaVar -> Type -> Infer Bool
occursCheck meta type_ =
    runExceptT (go type_) >>= \case
        Left () -> pure True
        Right () -> pure False
  where
    go :: Type -> ExceptT () Infer ()
    go type_ = do
        lift (followMetas type_) >>= \case
            IntV _ -> pure ()
            StringV _ -> pure ()
            ClosureV (MkClosure name body context) -> do
                value <- lift $ liftEval $ skolemizeClosure (Just name) body context
                go value
            ClosureV (PrimopClosure _primop arguments) ->
                traverse_ go arguments
            TupleV arguments -> traverse_ go arguments
            TypeConstructorApp _name arguments -> traverse_ go arguments
            Type -> pure ()
            Int -> pure ()
            String -> pure ()
            Tuple arguments -> traverse_ go arguments
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
            SkolemApp _ arguments -> traverse_ go arguments
            MetaApp otherMeta arguments -> do
                if (meta == otherMeta)
                    then throwError ()
                    else traverse_ go arguments

skolemizeClosure :: Maybe Name -> CoreExpr -> EvalContext -> Eval Type
skolemizeClosure mname codomainCore codomainContext = do
    codomainContext <- case mname of
        Nothing -> pure codomainContext
        Just name -> do
            codomainSkolem <- freshSkolem name
            skolemValue <- lazyValueM (SkolemApp codomainSkolem [])
            pure (define name skolemValue codomainContext)
    eval codomainContext codomainCore

bind :: Loc -> MetaVar -> Type -> Infer ()
bind loc metaVar type_ =
    readMetaVar metaVar >>= \case
        Just substituted -> do
            unify loc substituted type_
        Nothing -> do
            trace Subst (pretty (MetaApp metaVar []) <+> keyword ":=" <+> pretty type_)
            followMetas type_ >>= \case
                MetaApp metaVar2 [] | metaVar == metaVar2 -> pure ()
                type_ -> do
                    occursCheck metaVar type_ >>= \case
                        True -> do
                            type_ <- quoteFully type_
                            typeError (OccursCheckViolation loc metaVar type_)
                        False -> setMetaVar metaVar type_

-- TODO: This happens to early. If meta variables are inserted later they will still be *values* so
-- error messages are still wrong (and still rely on unsafePerformIO) :/

{- | Fully quote a type, e.g. for error messages.
Note that this also follows lazy `Quote`s inside CoreExprs
-}
quoteFully :: Type -> Infer CoreExpr
quoteFully type_ =
    followMetas type_ >>= \case
        IntV n -> pure $ CLiteral (IntLit n)
        StringV text -> pure $ CLiteral (StringLit text)
        ClosureV (MkClosure name body context) -> do
            value <- liftEval $ skolemizeClosure (Just name) body context
            quoteFully value
        ClosureV (PrimopClosure primop arguments) -> do
            quotedArguments <- traverse quoteFully arguments
            pure $ foldl' CApp (CPrimop primop) quotedArguments
        TupleV arguments -> do
            quotedArguments <- traverse quoteFully arguments
            pure $ CTupleLiteral quotedArguments
        TypeConstructorApp{} -> do
            undefined
        Type -> pure $ CLiteral TypeLit
        Int -> pure $ CLiteral IntTypeLit
        String -> pure $ CLiteral StringTypeLit
        Tuple arguments -> do
            quotedArguments <- traverse quoteFully arguments
            pure $ CTupleType quotedArguments
        Pi mname domain (codomainExpr, codomainEnv) -> do
            quotedDomain <- quoteFully domain
            codomain <- liftEval $ skolemizeClosure mname codomainExpr codomainEnv
            quotedCodomain <- quoteFully codomain
            pure $ CPi mname quotedDomain quotedCodomain
        Forall name domain (codomainExpr, codomainEnv) -> do
            quotedDomain <- quoteFully domain
            codomain <- liftEval $ skolemizeClosure (Just name) codomainExpr codomainEnv
            quotedCodomain <- quoteFully codomain
            pure $ CForall name quotedDomain quotedCodomain
        SkolemApp (MkSkolem skolemName skolemUnique) arguments -> do
            quotedArguments <- traverse quoteFully arguments
            -- We use the skolem unique as the variable unique here.
            -- This technically loses provenance of the skolem but we don't use that anywhere
            -- so it should be fine.
            -- Since Uniques are globally unique, this will not
            pure $ foldl' CApp (CVar (Name.makeDirectlyUnchecked (Name.original skolemName) skolemUnique)) quotedArguments
        MetaApp metaVar arguments -> do
            quotedArguments <- traverse quoteFully arguments
            pure $ foldl' CApp (CMeta metaVar) quotedArguments
