module Vega.Infer (typecheck, TypeError (..)) where

import Vega.Prelude
import Vega.Syntax

import Vega.Eval (CoreDeclaration, CoreExpr, Eval, EvalContext, Value, applyClosure, define, emptyEvalContext, eval, runEval)
import Vega.Name qualified as Name

import Vega.LazyM

import Vega.Loc (HasLoc)
import Vega.Pretty

import Data.Sequence qualified as Seq
import Data.Vector qualified as Vector

import Vega.MonadRef

data TypeError
    = UnableToUnify Loc Type Type
    deriving (Generic)
instance HasLoc TypeError

instance Pretty TypeError where
    pretty (UnableToUnify _ type1 type2) =
        "Unable to unify types "
            <> pretty type1
            <> "\n"
            <> "                  and "
            <> pretty type2

type Type = Value
type MetaVar = MetaVarF EvalContext

data Env = MkEnv
    { varTypes :: Map Name Type
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

newtype Infer a = MkInfer (ExceptT TypeError (StateT InferState IO) a)
    deriving (Functor, Applicative, Monad)

instance MonadRef Infer where
    type Ref Infer = IORef
    newRef x = MkInfer $ liftIO $ newIORef x
    readRef ref = MkInfer $ liftIO $ readIORef ref
    writeRef ref x = MkInfer $ liftIO $ writeIORef ref x

typeError :: TypeError -> Infer a
typeError error = MkInfer (throwError error)

liftEval :: Eval a -> Infer a
liftEval eval = MkInfer (liftIO (runEval eval))

runInfer :: Infer a -> IO (Either TypeError a)
runInfer (MkInfer exceptT) = evalStateT (runExceptT exceptT) initialInferState
  where
    initialInferState = MkInferState{}

freshName :: Text -> Infer Name
freshName text = MkInfer $ liftIO $ Name.freshNameIO text

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
                    type_ -> error $ "Meta variable substituted with non-application or closure type: " <> prettyPlain (pretty type_)
    type_ -> pure type_

freshSkolem :: Name -> Infer Skolem
freshSkolem name = MkInfer $ liftIO do
    unique <- newUnique
    pure (MkSkolem name unique)

emptyEnv :: Env
emptyEnv =
    MkEnv
        { varTypes = mempty
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

typecheck :: Vector (Declaration Renamed) -> IO (Either TypeError (Vector CoreDeclaration))
typecheck declarations = runInfer do
    (_env, declarations) <- mapAccumLM checkDeclaration emptyEnv declarations
    pure declarations

checkDeclaration :: Env -> Declaration Renamed -> Infer (Env, CoreDeclaration)
checkDeclaration env = \case
    DefineFunction _loc name typeExpr params body -> do
        -- TODO: Ugly hack so I don't need to deal with parameters here for now
        case params of
            -- TODO: This is the easiest way to do this for now, but in practice
            -- we need to be extra careful with parameterless functions around the order of (lazy?)
            -- initialization and things
            [] -> do
                typeCore <- check env Type typeExpr
                type_ <- liftEval $ eval (evalContext env) typeCore

                typeToCheckAgainst <- skolemize type_
                bodyCore <- check env typeToCheckAgainst body

                value <- lazyM $ eval (evalContext env) bodyCore

                pure (extendVariable name type_ value env, CDefineFunction name [] bodyCore)
            _ -> undefined

infer :: Env -> Expr Renamed -> Infer (Type, CoreExpr)
infer env = \case
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

        resultType <- liftEval $ eval updatedContext resultClosureExpr
        pure (resultType, CApp functionCore argumentCore)
    Lambda _loc pattern body -> do
        (varType, envTrans, bodyTrans) <- inferPattern env pattern

        (resultType, bodyCore) <- infer (envTrans env) body

        coreName <- freshName "x"

        pure (Pi undefined varType undefined, CLambda coreName (bodyTrans coreName bodyCore))
    Case loc scrutinee cases -> undefined
    Literal _loc literal -> pure (type_, CLiteral literal)
      where
        type_ = case literal of
            TypeLit -> Type -- Yes Type : Type, fight me
            IntTypeLit -> Type
            StringTypeLit -> Type
            IntLit _ -> Int
            StringLit _ -> String
    Sequence loc statements -> undefined
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

check :: Env -> Type -> Expr Renamed -> Infer CoreExpr
check env expectedType expr = do
    let deferToInference = do
            (actualType, core) <- infer env expr
            subsumes (getLoc expr) actualType expectedType
            pure core
    case expr of
        Var{} -> deferToInference
        App{} -> deferToInference
        Lambda loc pattern body -> do
            (parameterName, parameterType, resultClosureExpr, resultClosureContext) <- splitFunctionType loc expectedType

            (envTrans, coreTrans) <- checkPattern env parameterType pattern

            -- TODO: This is meant to be a different skolem than the one on the term level, right?

            updatedContext <- case parameterName of
                Nothing -> pure resultClosureContext
                Just name -> do
                    parameterSkolem <- freshSkolem name
                    parameterValue <- lazyValueM $ SkolemApp parameterSkolem []
                    pure $ define name parameterValue resultClosureContext

            resultType <- liftEval $ eval updatedContext resultClosureExpr

            bodyCore <- check (envTrans env) resultType body

            varName <- freshName "x"
            pure (CLambda varName (coreTrans varName bodyCore))
        Case _loc _scrutinee _cases -> undefined
        Literal{} -> deferToInference
        Sequence _loc _statements -> undefined
        Ascription{} -> deferToInference
        EPi _loc name domain codomain -> deferToInference
        EForall loc name kind body -> deferToInference

inferPattern :: Env -> Pattern Renamed -> Infer (Type, Env -> Env, Name -> CoreExpr -> CoreExpr)
inferPattern env = \case
    VarPat _loc name -> do
        varMeta <- freshAnonymousMeta
        let varType = MetaApp varMeta []
        varSkolem <- freshSkolem name
        varValue <- lazyValueM $ SkolemApp varSkolem []
        pure (varType, extendVariable name varType varValue, \bound -> CLet name (CVar bound))
    IntPat _loc value -> pure (Int, id, undefined)
    StringPat _loc value -> pure (String, id, undefined)
    OrPat{} -> undefined

checkPattern :: Env -> Type -> Pattern Renamed -> Infer (Env -> Env, Name -> CoreExpr -> CoreExpr)
checkPattern _env expectedType = \case
    VarPat _loc name -> do
        varSkolem <- freshSkolem name
        varValue <- lazyValueM $ SkolemApp varSkolem []
        pure (extendVariable name expectedType varValue, \binding -> CLet name (CVar binding))
    IntPat{} -> undefined
    StringPat{} -> undefined
    OrPat{} -> undefined

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

subsumes :: Loc -> Type -> Type -> Infer ()
subsumes loc subtype supertype = do
    subtype <- instantiate subtype
    supertype <- skolemize supertype
    unify loc subtype supertype

unify :: Loc -> Type -> Type -> Infer ()
unify loc type1 type2 = do
    type1 <- followMetas type1
    type2 <- followMetas type2
    case (type1, type2) of
        (IntV x, IntV y) | x == y -> pure ()
        (StringV x, StringV y) | x == y -> pure ()
        (Type, Type) -> pure ()
        (Int, Int) -> pure ()
        (String, String) -> pure ()
        (Pi mname1 domain1 codomain1, Pi mname2 domain2 codomain2) -> do
            unify loc domain1 domain2
            undefined
        (Forall mname1 domain1 codomain1, Forall mname2 domain2 codomain2) ->
            undefined
        (SkolemApp skolem1 args1, SkolemApp skolem2 args2)
            | skolem1 == skolem2 && length args1 == length args2 -> do
                traverse_ (uncurry (unify loc)) (Seq.zip args1 args2)
        (MetaApp metaVar1 [], type2) -> bind metaVar1 type2
        (type1, MetaApp metaVar2 []) -> bind metaVar2 type1
        -- See Note [Pattern Unification]
        (MetaApp metaVar1 arguments1, type2) -> patternUnification metaVar1 arguments1 type2
        _ -> typeError (UnableToUnify loc type1 type2)

-- See Note [Pattern Unification]
patternUnification :: MetaVar -> Seq Type -> Type -> Infer ()
patternUnification metaVar arguments type2 =
    -- TODO: This is kind of slow. We should figure out something more efficient
    -- TODO: Make sure we catch escaping skolems
    undefined

{-  Note [Pattern Unification]
    ~~~~~~~~~~~~~~~~~~~~~~~~~~
    We do pattern unification to infer applications of meta variables.

    Whenever we see (?f a b) ~ (C c d), we know (because type constructors are injective)
    that the only way to solve this is to set ?f := C and emit a ~ c, b ~ d.
    The same reasoning applies to skolems.

    If the RHS is not a fully applied constructor or skolem application, we cannot make that kind of assumption.
    For example, if we were to try and solve `?f x y ~ List(x -> y)`, a simple constructor substitution like that
    would be insufficient.
    However, if the application spine consists entirely of *distinct* skolems that all occur in the RHS, there exists
    a single unique solution!
    In the case above, this would be `?f := λx y. List(x -> y)`.
-}

bind :: MetaVar -> Type -> Infer ()
bind = undefined
