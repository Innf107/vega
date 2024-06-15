module Vega.Eval (
    Eval,
    runEval,
    EvalContext,
    HasContext (..),
    emptyEvalContext,
    define,
    freshSkolem,
    skolemizeClosure,
    defineSkolem,
    followMetas,
    lookupVar,
    Value,
    CoreDeclaration,
    CoreExpr,
    eval,
    applyClosure,
    quote,
) where

import Vega.Prelude
import Vega.Syntax

import Vega.Primop

import Data.Map qualified as Map
import System.IO.Unsafe (unsafePerformIO)
import Vega.Debug (showHeadConstructor)
import Vega.LazyM
import Vega.Monad.Ref
import Vega.Monad.Unique
import Vega.Name (ident)
import Vega.Name qualified as Name
import Vega.Pretty hiding (quote)
import Vega.Trace

newtype Eval a = MkEval (ReaderT (TraceAction IO) IO a)
    deriving newtype (Functor, Applicative, Monad, MonadTrace)

instance MonadRef Eval where
    type Ref Eval = IORef
    writeRef ref x = MkEval $ liftIO $ writeRef ref x
    readRef ref = MkEval $ liftIO $ readRef ref
    newRef initial = MkEval $ liftIO $ newRef initial

instance MonadUnique Eval where
    freshName text = MkEval $ liftIO $ freshName text
    newUnique = MkEval $ liftIO newUnique

class MonadEval m where
    liftEval :: Eval a -> m a

instance MonadEval Eval where
    liftEval = id

runEval :: (?traceAction :: TraceAction IO) => Eval a -> IO a
runEval (MkEval io) = runReaderT io ?traceAction

type Value = ValueF EvalContext
type Type = Value

type CoreDeclaration = CoreDeclarationF EvalContext

type CoreExpr = CoreExprF EvalContext

type Closure = ClosureF EvalContext

data EvalContext = MkEvalContext
    { varValues :: Map Name (LazyM Eval Value)
    , skolemBindings :: Map Skolem Value
    }

class HasContext context where
    getContext :: context -> EvalContext

instance HasContext EvalContext where
    getContext = id

instance ContextFromEmpty EvalContext where
    emptyContext = emptyEvalContext

instance EvalClosureForPrinting EvalContext where
    applyNullaryClosurePrint context expr = do
        let ?traceAction = ignoredTraceAction
        runEval $ eval context expr
    applyClosureForPrinting context expr name = do
        let ?traceAction = ignoredTraceAction
        runEval do
            let skolem = MkSkolem name (Name.unique name)
            lazyValue <- lazyValueM (StuckSkolem skolem [])
            applyClosure (MkClosure name expr context) lazyValue

emptyEvalContext :: EvalContext
emptyEvalContext =
    MkEvalContext
        { varValues = mempty
        , skolemBindings = mempty
        }

define :: Name -> LazyM Eval Value -> EvalContext -> EvalContext
define name value context = context{varValues = insert name value context.varValues}

defineSkolem :: Skolem -> Value -> EvalContext -> EvalContext
defineSkolem skolem value context = context{skolemBindings = insert skolem value context.skolemBindings}

lookupVar :: Name -> EvalContext -> Maybe Value
lookupVar name context = undefined

readMetaVar :: MetaVarF EvalContext -> Eval (Maybe Value)
readMetaVar (MkMeta _name _unique ref) = MkEval (liftIO (readIORef ref))

setMetaVar :: MetaVarF EvalContext -> Value -> Eval ()
setMetaVar (MkMeta _name _unique ref) value = MkEval (liftIO (writeIORef ref (Just value)))

freshSkolem :: (MonadUnique m) => Name -> m Skolem
freshSkolem name = do
    unique <- newUnique
    pure (MkSkolem name unique)

followMetas :: (HasContext context) => context -> Value -> Eval Value
followMetas (getContext -> context) value = case value of
    StuckMeta meta cont -> do
        readMetaVar meta >>= \case
            Nothing -> pure value
            Just replacement -> do
                replacement <- followMetas context replacement

                -- We do path compression.
                -- If a meta variable points to another substituted meta variable,
                -- we skip the indirection and bend the first one to point to the target directly.
                -- This means that further followMetas calls will only need to traverse one level of indirection
                -- rather than re-traversing the entire chain.
                -- Plus, this is extremely easy and fast to do so it's not like we're losing anything by doing path compression.
                setMetaVar meta replacement
                instantiateStuck replacement cont
    StuckSkolem skolem cont -> do
        case lookup skolem context.skolemBindings of
            Nothing -> pure value
            Just replacement -> do
                replacement <- followMetas context replacement

                -- Unfortunately we cannot do path compression on skolems since we don't actually have anything to mutate
                instantiateStuck replacement cont
    value -> pure value

{- | Instantiate a stuck value with something concrete. This will evaluate the stuck value's continuation
This assumes that the value is *NOT* a bound meta variable or skolem
-}
instantiateStuck :: Value -> Seq (StuckCont EvalContext) -> Eval Value
instantiateStuck value = \case
    Empty -> pure value
    (StuckApp argument :<| rest) -> do
        -- TODO: not sure about the lazies here :/
        lazyArgument <- lazyValueM argument
        result <- evalApplication value lazyArgument
        instantiateStuck result rest
    (StuckCase closureContext cases :<| rest) -> do
        result <- evalCase closureContext value cases
        instantiateStuck result rest

evalApplication :: Value -> LazyM Eval Value -> Eval Value
evalApplication funValue argValue = case funValue of
    ClosureV closure ->
        applyClosure closure argValue
    -- TODO: This should not need to force the value
    StuckMeta meta cont -> do
        argValue <- forceM argValue
        pure (StuckMeta meta (cont :|> StuckApp argValue))
    StuckSkolem skolem cont -> do
        argValue <- forceM argValue
        pure (StuckSkolem skolem (cont :|> StuckApp argValue))
    TypeConstructorApp name arguments -> do
        argValue <- forceM argValue
        pure $ TypeConstructorApp name (arguments :|> argValue)
    DataConstructorApp name arguments -> do
        argValue <- forceM argValue
        pure $ DataConstructorApp name (arguments :|> argValue)
    value -> error ("application of non-closure, -constructor or -variable during evaluation: " <> prettyPlain (showHeadConstructor value))

-- TODO: This needs to implement effect handlers. Not sure how to combine that with
-- partial evaluation
eval :: EvalContext -> CoreExpr -> Eval Value
eval context expr = withTrace
    Eval
    ( showHeadConstructor expr
        <+> lparen "{"
        <> intercalateMap ", " ident (Map.keys context.varValues)
        <> rparen "}"
    )
    $ case expr of
        CVar name -> case lookup name context.varValues of
            Nothing -> error ("variable not found during evaluation: " <> show name)
            Just value -> forceM value
        CApp funExpr argExpr -> do
            funValue <- eval context funExpr
            argValue <- lazyM (eval context argExpr)
            evalApplication funValue argValue
        CLambda name body -> pure $ ClosureV (MkClosure name body context)
        CCase expr cases -> do
            value <- eval context expr
            evalCase context value cases
        CTupleLiteral arguments -> do
            values <- traverse (eval context) arguments
            pure (TupleV values)
        CLiteral literal -> pure $ case literal of
            TypeLit -> Type
            IntTypeLit -> Int
            StringTypeLit -> String
            IntLit int -> IntV int
            StringLit text -> StringV text
        CLet name expr rest -> do
            value <- lazyM (eval context expr)
            eval (define name value context) rest
        CPrimop primop -> do pure (ClosureV (PrimopClosure primop []))
        CPi name type_ body -> do
            type_ <- eval context type_
            pure $ Pi name type_ (body, context)
        CForall name type_ body -> do
            type_ <- eval context type_
            pure $ Forall name type_ (body, context)
        CMeta (MkMeta name unique ref) ->
            readRef ref >>= \case
                Nothing -> pure (StuckMeta (MkMeta name unique ref) [])
                Just value -> pure value
        CTupleType arguments -> do
            values <- traverse (eval context) arguments
            pure (TupleType values)
        CQuote value -> pure value

evalCase :: EvalContext -> Value -> Vector (CorePattern Name, CoreExpr) -> Eval Value
evalCase context value cases = case value of
    StuckMeta meta cont -> pure $ StuckMeta meta (cont :|> StuckCase context cases)
    StuckSkolem skolem cont -> pure $ StuckSkolem skolem (cont :|> StuckCase context cases)
    value -> do
        -- TODO: This is kind of slow. We could generate a more efficient direct case based on the kind of pattern here
        matchingCase <- findMapM (\(pattern_, body) -> fmap (,body) <$> matchPattern value pattern_) cases
        case matchingCase of
            Nothing -> error "non-exhaustive patterns during eval"
            Just (contextTrans, body) ->
                eval (contextTrans context) body

matchPattern :: Value -> CorePattern Name -> Eval (Maybe (EvalContext -> EvalContext))
matchPattern value = \case
    CVarPat name -> do
        lazyValue <- lazyValueM value
        pure (Just (define name lazyValue))
    CWildcardPat -> pure (Just id)
    CIntPat expectedInt -> case value of
        IntV actualInt | expectedInt == actualInt -> pure $ Just id
        _ -> pure Nothing
    CStringPat expectedString -> case value of
        StringV actualString | expectedString == actualString -> pure $ Just id
        _ -> pure Nothing
    CTuplePat componentNames -> case value of
        TupleV values -> do
            assertM (length componentNames == length values)
            lazyValues <- traverse lazyValueM values
            pure (Just (compose (mzipWith define componentNames lazyValues)))
        _ -> pure Nothing
    CConstructorPat expectedName argumentNames -> case value of
        DataConstructorApp actualName argumentValues
            | expectedName == actualName -> do
                assertM (length argumentNames == length argumentValues)
                lazyValues <- traverse lazyValueM argumentValues
                pure (Just (compose (zipWith define (toList argumentNames) (toList lazyValues))))
        _ -> pure Nothing

applyClosure :: Closure -> LazyM Eval Value -> Eval Value
applyClosure (MkClosure name coreExpr context) argument =
    eval (define name argument context) coreExpr
applyClosure (PrimopClosure primop previousArgs) argument
    | length previousArgs + 1 < primopArity primop = do
        argumentValue <- forceM argument
        pure (ClosureV (PrimopClosure primop (previousArgs :|> argumentValue)))
    | otherwise = do
        argumentValue <- forceM argument
        case (primop, previousArgs :|> argumentValue) of
            (Debug, [_]) ->
                -- debugs are just ignored at compile time I guess?
                pure (TupleV [])
            (Add, [arg1, arg2]) ->
                pure $ case (arg1, arg2) of
                    (IntV x, IntV y) -> IntV (x + y)
                    (x, y) -> undefined
            (Subtract, [arg1, arg2]) ->
                undefined
            (Multiply, [arg1, arg2]) ->
                undefined
            (primop, args) -> error ("Invalid primop / argument combination: " <> show primop <> " (" <> prettyPlain (intercalateDoc ", " (fmap pretty args)) <> ")")


-- TODO: This happens to early. If meta variables are inserted later they will still be *values* so
-- error messages are still wrong (and still rely on unsafePerformIO) :/

{- | Fully quote a type, e.g. for error messages.
Note that this also follows lazy `Quote`s inside CoreExprs
-}
quote :: (HasContext context) => context -> Type -> Eval CoreExpr
quote context type_ =
    followMetas context type_ >>= \case
        IntV n -> pure $ CLiteral (IntLit n)
        StringV text -> pure $ CLiteral (StringLit text)
        ClosureV (MkClosure name body context) -> do
            parameterSkolem <- freshSkolem name
            parameterValue <- lazyValueM (StuckSkolem parameterSkolem [])

            let bodyContext = define name parameterValue context
            evaluatedBody <- eval bodyContext body

            CLambda name <$> quote bodyContext evaluatedBody
        ClosureV (PrimopClosure primop arguments) -> do
            quotedArguments <- traverse (quote context) arguments
            pure $ foldl' CApp (CPrimop primop) quotedArguments
        TupleV arguments -> do
            quotedArguments <- traverse (quote context) arguments
            pure $ CTupleLiteral quotedArguments
        DataConstructorApp constructorName arguments -> do
            quotedArguments <- traverse (quote context) arguments
            pure $ foldl' CApp (CVar constructorName) quotedArguments
        TypeConstructorApp constructorName arguments -> do
            quotedArguments <- traverse (quote context) arguments
            pure $ foldl' CApp (CVar constructorName) quotedArguments
        Type -> pure $ CLiteral TypeLit
        Int -> pure $ CLiteral IntTypeLit
        String -> pure $ CLiteral StringTypeLit
        TupleType arguments -> do
            quotedArguments <- traverse (quote context) arguments
            pure $ CTupleType quotedArguments
        Pi mname domain (codomainExpr, codomainEnv) -> do
            quotedDomain <- quote context domain
            codomain <- skolemizeClosure mname codomainExpr codomainEnv
            quotedCodomain <- quote context codomain
            pure $ CPi mname quotedDomain quotedCodomain
        Forall name domain (codomainExpr, codomainEnv) -> do
            quotedDomain <- quote context domain
            codomain <- skolemizeClosure (Just name) codomainExpr codomainEnv
            quotedCodomain <- quote context codomain
            pure $ CForall name quotedDomain quotedCodomain
        StuckSkolem (MkSkolem skolemName skolemUnique) cont -> do
            -- We use the skolem unique as the variable unique here.
            -- This technically loses provenance of the skolem but we don't use that anywhere
            -- so it should be fine.
            let skolemVar = CVar (Name.makeDirectlyUnchecked (Name.original skolemName) skolemUnique)

            quoteCont context skolemVar cont
        StuckMeta metaVar cont -> do
            quoteCont context (CMeta metaVar) cont

quoteCont :: (HasContext context) => context -> CoreExpr -> Seq (StuckCont EvalContext) -> Eval CoreExpr
quoteCont _context argument Empty = pure argument
quoteCont context functionExpr (StuckApp arg :<| rest) = do
    quotedArg <- quote context arg
    quoteCont context (CApp functionExpr quotedArg) rest
quoteCont context argument (StuckCase closedContext cases :<| rest) = do
    -- not entirely sure what to do here, we somehow need to quote cases using the context, but
    -- also cases is already an expression?
    undefined

skolemizeClosure :: Maybe Name -> CoreExpr -> EvalContext -> Eval Type
skolemizeClosure mname codomainCore codomainContext = do
    codomainContext <- case mname of
        Nothing -> pure codomainContext
        Just name -> do
            codomainSkolem <- freshSkolem name
            skolemValue <- lazyValueM (StuckSkolem codomainSkolem [])
            pure (define name skolemValue codomainContext)
    eval codomainContext codomainCore
