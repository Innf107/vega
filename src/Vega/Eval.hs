module Vega.Eval (
    Eval,
    runEval,
    EvalContext,
    HasContext (..),
    emptyEvalContext,
    define,
    defineSkolem,
    followSkolems,
    Value,
    CoreDeclaration,
    CoreExpr,
    eval,
    applyClosure,
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
import Vega.Pretty
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

runEval :: (?traceAction :: TraceAction IO) => Eval a -> IO a
runEval (MkEval io) = runReaderT io ?traceAction

type Value = ValueF EvalContext

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
            lazyValue <- lazyValueM (StuckValue (SkolemApp skolem []))
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

followSkolems :: (HasContext context) => context -> Value -> Eval Value
followSkolems (getContext -> context) = \case
    StuckValue stuck -> followStuckValues context stuck
    value -> pure value

-- TODO: This really needs to follow meta variables as well
followStuckValues :: (HasContext context) => context -> StuckValue EvalContext -> Eval Value
followStuckValues (getContext -> context) = \case
    (SkolemApp skolem [])
        | Just value <- lookup skolem context.skolemBindings ->
            followSkolems context value
    (SkolemApp skolem args)
        | Just funValue <- lookup skolem context.skolemBindings -> do
            let applyOne funValue argValue = do
                    lazyArgValue <- lazyValueM argValue
                    evalApplication context funValue lazyArgValue
            foldlM applyOne funValue args
    stuck@SkolemApp{} -> pure (StuckValue stuck)
    -- TODO: This should all be merged with followMetas
    stuck@MetaApp{} -> pure (StuckValue stuck)
    StuckCase stuckValue closureContext cases ->
        followStuckValues context stuckValue >>= \case
            StuckValue stuck -> pure $ StuckValue (StuckCase stuck closureContext cases)
            value -> evalCase context value closureContext cases

evalApplication :: EvalContext -> Value -> LazyM Eval Value -> Eval Value
evalApplication context funValue argValue = case funValue of
    ClosureV closure ->
        applyClosure closure argValue
    StuckValue (SkolemApp skolem arguments) -> do
        -- TODO: Do we really need to force the value here? :/
        argValue <- forceM argValue
        pure $ StuckValue (SkolemApp skolem (arguments :|> argValue))
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
            evalApplication context funValue argValue
        CLambda name body -> pure $ ClosureV (MkClosure name body context)
        CCase expr cases -> do
            value <- eval context expr
            evalCase context value context cases
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
                Nothing -> pure (StuckValue (MetaApp (MkMeta name unique ref) []))
                Just value -> pure value
        CTupleType arguments -> do
            values <- traverse (eval context) arguments
            pure (TupleType values)
        CQuote value -> pure value

-- TODO: This should follow metas
evalCase :: EvalContext -> Value -> EvalContext -> Vector (CorePattern Name, CoreExpr) -> Eval Value
evalCase context value closureContext cases =
    followSkolems context value >>= \case
        StuckValue stuck -> pure $ StuckValue (StuckCase stuck closureContext cases)
        value -> do
            -- TODO: This is kind of slow. We could generate a more efficient direct case based on the kind of pattern here
            matchingCase <- findMapM (\(pattern_, body) -> fmap (,body) <$> matchPattern value pattern_) cases
            case matchingCase of
                Nothing -> error "non-exhaustive patterns during eval"
                Just (contextTrans, body) ->
                    eval (contextTrans closureContext) body

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
