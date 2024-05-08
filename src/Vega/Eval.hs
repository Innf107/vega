module Vega.Eval (
    Eval,
    runEval,
    EvalContext,
    emptyEvalContext,
    define,
    Value,
    CoreDeclaration,
    CoreExpr,
    eval,
    applyClosure,
) where

import Vega.Prelude
import Vega.Syntax

import Vega.Primop

import Vega.Debug (showHeadConstructor)
import Vega.LazyM
import Vega.Monad.Ref
import Vega.Monad.Unique
import Vega.Name qualified as Name
import Vega.Pretty

newtype Eval a = MkEval (IO a) deriving newtype (Functor, Applicative, Monad, MonadRef)

instance MonadUnique Eval where
    freshName text = MkEval $ freshName text
    newUnique = MkEval newUnique

runEval :: Eval a -> IO a
runEval (MkEval io) = io

type Value = ValueF EvalContext

type CoreDeclaration = CoreDeclarationF EvalContext

type CoreExpr = CoreExprF EvalContext

type Closure = ClosureF EvalContext

data EvalContext = MkEvalContext
    { varValues :: Map Name (LazyM Eval Value)
    }

instance ContextFromEmpty EvalContext where
    emptyContext = emptyEvalContext

instance EvalClosureForPrinting EvalContext where
    applyNullaryClosurePrint context expr = runEval $ eval context expr
    applyClosureForPrinting context expr name = runEval do
        let skolem = MkSkolem name (Name.unique name)
        lazyValue <- lazyValueM (SkolemApp skolem [])
        applyClosure (MkClosure name expr context) lazyValue

emptyEvalContext :: EvalContext
emptyEvalContext =
    MkEvalContext
        { varValues = mempty
        }

define :: Name -> LazyM Eval Value -> EvalContext -> EvalContext
define name value context = context{varValues = insert name value context.varValues}

-- TODO: This needs to implement effect handlers. Not sure how to combine that with
-- partial evaluation
eval :: EvalContext -> CoreExpr -> Eval Value
eval context expr = case expr of
    CVar name -> case lookup name context.varValues of
        Nothing -> error ("variable not found during evaluation: " <> show name)
        Just value -> forceM value
    CApp funExpr argExpr -> do
        funValue <- eval context funExpr
        argValue <- lazyM (eval context argExpr)
        case funValue of
            ClosureV closure ->
                applyClosure closure argValue
            SkolemApp skolem arguments -> do
                -- TODO: Do we really need to force the value here? :/
                argValue <- forceM argValue
                pure $ SkolemApp skolem (arguments :|> argValue)
            TypeConstructorApp name arguments -> do
                argValue <- forceM argValue
                pure $ TypeConstructorApp name (arguments :|> argValue)
            DataConstructorApp name arguments -> do
                argValue <- forceM argValue
                pure $ DataConstructorApp name (arguments :|> argValue)
            value -> error ("application of non-closure, -constructor or -variable during evaluation: " <> prettyPlain (showHeadConstructor value))
    CLambda name body -> pure $ ClosureV (MkClosure name body context)
    CCase _expr _cases -> undefined
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
            Nothing -> pure (MetaApp (MkMeta name unique ref) [])
            Just value -> pure value
    CTupleType arguments -> do
        values <- traverse (eval context) arguments
        pure (TupleType values)
    CQuote value -> pure value

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
