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

import Vega.LazyM
import Vega.MonadRef

newtype Eval a = MkEval (IO a) deriving newtype (Functor, Applicative, Monad, MonadRef)

runEval :: Eval a -> IO a
runEval (MkEval io) = io

type Value = ValueF EvalContext
type CoreDeclaration = CoreDeclarationF EvalContext
type CoreExpr = CoreExprF EvalContext
type Closure = ClosureF EvalContext

data EvalContext = MkEvalContext
    { varValues :: Map Name (LazyM Eval Value)
    }

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
eval context = \case
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
            _ -> error ("application of non-closure or variable during evaluation")
    CLambda name body -> pure $ ClosureV (MkClosure name body context)
    CCase _expr _cases -> undefined
    CLiteral literal -> pure $ case literal of
        TypeLit -> Type
        IntTypeLit -> Int
        StringTypeLit -> String
        IntLit int -> IntV int
        StringLit text -> StringV text
    CLet name expr rest -> do
        value <- lazyM (eval context expr)
        eval (define name value context) rest
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

applyClosure :: Closure -> LazyM Eval Value -> Eval Value
applyClosure (MkClosure name coreExpr context) argument =
    eval (define name argument context) coreExpr
