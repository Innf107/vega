module Vega.Eval (
    EvalContext,
    emptyEvalContext,
    define,
    Value,
    eval,
    applyClosure,
) where

import Vega.Prelude
import Vega.Syntax

type Value = ValueF EvalContext
type Closure = ClosureF EvalContext

data EvalContext = MkEvalContext
    { varValues :: Map Name Value
    }

emptyEvalContext :: EvalContext
emptyEvalContext =
    MkEvalContext
        { varValues = mempty
        }

define :: Name -> Value -> EvalContext -> EvalContext
define name value context = context{varValues = insert name value context.varValues}

-- TODO: This needs to implement effect handlers. Not sure how to combine that with
-- partial evaluation
eval :: EvalContext -> CoreExpr -> Value
eval context = \case
    CVar name -> case lookup name context.varValues of
        Nothing -> error ("variable not found during evaluation: " <> show name)
        Just value -> value
    CApp funExpr argExpr -> do
        let funValue = eval context funExpr
        let argValue = eval context argExpr
        case funValue of
            ClosureV closure ->
                applyClosure closure argValue
            SkolemApp skolem arguments ->
                SkolemApp skolem (arguments :|> argValue)
            _ -> error ("application of non-closure or variable during evaluation")
    CLambda name body -> ClosureV (MkClosure name body context)
    CCase _expr _cases -> undefined
    CLiteral literal -> case literal of
        TypeLit -> Type
        IntTypeLit -> Int
        StringTypeLit -> String
        IntLit int -> IntV int
        StringLit text -> StringV text
    CLet name expr rest ->
        let ~value = eval context expr
         in eval (define name value context) rest
    CPi name type_ body -> Pi name (eval context type_) (body, context)
    CForall name type_ body -> Forall name (eval context type_) (body, context)

applyClosure :: Closure -> Value -> Value
applyClosure (MkClosure name coreExpr context) argument =
    eval (define name argument context) coreExpr
