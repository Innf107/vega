module Vega.Compile.CoreToMIR (coreToMIR) where

import Vega.Prelude

import Vega.Compile.MIR as MIR
import Vega.Eval qualified as Eval
import Vega.Syntax as Core

newtype Compile a = MkCompile (IO a)
    deriving newtype (Functor, Applicative, Monad)

runCompile :: Compile a -> IO a
runCompile (MkCompile io) = io

coreToMIR :: Vector (Eval.CoreDeclaration) -> IO (Vector MIR.Declaration)
coreToMIR = runCompile . traverse compileDeclaration

compileDeclaration :: Eval.CoreDeclaration -> Compile MIR.Declaration
compileDeclaration (CDefineVar name body) = MIR.DefineVar name <$> compilePureExpr body
compileDeclaration CDefineGADT = undefined

-- TODO: this needs to keep track of effects from the core and selectively
-- transform (possibly) *effectful* expressions into CPS/statement forms
compilePureExpr :: Eval.CoreExpr -> Compile MIR.Expr
compilePureExpr = \case
    CVar name -> pure $ MIR.Var name
    -- For now, all expressions are pure.
    -- This is *not* going to be the case once we introduce effects though!
    CApp expr1 expr2 -> do
        mirExpr1 <- compilePureExpr expr1
        mirExpr2 <- compilePureExpr expr2
        pure $ MIR.PureApp mirExpr1 mirExpr2
    CLambda name body -> do
        mirBody <- compilePureExpr body
        pure $ MIR.PureLambda name mirBody
    CCase{} -> undefined
    CLiteral literal -> pure $ MIR.Literal $ case literal of
        TypeLit -> MIR.UnitLit
        IntTypeLit -> MIR.UnitLit
        StringTypeLit -> MIR.UnitLit
        Core.IntLit int -> MIR.IntLit int
        Core.StringLit str -> undefined
    CTupleLiteral exprs -> undefined
    CLet name expr body -> do
        mirExpr <- compilePureExpr expr
        mirBody <- compilePureExpr body
        pure $ MIR.Let name mirExpr mirBody
    _ -> undefined