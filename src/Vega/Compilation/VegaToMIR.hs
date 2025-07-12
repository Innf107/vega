module Vega.Compilation.VegaToMIR where

import Relude
import Relude.Extra

import Vega.Compilation.MIR as MIR
import Vega.Syntax as Vega

import Data.Sequence qualified as Seq
import Effectful
import Vega.Util qualified as Util

type Compile es = () :: Constraint

newtype CompileEnv = CompileEnv
    { variableLocals :: HashMap LocalName Local
    }

variableLocal :: (HasCallStack) => LocalName -> CompileEnv -> Local
variableLocal name env = case lookup name env.variableLocals of
    Nothing -> error $ "Local variable not found during compilation: " <> show name
    Just local -> local

compileDeclaration :: (Compile es) => Vega.Declaration Typed -> MIR.Program -> Eff es MIR.Program
compileDeclaration declaration program = case declaration.syntax of
    DefineVariantType{} -> undefined
    DefineFunction{typeSignature, parameters, body} -> do
        undefined

freshLocal :: (Compile es) => Eff es Local
freshLocal = undefined

compileExpr :: CompileEnv -> Vega.Expr Typed -> Eff es (MIR.Expr -> MIR.Expr, MIR.Expr)
compileExpr env = \case
    Vega.Var _ (Vega.Global name) -> undefined
    Vega.Var _ (Vega.Local name) -> pure (id, MIR.Var (variableLocal name env))
    Vega.DataConstructor{} -> undefined
    Vega.Application{functionExpr, arguments} -> do
        (funBindings, functionLocal) <- toLocal env functionExpr
        (argBindings, argLocals) <- Seq.unzip <$> traverse (toLocal env) arguments
        pure (funBindings . Util.compose argBindings, MIR.Application functionLocal argLocals)
    Vega.PartialApplication{} -> undefined
    Vega.VisibleTypeApplication{} -> undefined
    Vega.Lambda loc typeParameters parameters result -> do
        undefined
    Vega.StringLiteral _ text -> do
        pure (id, MIR.Literal (MIR.StringLiteral text))
    Vega.IntLiteral _ text -> do
        pure (id, MIR.Literal (MIR.IntLiteral text))
    Vega.DoubleLiteral _ text -> do
        pure (id, MIR.Literal (MIR.DoubleLiteral text))
    Vega.TupleLiteral{} -> undefined
    Vega.BinaryOperator{} -> undefined
    Vega.If{condition, thenBranch, elseBranch} -> do
        conditionLocal <- toLocal env condition
        undefined
    Vega.SequenceBlock{} -> undefined
    Vega.Match{} -> undefined

-- TODO: this function return thing is cute but seems kind of slow (possibly quadratic in really bad cases?)
toLocal :: (Compile es) => CompileEnv -> Vega.Expr Typed -> Eff es (MIR.Expr -> MIR.Expr, Local)
toLocal env = \case
    Vega.Var _ (Vega.Global name) -> undefined
    Vega.Var _ (Vega.Local name) -> pure (id, variableLocal name env)
    Vega.DataConstructor{} -> undefined
    expr -> do
        (bindings, mirExpr) <- compileExpr env expr
        result <- freshLocal
        pure (bindings . MIR.Let result mirExpr, result)
