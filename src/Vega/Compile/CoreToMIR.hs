module Vega.Compile.CoreToMIR (coreToMIR) where

import Vega.Prelude

import Data.Set qualified as Set
import Vega.Compile.MIR as MIR
import Vega.Eval qualified as Eval
import Vega.Monad.Unique (MonadUnique (freshName))
import Vega.Syntax as Core
import Vega.Util (viaList, pattern Nil, pattern (:::))

newtype Compile a = MkCompile (IO a)
    deriving newtype (Functor, Applicative, Monad, MonadUnique)

runCompile :: Compile a -> IO a
runCompile (MkCompile io) = io

coreToMIR :: Vector (Eval.CoreDeclaration) -> IO (Vector MIR.Declaration)
coreToMIR = runCompile . traverse compileDeclaration

compileDeclaration :: Eval.CoreDeclaration -> Compile MIR.Declaration
compileDeclaration (CDefineVar name body) = MIR.DefineVar name <$> compileValue body
compileDeclaration (CDefineGADT _ _) = undefined

-- Values are, well, *evaluated* already so they don't contain any redexes and we can compile them to
-- pure MIR expressions directly.
compileValue :: Eval.Value -> Compile MIR.Expr
compileValue (ClosureV closure) = compileClosure closure
compileValue (IntV x) = pure (MIR.Literal (MIR.IntLit x))
compileValue (StringV x) = pure (MIR.Literal (MIR.StringLit x))
compileValue (TupleV components) = do
    componentExprs <- traverse compileValue components
    pure (MIR.TupleLiteral componentExprs)
compileValue (DataConstructorApp name arguments) = do
    argumentExprs <- traverse compileValue arguments
    pure (MIR.DataConstructor name (viaList argumentExprs))
compileValue (StuckSkolem skolem stuckCont) = undefined
-- TODO: We should really call followMetas before matching on anything here
compileValue (StuckMeta meta stuckCont) = undefined
-- MIR is untyped (for now) so we just translate compile-time-only types to unit
compileValue Type = pure unit
compileValue Int = pure unit
compileValue String = pure unit
compileValue TypeConstructorApp{} = pure unit
compileValue TupleType{} = pure unit
compileValue Pi{} = pure unit
compileValue Forall{} = pure unit

compileClosure :: ClosureF Eval.EvalContext -> Compile MIR.Expr
compileClosure (MkClosure name body context) = do
    contName <- freshName "k"
    statement <- compileExpr context body (ContVar contName)

    -- TODO: This desugars into separate lambdas but we should really try to group them up already
    pure (MIR.Lambda [name] contName statement)
compileClosure (PrimopClosure primop arguments) = do
    argumentExprs <- traverse compileValue arguments
    pure (MIR.PrimopApp primop argumentExprs)

compileExpr :: Eval.EvalContext -> Eval.CoreExpr -> Cont -> Compile MIR.Statement
compileExpr context expr cont = case expr of
    CVar name -> case Eval.lookupVar name context of
        Nothing -> pure $ continue cont (MIR.Var name)
        Just value -> do
            expr <- compileValue value
            pure $ continue cont expr
    CApp funExpr argExpr -> do
        -- TODO: This should probably try not to build up nested applications
        compileExpr context funExpr =<< contLambda \funVar ->
            compileExpr context argExpr =<< contLambda \argVar ->
                pure $ MIR.App (MIR.Var funVar) [MIR.Var argVar] cont
    _ -> undefined

continue :: Cont -> MIR.Expr -> MIR.Statement
continue (ContVar name) expr = MIR.Continue name expr
continue (ContLambda name statement) expr = MIR.Let name expr statement

contLambda :: (Name -> Compile MIR.Statement) -> Compile MIR.Cont
contLambda withCont = do
    argument <- freshName "x"
    statement <- withCont argument
    pure (MIR.ContLambda argument statement)

{- | Utility definition to make returning unit a little more readable.
This is useful since we return unit all the time when erasing types.
-}
unit :: MIR.Expr
unit = MIR.Literal MIR.UnitLit
