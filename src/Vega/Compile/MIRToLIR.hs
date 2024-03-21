module Vega.Compile.MIRToLIR (mirToLIR) where

import Vega.Prelude

import Vega.Compile.LIR as LIR
import Vega.Compile.MIR as MIR
import Vega.Monad.Unique
import Vega.Name
import Vega.Util (viaList)

newtype Compile a = MkCompile (StateT CompileState IO a)
    deriving newtype (Functor, Applicative, Monad)

instance MonadUnique Compile where
    newUnique = MkCompile (lift newUnique)
    freshName name = MkCompile (lift (freshName name))

unCompile :: Compile a -> StateT CompileState IO a
unCompile (MkCompile stateT) = stateT

data CompileState = MkCompileState
    { compiledBlocks :: Map Name (LIR.Block)
    , compiledGlobals :: Map Name (Seq LIR.Instruction)
    }

insertBlock :: Name -> LIR.Block -> Compile ()
insertBlock name block =
    MkCompile $ modify (\compState -> compState{compiledBlocks = insert name block compState.compiledBlocks})

mirToLIR :: Vector MIR.Declaration -> IO LIR.Program
mirToLIR decls = do
    finalState <- flip execStateT (MkCompileState{compiledBlocks = mempty, compiledGlobals = mempty}) $ unCompile do
        traverse_ compileDeclaration decls
    pure
        $ MkProgram
            { blocks = finalState.compiledBlocks
            , globalsWithInitializers = finalState.compiledGlobals
            }

-- TODO: This compiles top-level declarations into functions that return their values. should it really do that? ugghhh
-- I guess ideally we would require top-level bindings to be pure, evaluate this at compile time and then compile based on
-- the resulting value? That would probably need to happen in Core->MIR though
compileDeclaration :: MIR.Declaration -> Compile ()
compileDeclaration (DefineVar name body) = do
    result <- freshName "r"
    instructions <- compilePureBinding name body
    insertBlock name (MkBlock{instructions, terminator = Return (LIR.Var result), arguments = []})

compilePureBinding :: Name -> MIR.Expr -> Compile (Seq Instruction)
compilePureBinding target = \case
    MIR.Var source -> pure [LIR.Mov target (LIR.Var source)]
    expr@(PureApp{}) -> do
        -- TODO: use the statically known arity here if possible
        let (funExpr, argExprs) = collectPureAppSpine expr

        (funSource, funInstructions) <- compileExprToSource funExpr
        (argumentSources, argumentInstructions) <- second fold . unzip <$> traverse compileExprToSource argExprs
        -- Start a new block here... somehow?
        undefined -- (CallIndirect funSource (viaList argumentSources), funInstructions <> argumentInstructions)
    expr@PureLambda{} -> do
        blockName <- freshName "lambda"
        let (parameterNames, body) = collectPureLambdaSpine expr
        lambdaReturn <- freshName "lr"
        instructions <- compilePureBinding lambdaReturn body
        insertBlock blockName (MkBlock{instructions, terminator = Return (LIR.Var lambdaReturn), arguments = parameterNames})
        undefined
    -- TODO: figure out integer sizes i guess
    Literal (IntLit int) -> pure [LIR.Mov target (LIR.ImmediateInt (fromInteger int))]
    -- This doesn't actually do anything interesting but we still need to override garbage data so the garbage collector isn't confused
    -- and holds on to data that isn't reachable through anything else anymore.
    Literal UnitLit -> pure [LIR.Mov target (LIR.ImmediateInt 0)]
    Let varName expr body -> do
        varInstructions <- compilePureBinding varName expr
        restInstructions <- compilePureBinding varName body
        pure (varInstructions <> restInstructions)

compileExprToSource :: MIR.Expr -> Compile (LIR.Source, Seq Instruction)
compileExprToSource (MIR.Var name) = pure (LIR.Var name, [])
compileExprToSource (MIR.Literal (IntLit int)) = pure (LIR.ImmediateInt (fromInteger int), [])
compileExprToSource expr = do
    name <- freshName "t"
    instructions <- compilePureBinding name expr
    pure (LIR.Var name, instructions)

collectPureAppSpine :: MIR.Expr -> (MIR.Expr, Seq MIR.Expr)
collectPureAppSpine (PureApp funExpr argExpr) = do
    let (finalFunExpr, argExprs) = collectPureAppSpine funExpr
    (finalFunExpr, argExprs :|> argExpr)
collectPureAppSpine expr = (expr, [])

collectPureLambdaSpine :: MIR.Expr -> (Seq Name, MIR.Expr)
collectPureLambdaSpine (PureLambda name expr) = do
    let (paramNames, body) = collectPureLambdaSpine expr
    (name :<| paramNames, body)
collectPureLambdaSpine expr = ([], expr)
