module Vega.Compilation.LIR.CoreToLIR where

import Effectful
import Relude hiding (State, get, modify, put, runState)

import Effectful.State.Static.Local (State, get, modify, put, runState)

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.LIR.Syntax qualified as LIR
import Vega.Effect.Trace (Trace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique)
import Vega.Panic (panic)
import Vega.Pretty (pretty)

type Compile es = (Trace :> es, NewUnique :> es, State CurrentDeclarationState :> es)

data CurrentDeclarationState = MkDeclarationState
    { blocks :: HashMap LIR.BlockDescriptor LIR.Block
    , joinPoints :: HashMap LocalCoreName LIR.BlockDescriptor
    , additionalDeclarations :: Seq LIR.Declaration
    , -- TOOD: preserve the order or something?
      locals :: HashMap LocalCoreName LIR.Layout
    }

initialDeclarationState :: CurrentDeclarationState
initialDeclarationState =
    MkDeclarationState
        { blocks = mempty
        , joinPoints = mempty
        , additionalDeclarations = []
        , locals = mempty
        }

compileDeclaration :: (Trace :> es, NewUnique :> es) => Core.Declaration -> Eff es (Seq LIR.Declaration)
compileDeclaration = \case
    Core.DefineFunction functionName parameters statements finalExpr -> do
        compileFunction (Core.Global functionName) parameters statements finalExpr

compileFunction :: (Trace :> es, NewUnique :> es) => CoreName -> Seq LocalCoreName -> Seq Core.Statement -> Core.Expr -> Eff es (Seq LIR.Declaration)
compileFunction functionName parameters statements returnExpr = do
    (initDescriptor, finalDeclarationState) <- runState initialDeclarationState $ do
        initialBlock <- newBlock []
        compileBody initialBlock statements returnExpr
        pure (initialBlock.descriptor)
    let declaration =
            LIR.DefineFunction
                { name = functionName
                , parameters
                , locals = finalDeclarationState.locals
                , blocks = finalDeclarationState.blocks
                , init = initDescriptor
                }
    pure $ [declaration] <> finalDeclarationState.additionalDeclarations

compileBody :: (Compile es) => BlockBuilder -> Seq Core.Statement -> Core.Expr -> Eff es ()
compileBody block statements returnExpr = case statements of
    Empty -> compileReturn block returnExpr
    Core.Let name expr :<| rest -> do
        block <- compileLet block name expr
        compileBody block rest returnExpr
    Core.LetJoin name parameters statements returnExpr :<| rest -> do
        joinPointBlock <- newBlock parameters
        compileBody joinPointBlock statements returnExpr
        addJoinPoint name joinPointBlock.descriptor
        compileBody block rest returnExpr

compileLet :: (Compile es) => BlockBuilder -> LocalCoreName -> Core.Expr -> Eff es BlockBuilder
compileLet block local = \case
    Core.Value value -> undefined
    Core.Application function arguments -> do
        (block, arguments) <- compileValues block arguments
        continuation <- newBlock []
        finish block undefined
        pure continuation
    Core.JumpJoin joinPoint _arguments -> do
        panic $ "JumpJoin for join point " <> pretty joinPoint <> " in non-tail position"
    Core.Lambda parameters statements returnExpr -> do
        undefined
    Core.ConstructorCase scrutinee cases -> do
        undefined

compileReturn :: (Compile es) => BlockBuilder -> Core.Expr -> Eff es ()
compileReturn block = \case
    Core.Value value -> do
        (block, value) <- compileValue block value
        finish block (LIR.Return value)
    Core.Application function arguments -> do
        (block, arguments) <- compileValues block arguments
        -- TODO: this may not actually be a direct call?
        finish block (LIR.TailCallDirect function arguments)
    Core.JumpJoin joinPoint arguments -> do
        (block, arguments) <- compileValues block arguments

        joinPointBlock <- joinPointBlockFor joinPoint
        finish block (LIR.Jump joinPointBlock arguments)
    Core.Lambda parameters statements returnExpr -> do
        undefined
    Core.ConstructorCase scrutinee cases ->
        undefined

compileValues :: (Compile es) => BlockBuilder -> Seq Core.Value -> Eff es (BlockBuilder, Seq LIR.Value)
compileValues = do
    undefined

compileValue :: (Compile es) => BlockBuilder -> Core.Value -> Eff es (BlockBuilder, LIR.Value)
compileValue block = \case
    Core.Var var -> pure (block, LIR.Var var)
    Core.Literal literal -> pure (block, LIR.Literal literal)
    Core.DataConstructorApplication name arguments -> do
        (block, arguments) <- compileValues block arguments
        undefined

addJoinPoint :: (Compile es) => LocalCoreName -> LIR.BlockDescriptor -> Eff es ()
addJoinPoint name blockDescriptor = do
    modify (\state -> state{joinPoints = HashMap.insert name blockDescriptor state.joinPoints})

joinPointBlockFor :: (Compile es) => LocalCoreName -> Eff es LIR.BlockDescriptor
joinPointBlockFor name = do
    MkDeclarationState{joinPoints} <- get
    case HashMap.lookup name joinPoints of
        Nothing -> panic $ "JumpJoin to join point without a block descriptor: " <> pretty name
        Just descriptor -> pure descriptor

newLocal :: (Compile es) => Eff es LocalCoreName
newLocal = do
    unique <- newUnique
    pure (Core.Generated unique)

data BlockBuilder = MkBlockBuilder
    { descriptor :: LIR.BlockDescriptor
    , arguments :: Seq LocalCoreName
    , instructions :: Seq LIR.Instruction
    }

newBlock :: (Compile es) => Seq LocalCoreName -> Eff es BlockBuilder
newBlock arguments = do
    descriptor <- LIR.MkBlockDescriptor <$> newUnique
    pure MkBlockBuilder{descriptor, arguments, instructions = []}

-- The f only exists to allow shadowing the builder.
-- If you need this in a pure context, just instantiate it with Identity
addInstruction :: (Applicative f) => BlockBuilder -> LIR.Instruction -> f BlockBuilder
addInstruction builder newInstruction = pure $ builder{instructions = builder.instructions <> [newInstruction]}

finish :: (Compile es) => BlockBuilder -> LIR.Terminator -> Eff es ()
finish (MkBlockBuilder{descriptor, arguments, instructions}) terminator = do
    let finishedBlock = LIR.MkBlock{arguments, instructions, terminator}
    modify (\state -> state{blocks = HashMap.insert descriptor finishedBlock state.blocks})
