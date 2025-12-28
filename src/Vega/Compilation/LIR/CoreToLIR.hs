module Vega.Compilation.LIR.CoreToLIR (compileDeclaration) where

import Effectful
import Relude hiding (State, get, modify, put, runState)

import Effectful.State.Static.Local (State, get, modify, put, runState)

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Traversable (for)
import Data.Vector.Generic qualified as Vector
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.LIR.Layout (Layout, generateLayout)
import Vega.Compilation.LIR.Layout qualified as Layout
import Vega.Compilation.LIR.Syntax qualified as LIR
import Vega.Effect.Trace (Trace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique)
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Util (mapAccumLM, forIndexed_, forFoldLM, indexed)
import Data.Foldable (foldrM)
import qualified Vega.Syntax as Vega
import Vega.Effect.GraphPersistence
import qualified Vega.Effect.GraphPersistence as GraphPersistence

type Compile es = (GraphPersistence :> es, Trace :> es, NewUnique :> es, State CurrentDeclarationState :> es)

data CurrentDeclarationState = MkDeclarationState
    { blocks :: HashMap LIR.BlockDescriptor LIR.Block
    , joinPoints :: HashMap LocalCoreName LIR.BlockDescriptor
    , additionalDeclarations :: Seq LIR.Declaration
    , -- TOOD: preserve the order or something?
      locals :: HashMap LocalCoreName LIR.Variable
    , layouts :: Seq Layout
    }

initialDeclarationState :: CurrentDeclarationState
initialDeclarationState =
    MkDeclarationState
        { blocks = mempty
        , joinPoints = mempty
        , additionalDeclarations = []
        , locals = mempty
        , layouts = mempty
        }

registerVariable :: (Compile es) => LocalCoreName -> LIR.Variable -> Eff es ()
registerVariable local variable = do
    modify (\state -> state{locals = HashMap.insert local variable state.locals})

registerAdditionalDeclarations :: (Compile es) => Seq LIR.Declaration -> Eff es ()
registerAdditionalDeclarations declarations = modify (\state -> state{additionalDeclarations = state.additionalDeclarations <> declarations})

compileDeclaration :: (GraphPersistence :> es, Trace :> es, NewUnique :> es) => Core.Declaration -> Eff es (Seq LIR.Declaration)
compileDeclaration = \case
    Core.DefineFunction{name, representationParameters = _, parameters, returnRepresentation, statements, result} -> do
        compileFunction (Core.Global name) parameters returnRepresentation statements result

compileFunction ::
    (GraphPersistence :> es, Trace :> es, NewUnique :> es) =>
    CoreName ->
    Seq (LocalCoreName, Core.Representation) ->
    Core.Representation ->
    Seq Core.Statement ->
    Core.Expr ->
    Eff es (Seq LIR.Declaration)
compileFunction functionName parameters returnRepresentation statements returnExpr = do
    (initDescriptor, finalDeclarationState) <- runState initialDeclarationState $ do
        initialBlock <- newBlock []
        compileBody initialBlock statements returnExpr
        pure (initialBlock.descriptor)
    let declaration =
            LIR.DefineFunction
                { name = functionName
                , parameters = undefined
                , layouts = finalDeclarationState.layouts
                , blocks = finalDeclarationState.blocks
                , init = initDescriptor
                }
    pure $ [declaration] <> finalDeclarationState.additionalDeclarations

compileBody :: (Compile es) => BlockBuilder -> Seq Core.Statement -> Core.Expr -> Eff es ()
compileBody block statements returnExpr = case statements of
    Empty -> compileReturn block returnExpr
    Core.Let name representation expr :<| rest -> do
        var <- newVar (generateLayout representation)
        registerVariable name var
        block <- compileLet block var expr
        compileBody block rest returnExpr
    Core.LetJoin name parameters statements returnExpr :<| rest -> do
        parameterVariables <- for parameters \(parameter, _representation) -> do
            variable <- newVar undefined
            registerVariable parameter variable
            pure variable
        joinPointBlock <- newBlock parameterVariables
        compileBody joinPointBlock statements returnExpr
        addJoinPoint name joinPointBlock.descriptor
        compileBody block rest returnExpr
    Core.LetFunction{} :<| rest -> undefined

compileLet :: (Compile es) => BlockBuilder -> LIR.Variable -> Core.Expr -> Eff es BlockBuilder
compileLet block local = \case
    Core.Value value -> undefined
    Core.Application function arguments -> do
        (block, arguments) <- compileValues block arguments
        continuation <- newBlock []
        -- TODO: distinguish between direct and indirect calls
        finish block (LIR.CallDirect local function arguments continuation.descriptor)
        pure continuation
    Core.JumpJoin joinPoint _arguments -> do
        panic $ "JumpJoin for join point " <> pretty joinPoint <> " in non-tail position"
    Core.Lambda parameters statements returnExpr -> do
        let returnRepresentation = undefined returnExpr
        compileLambda block local parameters returnRepresentation statements returnExpr
    Core.TupleAccess tupleValue index -> do
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
    Core.TupleAccess tupleValue index -> do
        undefined
    Core.ConstructorCase scrutinee cases ->
        undefined
    Core.Lambda parameters statements returnExpr -> do
        lambdaName <- undefined
        let returnRepresentation = undefined returnExpr
        lambdaDeclarations <- compileFunction lambdaName parameters returnRepresentation statements returnExpr
        registerAdditionalDeclarations lambdaDeclarations
        let value = undefined
        finish block (LIR.Return value)

compileValues :: (Compile es) => BlockBuilder -> Seq Core.Value -> Eff es (BlockBuilder, Seq LIR.Variable)
compileValues block values = mapAccumLM compileValue block values

compileValue :: (Compile es) => BlockBuilder -> Core.Value -> Eff es (BlockBuilder, LIR.Variable)
compileValue block = \case
    Core.Var var -> case var of
        Core.Local name -> undefined
        Core.Global name -> pure (block, undefined)
    Core.Literal literal -> do
        layout <- undefined literal
        variable <- newVar layout
        undefined
    Core.DataConstructorApplication constructor arguments representation -> do
        (block, arguments) <- compileValues block arguments

        -- TODO: add the tag for sum constructors

        let layout = generateLayout representation

        result <- newVar layout
        block <- addInstruction block $ LIR.AllocA result layout
        
        block <- forFoldLM (indexed arguments) block \block (index, argument) -> do
            (block, target) <- pointerToPath undefined undefined undefined undefined
            addInstruction block $ LIR.Memcpy target argument undefined
            
        pure (block, result)

compileLambda :: (Compile es) => BlockBuilder -> LIR.Variable -> Seq (LocalCoreName, Core.Representation) -> Core.Representation -> Seq Core.Statement -> Core.Expr -> Eff es BlockBuilder
compileLambda block local parameters returnRepresentation statements returnExpr = do
    lambdaName <- undefined

    lambdaDeclarations <- compileFunction lambdaName parameters returnRepresentation statements returnExpr
    registerAdditionalDeclarations lambdaDeclarations
    -- TODO: do this properly with the right layout
    let locals = undefined
    addInstruction block (LIR.AllocateClosure local lambdaName locals)
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

pointerToPath :: (HasCallStack, Compile es) => LIR.Variable -> Layout -> Layout.Path -> BlockBuilder -> Eff es (BlockBuilder, LIR.Variable)
pointerToPath pointer layout path block = go block 0 path
  where
    go block offset = \case
        Empty -> do
            result <- newVar layout
            block <- addInstruction block (LIR.GetElementPointer{result, pointer, arrayOffset = 0, internalOffset = 0, resultLayout = layout})
            pure (block, result)
        (Layout.ProductField index :<| rest) -> case layout.contents of
            Layout.ProductLayout{offsets} -> do
                go block (offset + (offsets Vector.! index)) rest
            _ -> panic $ "product field accessed on non-product layout"
        (Layout.SumConstructor index :<| rest) -> case layout.contents of
            Layout.SumLayout{constructors} -> do
                undefined
            _ -> panic $ "sum constructor accessed on non-sum layout"

newVar :: (Compile es) => Layout -> Eff es LIR.Variable
newVar layout = do
    state <- get
    let variable = LIR.MkVariable (length state.layouts)
    put (state{layouts = state.layouts <> [layout]})
    pure variable

data BlockBuilder = MkBlockBuilder
    { descriptor :: LIR.BlockDescriptor
    , arguments :: Seq LIR.Variable
    , instructions :: Seq LIR.Instruction
    }

newBlock :: (Compile es) => Seq LIR.Variable -> Eff es BlockBuilder
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
