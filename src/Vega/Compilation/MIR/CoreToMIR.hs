module Vega.Compilation.MIR.CoreToMIR (compileDeclaration) where

import Effectful
import Relude hiding (State, get, modify, put, runState)

import Effectful.State.Static.Local (State, get, modify, put, runState)

import Data.Foldable (foldrM)
import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Traversable (for)
import Data.Vector.Generic qualified as Vector
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName, Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.MIR.Syntax (Phis (..))
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Effect.GraphPersistence
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Effect.Trace (Trace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique)
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Syntax qualified as Vega
import Vega.Util (assert, forFoldLM, forIndexed_, indexed, mapAccumLM)

type Compile es = (GraphPersistence :> es, Trace :> es, NewUnique :> es, State CurrentDeclarationState :> es)

data CurrentDeclarationState = MkDeclarationState
    { blocks :: HashMap MIR.BlockDescriptor MIR.Block
    , joinPoints :: HashMap LocalCoreName MIR.BlockDescriptor
    , additionalDeclarations :: Seq MIR.Declaration
    , -- TOOD: preserve the order or something?
      locals :: HashMap LocalCoreName (MIR.Variable, Representation)
    , varCount :: Int
    }

initialDeclarationState :: CurrentDeclarationState
initialDeclarationState =
    MkDeclarationState
        { blocks = mempty
        , joinPoints = mempty
        , additionalDeclarations = []
        , locals = mempty
        , varCount = 0
        }

registerVariable :: (Compile es) => LocalCoreName -> MIR.Variable -> Representation -> Eff es ()
registerVariable local variable representation = do
    modify (\state -> state{locals = HashMap.insert local (variable, representation) state.locals})

registerAdditionalDeclarations :: (Compile es) => Seq MIR.Declaration -> Eff es ()
registerAdditionalDeclarations declarations = modify (\state -> state{additionalDeclarations = state.additionalDeclarations <> declarations})

compileDeclaration :: (GraphPersistence :> es, Trace :> es, NewUnique :> es) => Core.Declaration -> Eff es (Seq MIR.Declaration)
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
    Eff es (Seq MIR.Declaration)
compileFunction functionName parameters returnRepresentation statements returnExpr = do
    (initDescriptor, finalDeclarationState) <- runState initialDeclarationState $ do
        initialBlock <- newBlock (MkPhys mempty)
        compileBody initialBlock statements returnExpr
        pure (initialBlock.descriptor)
    let declaration =
            MIR.DefineFunction
                { name = functionName
                , parameters
                , blocks = finalDeclarationState.blocks
                , init = initDescriptor
                }
    pure $ [declaration] <> finalDeclarationState.additionalDeclarations

compileBody :: (Compile es) => BlockBuilder -> Seq Core.Statement -> Core.Expr -> Eff es ()
compileBody block statements returnExpr = case statements of
    Empty -> compileReturn block returnExpr
    Core.Let name representation expr :<| rest -> do
        var <- newVar
        registerVariable name var representation
        block <- compileLet block var expr
        compileBody block rest returnExpr
    Core.LetJoin name parameters statements returnExpr :<| rest -> do
        undefined
    {-
    parameterVariables <- for parameters \(parameter, representation) -> do
        variable <- newVar
        registerVariable parameter variable representation
        pure variable
    joinPointBlock <- newBlock parameterVariables
    compileBody joinPointBlock statements returnExpr
    addJoinPoint name joinPointBlock.descriptor
    compileBody block rest returnExpr
    -}
    Core.LetFunction{} :<| rest -> undefined

compileLet :: (Compile es) => BlockBuilder -> MIR.Variable -> Core.Expr -> Eff es BlockBuilder
compileLet block local = \case
    Core.Value value -> undefined
    Core.Application function arguments -> do
        (block, arguments) <- compileValues block arguments
        continuation <- newBlock (MkPhys mempty)
        -- TODO: distinguish between direct and indirect calls
        finish block (MIR.CallDirect local function arguments continuation.descriptor)
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
        finish block (MIR.Return value)
    Core.Application function arguments -> do
        (block, arguments) <- compileValues block arguments
        -- TODO: this may not actually be a direct call?
        finish block (MIR.TailCallDirect function arguments)
    Core.JumpJoin joinPoint arguments -> do
        (block, arguments) <- compileValues block arguments

        joinPointBlock <- joinPointBlockFor joinPoint
        finish block (MIR.Jump joinPointBlock arguments)
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
        finish block (MIR.Return value)

compileValues :: (Compile es) => BlockBuilder -> Seq Core.Value -> Eff es (BlockBuilder, Seq MIR.Variable)
compileValues block values = mapAccumLM compileValue block values

compileValue :: (Compile es) => BlockBuilder -> Core.Value -> Eff es (BlockBuilder, MIR.Variable)
compileValue block = \case
    Core.Var var -> case var of
        Core.Local name -> undefined
        Core.Global name -> pure (block, undefined)
    Core.Literal literal -> do
        variable <- newVar
        case literal of
            Core.IntLiteral value -> do
                -- TODO: check the size properly etc.
                block <- addInstruction block (MIR.LoadIntLiteral variable (fromIntegral value))
                pure (block, variable)
            _ -> undefined
    Core.DataConstructorApplication constructor arguments representation -> do
        (block, arguments) <- compileValues block arguments
        variable <- newVar
        builder <- case constructor of
            Core.TupleConstructor size -> do
                assert (size == length arguments)
                addInstruction block (MIR.ProductConstructor{var = variable, values = arguments, representation = representation})
            Core.UserDefinedConstructor constructorName -> do
                GraphPersistence.getDataConstructorIndex constructorName >>= \case
                    OnlyConstructor -> addInstruction block (MIR.ProductConstructor{var = variable, values = arguments, representation = representation})
                    MultiConstructor tag -> addInstruction block (MIR.SumConstructor{var = variable, tag, values = arguments, representation})
        pure (builder, variable)

compileLambda :: (Compile es) => BlockBuilder -> MIR.Variable -> Seq (LocalCoreName, Core.Representation) -> Core.Representation -> Seq Core.Statement -> Core.Expr -> Eff es BlockBuilder
compileLambda block local parameters returnRepresentation statements returnExpr = do
    lambdaName <- undefined

    lambdaDeclarations <- compileFunction lambdaName parameters returnRepresentation statements returnExpr
    registerAdditionalDeclarations lambdaDeclarations
    -- TODO: do this properly with the right layout
    let locals = undefined
    -- addInstruction block (MIR.AllocateClosure local lambdaName locals)
    undefined

addJoinPoint :: (Compile es) => LocalCoreName -> MIR.BlockDescriptor -> Eff es ()
addJoinPoint name blockDescriptor = do
    modify (\state -> state{joinPoints = HashMap.insert name blockDescriptor state.joinPoints})

joinPointBlockFor :: (Compile es) => LocalCoreName -> Eff es MIR.BlockDescriptor
joinPointBlockFor name = do
    MkDeclarationState{joinPoints} <- get
    case HashMap.lookup name joinPoints of
        Nothing -> panic $ "JumpJoin to join point without a block descriptor: " <> pretty name
        Just descriptor -> pure descriptor

newVar :: (Compile es) => Eff es MIR.Variable
newVar = do
    state <- get
    let variable = MIR.MkVariable state.varCount
    put (state{varCount = state.varCount + 1})
    pure variable

data BlockBuilder = MkBlockBuilder
    { descriptor :: MIR.BlockDescriptor
    , instructions :: Seq MIR.Instruction
    , phis :: MIR.Phis
    }

newBlock :: (Compile es) => MIR.Phis -> Eff es BlockBuilder
newBlock phis = do
    descriptor <- MIR.MkBlockDescriptor <$> newUnique
    pure MkBlockBuilder{descriptor, instructions = [], phis}

-- The f only exists to allow shadowing the builder.
-- If you need this in a pure context, just instantiate it with Identity
addInstruction :: (Applicative f) => BlockBuilder -> MIR.Instruction -> f BlockBuilder
addInstruction builder newInstruction = pure $ builder{instructions = builder.instructions <> [newInstruction]}

finish :: (Compile es) => BlockBuilder -> MIR.Terminator -> Eff es ()
finish (MkBlockBuilder{descriptor, instructions, phis}) terminator = do
    let finishedBlock = MIR.MkBlock{instructions, terminator, phis}
    modify (\state -> state{blocks = HashMap.insert descriptor finishedBlock state.blocks})
