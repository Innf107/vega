{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE ImplicitParams #-}
-- Workaround for https://gitlab.haskell.org/ghc/ghc/-/issues/20630 since we use
-- ImplicitParams with do blocks quite a lot here and we don't actually need ApplicativeDo
{-# LANGUAGE NoApplicativeDo #-}

module Vega.Compilation.MIRToLLVM where

import Relude hiding (State, evalState, get, modify, put)

import Data.HashMap.Strict qualified as HashMap
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Sequence (Seq (..))
import Data.Text qualified as Text
import Data.Traversable (for)
import Effectful (Eff, IOE, (:>))
import Effectful.State.Static.Local (State, evalState, get, modify, put)
import LLVM.Core qualified as LLVM
import LLVM.InstructionBuilder qualified as LLVMBuilder
import Vega.Compilation.Core.Syntax (Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Syntax (renderPackageName)
import Vega.Syntax qualified as Vega
import Vega.Util (viaList)

data DeclarationState = MkDeclarationState
    { registeredBlocks :: HashMap MIR.BlockDescriptor LLVM.BasicBlock
    , outstandingBlocks :: Seq MIR.BlockDescriptor
    , variableMappings :: HashMap MIR.Variable LLVM.Value
    }

type Compile es = (?context :: LLVM.Context, IOE :> es, ?function :: LLVM.Value, State DeclarationState :> es)

compile :: (IOE :> es) => MIR.Program -> Eff es LLVM.Module
compile program = do
    context <- liftIO LLVM.contextCreate
    let ?context = context
    module_ <- liftIO $ LLVM.moduleCreateWithName "idkwhattoputhereyet"
    for_ program.declarations \declaration -> do
        let initialState =
                MkDeclarationState
                    { registeredBlocks = mempty
                    , outstandingBlocks = []
                    , variableMappings = mempty
                    }
        evalState initialState $ compileDeclaration module_ declaration
    pure module_

compileDeclaration ::
    (?context :: LLVM.Context, IOE :> es, State DeclarationState :> es) =>
    LLVM.Module -> MIR.Declaration -> Eff es ()
compileDeclaration module_ = \case
    MIR.DefineFunction
        { name
        , parameters
        , returnRepresentation
        , init
        , blocks
        } -> do
            parameterTypes <- viaList <$> for parameters \(_, representation) -> llvmParameterLayout representation
            returnType <- llvmReturnLayout returnRepresentation
            function <- liftIO $ LLVM.addFunction module_ (renderLLVMName name) (LLVM.functionType parameterTypes returnType False)
            let ?function = function

            builder <- liftIO LLVMBuilder.createBuilder

            initialBlock <- liftIO $ LLVM.appendBasicBlock function ""
            -- Because LLVM blocks may not jump back to the initial block, but MIR blocks may do that, we
            -- add an empty dummy block that just jumps to the first real block. LLVM should be able
            -- to optimize this out if it is not necessary.

            initialMIRBlock <- registerNewBlock init

            liftIO $ LLVMBuilder.positionBuilderAtEnd builder initialBlock
            _ <- liftIO $ LLVMBuilder.buildBr builder initialMIRBlock

            let go = do
                    state@MkDeclarationState{outstandingBlocks} <- get
                    case outstandingBlocks of
                        [] -> pure ()
                        blockDescriptors -> do
                            put state{outstandingBlocks = []}
                            for_ blockDescriptors \descriptor -> do
                                let block = case HashMap.lookup descriptor blocks of
                                        Nothing -> panic $ "Unknown block descriptor: " <> pretty descriptor <> " in function " <> pretty name
                                        Just block -> block
                                compileRegisteredBlock builder descriptor block
                            go
            go

compileRegisteredBlock :: (Compile es) => LLVMBuilder.Builder -> MIR.BlockDescriptor -> MIR.Block -> Eff es ()
compileRegisteredBlock builder descriptor block = do
    MkDeclarationState{registeredBlocks} <- get
    let llvmBlock = case HashMap.lookup descriptor registeredBlocks of
            Nothing -> panic $ "compileRegisteredBlock: Trying to compile unregistered MIR block " <> pretty descriptor
            Just llvmBlock -> llvmBlock
    liftIO $ LLVMBuilder.positionBuilderAtEnd builder llvmBlock
    compilePhis builder block.phis
    for_ block.instructions (compileInstruction builder)
    compileTerminator builder block.terminator

compilePhis :: (Compile es) => LLVMBuilder.Builder -> MIR.Phis -> Eff es ()
compilePhis builder (MIR.MkPhis phis) = do
    for_ (HashMap.toList phis) \(targetVar, incoming) -> do
        incomingValues <-
            fromList <$> for (HashMap.toList incoming) \(block, variable) -> do
                value <- lookupVar variable
                block <- lookupBlock block
                pure (value, block)
        asVar targetVar $ LLVMBuilder.buildPhi builder undefined incomingValues


compileInstruction :: (Compile es) => LLVMBuilder.Builder -> MIR.Instruction -> Eff es ()
compileInstruction builder = \case
    _ -> undefined

compileTerminator :: (Compile es) => LLVMBuilder.Builder -> MIR.Terminator -> Eff es ()
compileTerminator builder = \case
    MIR.Return variable -> undefined
    _ -> undefined

registerNewBlock :: (Compile es) => MIR.BlockDescriptor -> Eff es LLVM.BasicBlock
registerNewBlock descriptor = do
    state <- get @DeclarationState
    case HashMap.lookup descriptor state.registeredBlocks of
        Just _previousBlock -> panic $ "Trying to register MIR block " <> pretty descriptor <> " twice"
        Nothing -> do
            llvmBlock <- liftIO $ LLVM.appendBasicBlock ?function ""
            put
                ( state
                    { registeredBlocks = HashMap.insert descriptor llvmBlock state.registeredBlocks
                    , outstandingBlocks = state.outstandingBlocks :|> descriptor
                    }
                )
            pure llvmBlock

data Layout = MkLayout
    { size :: Int
    , alignment :: Int
    , llvmType :: LLVM.Type
    }

asVar :: (Compile es) => MIR.Variable -> (Text -> IO LLVM.Value) -> Eff es ()
asVar var cont = do
    llvmValue <- liftIO $ cont (renderVariable var)

    modify (\state -> state{variableMappings = HashMap.insert var llvmValue state.variableMappings})

lookupVar :: (HasCallStack, Compile es) => MIR.Variable -> Eff es LLVM.Value
lookupVar variable = do
    MkDeclarationState{variableMappings} <- get
    case HashMap.lookup variable variableMappings of
        Nothing -> panic $ "Trying to use MIR variable without associated LLVM value: " <> pretty variable
        Just value -> pure value

lookupBlock :: (HasCallStack, Compile es) => MIR.BlockDescriptor -> Eff es LLVM.BasicBlock
lookupBlock block = do
    MkDeclarationState{registeredBlocks} <- get
    case HashMap.lookup block registeredBlocks of
        Nothing -> panic $ "Trying to look up LLVM block of unregistered MIR block " <> pretty block
        Just value -> pure value

renderVariable :: MIR.Variable -> Text
renderVariable (MIR.MkVariable var) = show var

representationLayout :: (Compile es) => Representation -> Eff es Layout
representationLayout = \case
    Core.PrimitiveRep primitive -> case primitive of
        Vega.IntRep -> pure (MkLayout{size = 8, alignment = 8, llvmType = LLVM.int64Type})
        Vega.BoxedRep -> pure (MkLayout{size = 8, alignment = 8, llvmType = LLVM.pointerType})
        _ -> undefined
    _ -> undefined

-- TODO: consider using more standard name mangling i guess
renderLLVMName :: Core.CoreName -> Text
renderLLVMName = \case
    Core.Global name -> "_vega_" <> renderPackageName name.moduleName.package <> ":" <> Text.intercalate "/" (toList (name.moduleName.subModules)) <> ":" <> name.name
    Core.Local _ -> undefined

llvmParameterLayout :: (?context :: LLVM.Context) => Representation -> Eff es LLVM.Type
llvmParameterLayout representation = case representation of
    Core.PrimitiveRep primitive -> primitiveLayout primitive
    Core.ProductRep inner -> undefined
    Core.SumRep{} -> undefined
    _ -> undefined

llvmReturnLayout :: (?context :: LLVM.Context) => Representation -> Eff es LLVM.Type
llvmReturnLayout representation = case representation of
    Core.PrimitiveRep primitive -> primitiveLayout primitive
    Core.ProductRep [] -> pure $ LLVM.voidType
    Core.ProductRep inner -> undefined
    Core.SumRep{} -> undefined
    _ -> undefined

primitiveLayout :: (?context :: LLVM.Context) => Vega.PrimitiveRep -> Eff es LLVM.Type
primitiveLayout = \case
    Vega.UnitRep -> pure $ LLVM.structType [] False
    Vega.EmptyRep -> pure LLVM.voidType
    -- TODO: we might be able to give heap pointers a different address space from unmanaged pointers?
    Vega.BoxedRep -> pure $ LLVM.pointerType
    Vega.IntRep -> pure $ LLVM.int64Type
    Vega.DoubleRep -> pure $ LLVM.doubleType
