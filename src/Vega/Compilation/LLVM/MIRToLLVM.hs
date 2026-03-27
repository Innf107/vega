{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE ImplicitParams #-}
-- Workaround for https://gitlab.haskell.org/ghc/ghc/-/issues/20630 since we use
-- ImplicitParams with do blocks quite a lot here and we don't actually need ApplicativeDo
{-# LANGUAGE NoApplicativeDo #-}

module Vega.Compilation.LLVM.MIRToLLVM where

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
import Vega.Compilation.LLVM.Layout (Layout)
import Vega.Compilation.LLVM.Layout qualified as Layout
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Syntax (renderPackageName)
import Vega.Syntax qualified as Vega
import Vega.Util (forIndexed_, viaList)

data DeclarationState = MkDeclarationState
    { registeredBlocks :: HashMap MIR.BlockDescriptor LLVM.BasicBlock
    , outstandingBlocks :: Seq MIR.BlockDescriptor
    , variableMappings :: HashMap MIR.Variable LLVM.Value
    }

data FunctionEnv = MkFunctionEnv
    { sretVariable :: Maybe (LLVM.Value, Layout)
    }

type Compile es = (?context :: LLVM.Context, IOE :> es, ?function :: LLVM.Value, ?functionEnv :: FunctionEnv, State DeclarationState :> es)

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
            returnLayout <- Layout.representationLayout returnRepresentation

            baseParameterTypes <-
                for parameters \(_, representation) ->
                    Layout.llvmParameterType <$> Layout.representationLayout representation

            (parameterTypes, returnType, usesSRet) <- case Layout.kind returnLayout of
                Layout.AggregatePointer -> do
                    -- If we return a complex (AggregatePointer) value, we can't return it directly
                    -- but instead we need to assign it to an sret parameter. By convention, this is
                    -- always our *last* parameter
                    --
                    -- TODO: add an sret attribute (and alignment??)
                    pure (baseParameterTypes :|> LLVM.pointerType, LLVM.voidType, True)
                Layout.LLVMScalar scalar -> pure (baseParameterTypes, scalar, False)

            function <- liftIO $ LLVM.addFunction module_ (renderLLVMName name) (LLVM.functionType (viaList parameterTypes) returnType False)
            let ?function = function
            let ?functionEnv =
                    MkFunctionEnv
                        { sretVariable =
                            if usesSRet
                                -- The sret parameter is always the last one
                                then Just (LLVM.getParam function (length parameterTypes - 1), returnLayout)
                                else Nothing
                        }

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
        asVar_ targetVar $ LLVMBuilder.buildPhi builder undefined incomingValues

compileInstruction :: (Compile es) => LLVMBuilder.Builder -> MIR.Instruction -> Eff es ()
compileInstruction builder = \case
    MIR.Add out in1 in2 -> undefined
    MIR.AccessField var path target -> undefined
    MIR.Box{var, target, targetRepresentation} -> undefined
    MIR.Unbox{var, boxedTarget, representation} -> undefined
    MIR.ProductConstructor{var, values, representation} -> do
        llvmValues <- for values lookupVar
        layout <- Layout.representationLayout representation

        productPointer <- asVar var (LLVMBuilder.buildAlloca builder (Layout.llvmType layout))

        forIndexed_ llvmValues \value index -> do
            let (offset, _subLayout) = Layout.productOffsetAndLayout index layout
            pointer <- case offset of
                0 -> pure productPointer
                _ -> do
                    liftIO $ LLVMBuilder.buildGetElementPtr builder LLVM.int8Type productPointer [LLVM.constInt LLVM.int64Type (fromIntegral offset) False] ""
            _ <- liftIO $ LLVMBuilder.buildStore builder pointer value
            pure ()
    MIR.SumConstructor{var, tag, values, representation} -> undefined
    MIR.AllocClosure{var, closedValues, representation} -> undefined
    MIR.LoadGlobalClosure{var, functionName} -> do
        undefined
    MIR.LoadGlobal{var, globalName, representation} -> undefined
    MIR.LoadIntLiteral{var, literal} -> do
        insertVarMapping var (LLVM.constInt LLVM.int64Type (fromIntegral literal) True)
    MIR.LoadSumTag{var, sum, sumRepresentation} -> undefined
    MIR.CallDirect{var, functionName, arguments} -> undefined
    MIR.CallClosure{var, closure, arguments} -> undefined

compileTerminator :: (Compile es) => LLVMBuilder.Builder -> MIR.Terminator -> Eff es ()
compileTerminator builder = \case
    MIR.Return variable -> do
        value <- lookupVar variable

        case ?functionEnv.sretVariable of
            Nothing -> do
                _ <- liftIO $ LLVMBuilder.buildRet builder value
                pure ()
            Just (target, returnLayout) -> do
                -- The sret parameter is always the last parameter
                _ <- liftIO $ LLVMBuilder.buildMemCpy builder target 0 value 0 (LLVM.constInt LLVM.int64Type (fromIntegral (Layout.size returnLayout)) False)
                _ <- liftIO $ LLVMBuilder.buildRetVoid builder
                pure ()
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

asVar :: (Compile es) => MIR.Variable -> (Text -> IO LLVM.Value) -> Eff es LLVM.Value
asVar var cont = do
    llvmValue <- liftIO $ cont (renderVariable var)
    insertVarMapping var llvmValue
    pure llvmValue


insertVarMapping :: Compile es => MIR.Variable -> LLVM.Value -> Eff es ()
insertVarMapping var llvmValue =  modify (\state -> state{variableMappings = HashMap.insert var llvmValue state.variableMappings})

asVar_ :: (Compile es) => MIR.Variable -> (Text -> IO LLVM.Value) -> Eff es ()
asVar_ var cont = do
    _ <- asVar var cont
    pure ()

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
renderVariable (MIR.MkVariable var) = "x" <> show var

-- TODO: consider using more standard name mangling i guess
renderLLVMName :: Core.CoreName -> Text
renderLLVMName = \case
    Core.Global name -> "_vega_" <> renderPackageName name.moduleName.package <> ":" <> Text.intercalate "/" (toList (name.moduleName.subModules)) <> ":" <> name.name
    Core.Local _ -> undefined
