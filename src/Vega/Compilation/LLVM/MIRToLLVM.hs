{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}
-- Workaround for https://gitlab.haskell.org/ghc/ghc/-/issues/20630 since we use
-- ImplicitParams with do blocks quite a lot here and we don't actually need ApplicativeDo
{-# LANGUAGE NoApplicativeDo #-}

module Vega.Compilation.LLVM.MIRToLLVM (compile) where

import Relude hiding (State, evalState, get, modify, put)

import Data.ByteString qualified as ByteString
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Data.Traversable (for)
import Data.Vector.Storable qualified as Storable
import Data.Vector.Strict qualified as Strict
import Effectful (Eff, IOE, (:>))
import Effectful.State.Static.Local (State, evalState, get, modify, put)
import GHC.Records (HasField, getField)
import GHC.TypeLits (Symbol)
import LLVM.Core qualified as LLVM
import LLVM.Core.Context qualified as LLVM
import LLVM.InstructionBuilder qualified as LLVMBuilder
import System.IO.Unsafe (unsafePerformIO)
import Vega.Alignment qualified as Alignment
import Vega.Compilation.Core.Syntax (Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.LLVM.AttributeFunctionType (AttributeFunctionType, addFunctionWithAttributes, attributeFunctionType, parametersWithAttributes, rawFunctionType, returnTypeWithAttributes)
import Vega.Compilation.LLVM.Layout (Layout)
import Vega.Compilation.LLVM.Layout qualified as Layout
import Vega.Compilation.LLVM.Runtime (RuntimeDefinitions (..), declareRuntimeDefinitions)
import Vega.Compilation.LLVM.Runtime.Heap qualified as Heap
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Debug (showHeadConstructor)
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Syntax (renderPackageName)
import Vega.Syntax qualified as Vega
import Vega.Util (forIndexed_, viaList, type (?))
import Vega.Util qualified as Util
import Vega.Compilation.LLVM.Runtime.ToLLVMConstant (ToLLVMConstant(toLLVMConstant))
import qualified Vega.Compilation.LLVM.Runtime.ToLLVMConstant as ToLLVMConstant

data DeclarationState = MkDeclarationState
    { registeredBlocks :: HashMap MIR.BlockDescriptor LLVM.BasicBlock
    , outstandingBlocks :: Seq MIR.BlockDescriptor
    , variableMappings :: HashMap MIR.Variable (LLVM.Value, Layout)
    }

data FunctionEnv = MkFunctionEnv
    { sretVariable :: Maybe (LLVM.Value, Layout)
    }

type Compile es =
    ( ?context :: LLVM.Context
    , ?module_ :: LLVM.Module
    , ?runtimeDefinitions :: RuntimeDefinitions
    , IOE :> es
    , ?function :: LLVM.Value
    , ?functionEnv :: FunctionEnv
    , State DeclarationState :> es
    )

compile :: (IOE :> es) => MIR.Program -> Eff es LLVM.Module
compile program = do
    context <- liftIO LLVM.contextCreate
    let ?context = context
    module_ <- LLVM.moduleCreateWithName "idkwhattoputhereyet"
    runtimeDefinitions <- declareRuntimeDefinitions module_
    let ?module_ = module_
    let ?runtimeDefinitions = runtimeDefinitions
    for_ program.declarations \declaration -> do
        forwardDeclareDeclaration declaration

    for_ program.declarations \declaration -> do
        let initialState =
                MkDeclarationState
                    { registeredBlocks = mempty
                    , outstandingBlocks = []
                    , variableMappings = mempty
                    }
        evalState initialState $ compileDeclaration declaration
    pure module_

type AttributeApplication = LLVM.Value -> IO ()

functionLLVMType ::
    (?context :: LLVM.Context, IOE :> es) =>
    Seq Layout ->
    Layout ->
    Eff es (AttributeFunctionType, "sretParameter" ? Maybe (Int, Layout))
functionLLVMType parameters returnLayout = do
    let baseParameterTypes = fmap Layout.llvmParameterType parameters

    (parameterTypes, returnType, usesSRet) <- case Layout.kind returnLayout of
        Layout.AggregatePointer -> do
            -- If we return a complex (AggregatePointer) value, we can't return it directly
            -- but instead we need to assign it to an sret parameter. This always needs to be the *first* parameter.
            --
            -- TODO: alignment?
            sretAttribute <- sretAttribute (Layout.llvmType returnLayout)
            pure ((LLVM.pointerType, [sretAttribute]) :<| baseParameterTypes, LLVM.voidType, True)
        Layout.LLVMScalar scalar -> pure (baseParameterTypes, scalar, False)
        Layout.ZeroSized -> pure (baseParameterTypes, LLVM.voidType, False)

    -- The sret parameter is always the first one
    let sretParameter = if usesSRet then Just (0, returnLayout) else Nothing
    let functionType = attributeFunctionType (viaList parameterTypes) (returnType, [])

    pure (functionType, sretParameter)

forwardDeclareDeclaration ::
    ( ?context :: LLVM.Context
    , ?module_ :: LLVM.Module
    , ?runtimeDefinitions :: RuntimeDefinitions
    , IOE :> es
    ) =>
    MIR.Declaration -> Eff es ()
forwardDeclareDeclaration = \case
    MIR.DefineFunction{name, parameters, returnRepresentation} -> do
        parameterLayouts <- for parameters \(_, representation) -> Layout.representationLayout representation
        returnLayout <- Layout.representationLayout returnRepresentation

        (functionTypeWithAttributes, _) <- functionLLVMType parameterLayouts returnLayout
        function <- addFunctionWithAttributes ?module_ (renderLLVMName name) functionTypeWithAttributes
        LLVM.setFunctionCallConv function LLVM.tailCallConv

        -- We also generate a wrapper function for closures. See Note: [Closure Representation]
        let parameters = parametersWithAttributes functionTypeWithAttributes
        let returnType = returnTypeWithAttributes functionTypeWithAttributes
        -- We add a single "Boxed" (i.e. ptr for LLVM) argument
        let wrapperType = attributeFunctionType (parameters <> [(LLVM.pointerType, [])]) returnType
        closureWrapper <- addFunctionWithAttributes ?module_ (closureWrapperNameForFunction name) wrapperType
        LLVM.setFunctionCallConv closureWrapper LLVM.tailCallConv

        block <- LLVM.appendBasicBlock closureWrapper ""
        builder <- LLVMBuilder.createBuilder
        LLVMBuilder.positionBuilderAtEnd builder block

        let arguments = Storable.generate (Strict.length parameters) \i -> LLVM.getParam function i
        result <- LLVMBuilder.buildCall builder (rawFunctionType functionTypeWithAttributes) function arguments ""
        LLVM.setTailCallKind result LLVM.TailCallKindMustTail
        LLVM.setInstructionCallConv result LLVM.tailCallConv
        case Layout.kind returnLayout of
            Layout.LLVMScalar _ -> do
                _ <- LLVMBuilder.buildRet builder result
                pure ()
            -- AggregatePointers are returned in sret parameters anyway so we are already passing that along correctly anyway
            Layout.AggregatePointer -> do
                _ <- LLVMBuilder.buildRetVoid builder
                pure ()
            Layout.ZeroSized -> do
                _ <- LLVMBuilder.buildRetVoid builder
                pure ()

compileDeclaration ::
    ( ?context :: LLVM.Context
    , ?module_ :: LLVM.Module
    , ?runtimeDefinitions :: RuntimeDefinitions
    , IOE :> es
    , State DeclarationState :> es
    ) =>
    MIR.Declaration -> Eff es ()
compileDeclaration = \case
    MIR.DefineFunction
        { name
        , parameters
        , returnRepresentation
        , init
        , blocks
        } -> do
            -- TODO: we don't actually need to re-compute this twice now
            parameterLayouts <- for parameters \(_, representation) -> Layout.representationLayout representation
            returnLayout <- Layout.representationLayout returnRepresentation
            (_functionType, sretParameter) <- functionLLVMType parameterLayouts returnLayout

            function <-
                LLVM.getNamedFunction ?module_ (renderLLVMName name) >>= \case
                    Nothing -> panic $ "Unable to access function '" <> pretty name <> "' that should have been forward-declared."
                    Just function_ -> pure function_
            let ?function = function
            let ?functionEnv =
                    MkFunctionEnv
                        { sretVariable =
                            case sretParameter of
                                Just (position, returnLayout) -> Just (LLVM.getParam function position, returnLayout)
                                Nothing -> Nothing
                        }

            forIndexed_ parameters \(variable, representation) index -> do
                layout <- Layout.representationLayout representation
                insertVarMapping variable (LLVM.getParam function index) layout

            builder <- LLVMBuilder.createBuilder

            initialBlock <- LLVM.appendBasicBlock function ""
            -- Because LLVM blocks may not jump back to the initial block, but MIR blocks may do that, we
            -- add an empty dummy block that just jumps to the first real block. LLVM should be able
            -- to optimize this out if it is not necessary.

            initialMIRBlock <- registerNewBlock init

            LLVMBuilder.positionBuilderAtEnd builder initialBlock
            _ <- LLVMBuilder.buildBr builder initialMIRBlock

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
    LLVMBuilder.positionBuilderAtEnd builder llvmBlock
    compilePhis builder block.phis
    for_ block.instructions (compileInstruction builder)
    compileTerminator builder block.terminator

compilePhis :: (Compile es) => LLVMBuilder.Builder -> MIR.Phis -> Eff es ()
compilePhis builder (MIR.MkPhis phis) = do
    for_ (HashMap.toList phis) \(targetVar, incoming) -> do
        incomingValues <-
            fromList <$> for (HashMap.toList incoming) \(block, variable) -> do
                (value, _) <- lookupVar variable
                block <- lookupBlock block
                pure (value, block)
        asVar_ targetVar undefined $ LLVMBuilder.buildPhi builder undefined incomingValues

compileInstruction :: (Compile es) => LLVMBuilder.Builder -> MIR.Instruction -> Eff es ()
compileInstruction builder = \case
    MIR.Identity var target -> do
        (targetValue, targetLayout) <- lookupVar target
        insertVarMapping var targetValue targetLayout
    MIR.Add var arg1 arg2 -> do
        arg1Value <- lookupVarValue arg1
        arg2Value <- lookupVarValue arg2
        asVar_ var Layout.intLayout $ LLVMBuilder.buildAdd builder arg1Value arg2Value
    MIR.AccessField{var, path, target, fieldRepresentation} -> do
        (targetValue, targetLayout) <- lookupVar target
        fieldLayout <- Layout.representationLayout fieldRepresentation

        let go currentOffset layout = \case
                Empty -> currentOffset
                MIR.ProductFieldPath index :<| rest -> do
                    let (offset, innerLayout) = Layout.productOffsetAndLayout index layout
                    go (currentOffset + offset) innerLayout rest
                MIR.SumConstructorPath index :<| rest -> do
                    let (offset, innerLayout) = Layout.sumOffsetAndLayout index layout
                    go (currentOffset + offset) innerLayout rest
        let offset = go 0 targetLayout path

        pointer <- buildGEPOffset builder targetValue offset ""
        asVar_ var fieldLayout $ buildLoadOrKeepPointer builder fieldLayout pointer
    MIR.Box{var, target} -> do
        -- TODO: we should probably inline the fast path for minor heap allocations here
        (targetValue, targetLayout) <- lookupVar target

        layoutInfoTablePointer <- getOrCreateLayoutInfoTablePointer targetLayout

        memoryPointer <- asVar var Layout.boxedLayout $ buildRuntimeCall builder "vega_allocate_boxed" [layoutInfoTablePointer]
        buildComplexStore builder targetLayout targetValue memoryPointer
    MIR.Unbox{var, boxedTarget, representation} -> do
        (targetValue, _) <- lookupVar boxedTarget
        layout <- Layout.representationLayout representation

        asVar_ var layout $ buildComplexLoad builder layout targetValue
    MIR.ProductConstructor{var, values, representation} -> do
        llvmValues <- for values lookupVarValue
        layout <- Layout.representationLayout representation

        case Layout.kind layout of
            Layout.ZeroSized -> insertVarMapping var zeroSizedDummyValue layout
            Layout.LLVMScalar{} -> undefined
            Layout.AggregatePointer -> do
                productPointer <- asVar var layout $ buildLayoutAlloca builder layout
                forIndexed_ llvmValues \value index -> do
                    let (offset, subLayout) = Layout.productOffsetAndLayout index layout
                    pointer <- case offset of
                        0 -> pure productPointer
                        _ -> buildGEPOffset builder productPointer offset ""
                    store <- LLVMBuilder.buildStore builder value pointer
                    LLVM.setAlignment store (Alignment.toInt (Layout.alignment subLayout))
                    pure ()
    MIR.SumConstructor{var, tag, payload, representation} -> do
        (value, _) <- lookupVar payload
        layout <- Layout.representationLayout representation

        sumPointer <- asVar var layout $ buildLayoutAlloca builder layout

        -- Store the tag
        let tagLLVMType = LLVM.intType (Layout.sumTagSizeInBytes layout * 8)
        tagPointer <- buildGEPOffset builder sumPointer (Layout.sumTagOffset layout) ""
        _ <- LLVMBuilder.buildStore builder (LLVM.constInt tagLLVMType (fromIntegral tag) False) tagPointer

        -- Storing the payload currently involves a single contiguous copy. This may change in the future
        -- if we add support for non-contiguous payloads.
        -- See NOTE: [Sum tags] in Vega.Compilation.LLVM.Layout for details.
        let (payloadOffset, payloadLayout) = Layout.sumOffsetAndLayout tag layout

        payloadPointer <- buildGEPOffset builder sumPointer payloadOffset ""
        buildComplexStore builder payloadLayout value payloadPointer
    MIR.AllocClosure{var, closedValues, representation} -> undefined
    MIR.LoadGlobalClosure{var, functionName} -> do
        asVar_ var (Layout.closureLayout Layout.boxedLayout) $ buildClosure builder functionName Layout.boxedLayout LLVM.constNullPointer
    MIR.LoadGlobal{var, globalName, representation} -> undefined
    MIR.LoadIntLiteral{var, literal} -> do
        insertVarMapping var (LLVM.constInt LLVM.int64Type (fromIntegral literal) True) Layout.intLayout
    MIR.LoadSumTag{var, sum} -> do
        (sumValue, sumLayout) <- lookupVar sum
        let tagLayout = Layout.sizedIntLayoutInBytes (Layout.sumTagSizeInBytes sumLayout)

        tagPointer <- buildGEPOffset builder sumValue (Layout.sumTagOffset sumLayout) "tagptr"
        asVar_ var tagLayout $ LLVMBuilder.buildLoad builder (Layout.llvmType tagLayout) tagPointer
    MIR.CallDirect{var, functionName, arguments, returnRepresentation} -> do
        (argumentValues, argumentLayouts) <- Seq.unzip <$> for arguments lookupVar
        returnLayout <- Layout.representationLayout returnRepresentation

        asVar_ var returnLayout $ buildDirectCall builder functionName (viaList argumentValues) argumentLayouts returnLayout LLVM.TailCallKindNone
    MIR.CallClosure{var, closure, arguments, returnRepresentation} -> do
        (closureValue, closureLayout) <- lookupVar closure
        let (functionPointerOffset, _functionPointerLayout) = Layout.productOffsetAndLayout 0 closureLayout
        pointerToFunctionPointer <- buildGEPOffset builder closureValue functionPointerOffset ""
        functionPointer <- LLVMBuilder.buildLoad builder LLVM.pointerType pointerToFunctionPointer ""

        let (payloadOffset, payloadLayout) = Layout.productOffsetAndLayout 1 closureLayout
        pointerToPayload <- buildGEPOffset builder closureValue payloadOffset ""
        payload <- buildLoadOrKeepPointer builder payloadLayout pointerToPayload "payload"

        (argumentValuesWithoutPayload, argumentLayoutsWithoutPayload) <- Seq.unzip <$> for arguments lookupVar

        let argumentLayouts = viaList $ argumentLayoutsWithoutPayload <> [Layout.boxedLayout]

        returnLayout <- Layout.representationLayout returnRepresentation

        (closureFunctionTypeWithAttributes, _) <- functionLLVMType argumentLayouts returnLayout
        let closureFunctionType = rawFunctionType closureFunctionTypeWithAttributes

        case Layout.kind returnLayout of
            Layout.ZeroSized -> do
                callInstr <-
                    LLVMBuilder.buildCall
                        builder
                        closureFunctionType
                        functionPointer
                        (viaList $ argumentValuesWithoutPayload <> [payload])
                        ""
                LLVM.setInstructionCallConv callInstr LLVM.tailCallConv
                insertVarMapping var zeroSizedDummyValue returnLayout
            Layout.LLVMScalar _ -> do
                callInstr <-
                    asVar var returnLayout $
                        LLVMBuilder.buildCall
                            builder
                            closureFunctionType
                            functionPointer
                            (viaList $ argumentValuesWithoutPayload <> [payload])
                LLVM.setInstructionCallConv callInstr LLVM.tailCallConv
            Layout.AggregatePointer -> do
                returnPointer <- asVar var returnLayout $ buildLayoutAlloca builder returnLayout
                callInstr <-
                    LLVMBuilder.buildCall
                        builder
                        closureFunctionType
                        functionPointer
                        (viaList $ argumentValuesWithoutPayload <> [returnPointer, payload])
                        ""
                LLVM.setInstructionCallConv callInstr LLVM.tailCallConv

compileTerminator :: (Compile es) => LLVMBuilder.Builder -> MIR.Terminator -> Eff es ()
compileTerminator builder = \case
    MIR.Return variable -> do
        (value, layout) <- lookupVar variable

        case Layout.kind layout of
            Layout.ZeroSized -> do
                _ <- LLVMBuilder.buildRetVoid builder
                pure ()
            Layout.LLVMScalar _ -> do
                _ <- LLVMBuilder.buildRet builder value
                pure ()
            Layout.AggregatePointer -> do
                case ?functionEnv.sretVariable of
                    Nothing -> panic $ "Returning AggregatePointer layout from a function without sret variable: " <> show layout
                    Just (sretVariable, _) -> do
                        buildComplexStore builder layout sretVariable value
                        _ <- LLVMBuilder.buildRetVoid builder
                        pure ()
    MIR.SwitchInt scrutinee alternatives -> do
        (scrutineeValue, layout) <- lookupVar scrutinee
        let llvmType = Layout.llvmType layout

        cases <-
            viaList <$> for alternatives \(int, target) -> do
                targetLLVMBlock <- registerNewBlock target
                pure (LLVM.constInt llvmType (fromIntegral int) False, targetLLVMBlock)

        defaultBlock <- newUnreachableBlock

        _ <- LLVMBuilder.buildSwitch builder scrutineeValue cases defaultBlock
        pure ()
    MIR.TailCallDirect{functionName, arguments, returnRepresentation} -> do
        (argumentValues, argumentLayouts) <- Seq.unzip <$> for arguments lookupVar
        returnLayout <- Layout.representationLayout returnRepresentation

        result <- buildDirectCall builder functionName (viaList argumentValues) argumentLayouts returnLayout LLVM.TailCallKindMustTail "ret"
        _ <- LLVMBuilder.buildRet builder result
        pure ()
    _ -> undefined

getOrCreateLayoutInfoTablePointer :: (Compile es) => Layout -> Eff es LLVM.Value
getOrCreateLayoutInfoTablePointer layout = do
    let identifier = "info_" <> Layout.identifier layout
    LLVM.getNamedGlobal ?module_ identifier >>= \case
        Just global -> pure (LLVM.globalAsValue global)
        Nothing -> do
            let infoTable =
                    Heap.MkInfoTable
                        { objectType = Heap.Boxed
                        , layout =
                            Heap.BoxedLayout
                                ( Heap.MkBoxedLayout
                                    { sizeInBytes = fromIntegral (Layout.size layout)
                                    , -- TODO: fill this in properly
                                      boxedCount = 0
                                    }
                                )
                        }
            (infoTableLLVMType, infoTableConstant) <- toLLVMConstant infoTable

            llvmInfoTableGlobal <- LLVM.addGlobal ?module_ infoTableLLVMType identifier
            LLVM.setInitializer llvmInfoTableGlobal infoTableConstant
            pure (LLVM.globalAsValue llvmInfoTableGlobal)

buildDirectCall :: (Compile es) => LLVMBuilder.Builder -> Vega.GlobalName -> Storable.Vector LLVM.Value -> Seq Layout -> Layout -> LLVM.TailCallKind -> Text -> Eff es LLVM.Value
buildDirectCall builder functionName arguments argumentLayouts returnLayout tailCallKind varName = do
    function <-
        LLVM.getNamedFunction ?module_ (renderLLVMName (Core.Global functionName)) >>= \case
            Nothing -> panic $ "Trying to generate call to non-existent function" <> pretty (Core.Global functionName)
            Just function -> pure function

    (functionTypeWithAttributes, _) <- functionLLVMType argumentLayouts returnLayout
    let functionType = rawFunctionType functionTypeWithAttributes

    (returnValue, callInstr) <- case Layout.kind returnLayout of
        Layout.ZeroSized -> do
            callInstr <- LLVMBuilder.buildCall builder functionType function arguments ""
            pure (zeroSizedDummyValue, callInstr)
        Layout.LLVMScalar _ -> do
            callInstr <- LLVMBuilder.buildCall builder functionType function arguments varName
            pure (callInstr, callInstr)
        Layout.AggregatePointer -> do
            -- TODO: this doesn't actually work for tail calls (it's probably unsound even oops)
            returnPointer <- buildLayoutAlloca builder returnLayout varName
            callInstr <- LLVMBuilder.buildCall builder functionType function (arguments <> [returnPointer]) ""
            pure (returnPointer, callInstr)
    LLVM.setTailCallKind callInstr tailCallKind
    LLVM.setInstructionCallConv callInstr LLVM.tailCallConv
    pure returnValue

buildRuntimeCall ::
    (Compile es) =>
    LLVMBuilder.Builder ->
    forall (name :: Symbol) ->
    (HasField name RuntimeDefinitions (LLVM.Value, LLVM.FunctionType)) =>
    Storable.Vector LLVM.Value ->
    Text ->
    Eff es LLVM.Value
buildRuntimeCall builder name arguments varName = do
    let (function, functionType) = getField @name ?runtimeDefinitions
    LLVMBuilder.buildCall builder functionType function arguments varName

buildClosure :: (Compile es) => LLVMBuilder.Builder -> Vega.GlobalName -> Layout -> LLVM.Value -> Text -> Eff es LLVM.Value
buildClosure builder functionName closureLayout closureValue varName = do
    functionPointer <-
        -- We need to use the closure wrapper instead of the actual function here. See Note: [Closure Representation].
        LLVM.getNamedFunction ?module_ (closureWrapperNameForFunction (Core.Global functionName)) >>= \case
            Nothing -> panic $ "Trying to create closure for non-existent top-level function: " <> Vega.prettyGlobal Vega.VarKind functionName
            Just function_ -> pure function_
    let combinedLayout = Layout.productLayout [Layout.functionPointerLayout, closureLayout]
    buildProduct builder [functionPointer, closureValue] combinedLayout varName

buildProduct :: (Compile es) => LLVMBuilder.Builder -> Seq LLVM.Value -> Layout -> Text -> Eff es LLVM.Value
buildProduct builder values layout varName = do
    productPointer <- buildLayoutAlloca builder layout varName

    forIndexed_ values \value index -> do
        let (offset, subLayout) = Layout.productOffsetAndLayout index layout
        pointer <- case offset of
            0 -> pure productPointer
            _ -> buildGEPOffset builder productPointer offset ""
        buildComplexStore builder subLayout value pointer

    pure productPointer

buildComplexStore :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> LLVM.Value -> Eff es ()
buildComplexStore builder layout value pointer = do
    case Layout.kind layout of
        Layout.LLVMScalar _scalar -> do
            store <- LLVMBuilder.buildStore builder value pointer
            LLVM.setAlignment store (Alignment.toInt (Layout.alignment layout))
            pure ()
        Layout.AggregatePointer -> do
            let alignment = Alignment.toInt (Layout.alignment layout)
            let size = LLVM.constInt LLVM.int64Type (fromIntegral (Layout.size layout)) False
            _ <- LLVMBuilder.buildMemCpy builder pointer alignment value alignment size
            pure ()
        Layout.ZeroSized -> pure ()

buildLoadOrKeepPointer :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> Text -> Eff es LLVM.Value
buildLoadOrKeepPointer builder layout value varName = case Layout.kind layout of
    Layout.LLVMScalar scalar -> LLVMBuilder.buildLoad builder scalar value varName
    Layout.AggregatePointer -> pure value
    Layout.ZeroSized -> pure value

buildComplexLoad :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> Text -> Eff es LLVM.Value
buildComplexLoad builder layout pointer varName = case Layout.kind layout of
    Layout.LLVMScalar scalar -> LLVMBuilder.buildLoad builder scalar pointer varName
    Layout.AggregatePointer -> do
        localMemory <- buildLayoutAlloca builder layout ""
        let alignment = Alignment.toInt (Layout.alignment layout)
        let size = LLVM.constInt LLVM.int64Type (fromIntegral (Layout.size layout)) False
        _ <- LLVMBuilder.buildMemCpy builder localMemory alignment pointer alignment size
        pure localMemory
    Layout.ZeroSized -> pure zeroSizedDummyValue

{- | Build a @getelementptr@ instruction pointing at a constant offset given in bytes.
The offset is assumed to be in-bounds.
-}
buildGEPOffset :: (Compile es) => LLVMBuilder.Builder -> LLVM.Value -> Int -> Text -> Eff es LLVM.Value
buildGEPOffset builder pointer offset name = do
    result <- LLVMBuilder.buildInBoundsGetElementPtr builder LLVM.int8Type pointer [LLVM.constInt LLVM.int64Type (fromIntegral offset) False] name
    pure result

buildLayoutAlloca :: Compile es => LLVMBuilder.Builder -> Layout -> Text -> Eff es LLVM.Value
buildLayoutAlloca builder layout varName = do
    alloca <- LLVMBuilder.buildAlloca builder (Layout.llvmType layout) varName
    LLVM.setAlignment alloca (Alignment.toInt (Layout.alignment layout))
    pure alloca

registerNewBlock :: (Compile es) => MIR.BlockDescriptor -> Eff es LLVM.BasicBlock
registerNewBlock descriptor = do
    state <- get @DeclarationState
    case HashMap.lookup descriptor state.registeredBlocks of
        Just _previousBlock -> panic $ "Trying to register MIR block " <> pretty descriptor <> " twice"
        Nothing -> do
            llvmBlock <- LLVM.appendBasicBlock ?function ""
            put
                ( state
                    { registeredBlocks = HashMap.insert descriptor llvmBlock state.registeredBlocks
                    , outstandingBlocks = state.outstandingBlocks :|> descriptor
                    }
                )
            pure llvmBlock

-- TODO: we might want to be able to swap this out to panic in debug builds instead of using unreachable
newUnreachableBlock :: (Compile es) => Eff es LLVM.BasicBlock
newUnreachableBlock = do
    -- TODO: it would be nice if we could reuse the existing builder here instead of allocating a new one
    builder <- LLVMBuilder.createBuilder
    llvmBlock <- LLVM.appendBasicBlock ?function "unreachable"
    LLVMBuilder.positionBuilderAtEnd builder llvmBlock
    _ <- LLVMBuilder.buildUnreachable builder
    pure llvmBlock

asVar :: (Compile es) => MIR.Variable -> Layout -> (Text -> Eff es LLVM.Value) -> Eff es LLVM.Value
asVar var layout cont = do
    llvmValue <- cont (renderVariable var)
    insertVarMapping var llvmValue layout
    pure llvmValue

insertVarMapping :: (Compile es) => MIR.Variable -> LLVM.Value -> Layout -> Eff es ()
insertVarMapping var llvmValue layout = modify (\state -> state{variableMappings = HashMap.insert var (llvmValue, layout) state.variableMappings})

asVar_ :: (Compile es) => MIR.Variable -> Layout -> (Text -> Eff es LLVM.Value) -> Eff es ()
asVar_ var layout cont = do
    _ <- asVar var layout cont
    pure ()

closureWrapperNameForFunction :: Core.CoreName -> Text
closureWrapperNameForFunction coreName = renderLLVMName coreName <> "__closure"

lookupVar :: (HasCallStack, Compile es) => MIR.Variable -> Eff es (LLVM.Value, Layout)
lookupVar variable = do
    MkDeclarationState{variableMappings} <- get
    case HashMap.lookup variable variableMappings of
        Nothing -> panic $ "Trying to use MIR variable without associated LLVM value: " <> pretty variable
        Just value -> pure value

lookupVarValue :: (HasCallStack, Compile es) => MIR.Variable -> Eff es LLVM.Value
lookupVarValue variable = do
    (value, _) <- lookupVar variable
    pure value

lookupBlock :: (HasCallStack, Compile es) => MIR.BlockDescriptor -> Eff es LLVM.BasicBlock
lookupBlock block = do
    MkDeclarationState{registeredBlocks} <- get
    case HashMap.lookup block registeredBlocks of
        Nothing -> panic $ "Trying to look up LLVM block of unregistered MIR block " <> pretty block
        Just value -> pure value

renderVariable :: MIR.Variable -> Text
renderVariable (MIR.MkVariable name index) = name <> "_" <> show index

-- TODO: consider using more standard name mangling i guess
renderLLVMName :: Core.CoreName -> Text
renderLLVMName = \case
    Core.Global name -> "_vega_" <> renderPackageName name.moduleName.package <> "::" <> Text.intercalate "/" (toList (name.moduleName.subModules)) <> "::" <> name.name
    Core.Local _ -> undefined

sretAttribute :: (?context :: LLVM.Context, IOE :> es) => LLVM.Type -> Eff es LLVM.Attribute
sretAttribute targetType = do
    kind <- LLVM.getEnumAttributeKindForName "sret"
    LLVM.createTypeAttribute kind targetType

byvalAttribute :: (?context :: LLVM.Context, IOE :> es) => LLVM.Type -> Eff es LLVM.Attribute
byvalAttribute targetType = do
    kind <- LLVM.getEnumAttributeKindForName "byval"
    LLVM.createTypeAttribute kind targetType

{- | Zero sized values should never appear in the generated LLVM code, but
we sometimes still need to register a value for a MIR variable, so we
use this dummy value that will be very visible if it does end up in the generated code
-}
zeroSizedDummyValue :: (?context :: LLVM.Context) => LLVM.Value
zeroSizedDummyValue = LLVM.constString "USE_OF_ZERO_SIZED_VALUE" LLVM.Don'tNullTerminate

{- NOTE [Closure Representation]:
Closures with payload representation `r` are *always* represented as products (FunctionPointer * r).

This means that functions operating on them can assume a simple 2-element product layout.

However, since every closure contains a payload, we need to do something slightly more clever for closures referring to top-level functions.
Currently, all closures have payloads of representation `Boxed` (although this will change), but in particular that means
that top-level closures have a non-empty (but unused) closure payload.
This means that we cannot use the actual function as the function pointer for the closure.
Instead, for every top-level function `f` we generate a wrapper function `f_closure` that takes an additional payload argument,
discards it and calls `f` with the remaining arguments.
-}
