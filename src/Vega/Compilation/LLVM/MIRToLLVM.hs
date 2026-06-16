{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}

module Vega.Compilation.LLVM.MIRToLLVM (compile, addMainFunction) where

import Relude hiding (State, evalState, get, modify, prettyCallStack, put, trace)

import Data.ByteString qualified as ByteString
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Data.Traversable (for)
import Data.Unique (hashUnique, newUnique)
import Data.Vector.Storable qualified as Storable
import Data.Vector.Strict qualified as Strict
import Effectful (Eff, IOE, (:>))
import Effectful.State.Static.Local (State, evalState, get, modify, put)
import GHC.Records (HasField, getField)
import GHC.TypeLits (Symbol)
import LLVM.Core qualified as LLVM
import LLVM.Core.Context qualified as LLVM
import LLVM.Core.Phi qualified as LLVM.Phi
import LLVM.InstructionBuilder qualified as LLVMBuilder
import System.IO.Unsafe (unsafePerformIO)
import Vega.Alignment (Alignment)
import Vega.Alignment qualified as Alignment
import Vega.Builtins (Primop (..))
import Vega.Builtins qualified as Builtins
import Vega.Compilation.Core.Syntax (Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.LLVM.AttributeFunctionType (AttributeFunctionType, addFunctionWithAttributes, attributeFunctionType, buildCallWithAttributes, parametersWithAttributes, rawFunctionType, returnTypeWithAttributes)
import Vega.Compilation.LLVM.AttributeFunctionType qualified as AttributeFunctionType
import Vega.Compilation.LLVM.Layout (Layout)
import Vega.Compilation.LLVM.Layout qualified as Layout
import Vega.Compilation.LLVM.Runtime (RuntimeDefinitions (..), declareRuntimeDefinitions)
import Vega.Compilation.LLVM.Runtime.Heap qualified as Heap
import Vega.Compilation.LLVM.Runtime.ToLLVMConstant (ToLLVMConstant (toLLVMConstant), size)
import Vega.Compilation.LLVM.Runtime.ToLLVMConstant qualified as ToLLVMConstant
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Debug (showHeadConstructor)
import Vega.Effect.Trace (Category (..), Trace, trace, withTrace)
import Vega.Panic (panic, prettyCallStack)
import Vega.Pretty (pretty)
import Vega.Pretty qualified as Pretty
import Vega.Syntax (renderPackageName)
import Vega.Syntax qualified as Vega
import Vega.Util (Sign (..), forIndexed_, viaList, type (?))
import Vega.Util qualified as Util
import Witherable qualified

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
    , Trace :> es
    )

{-# SCC compile #-}
compile :: (?context :: LLVM.Context, IOE :> es, Trace :> es) => MIR.Program -> LLVM.Module -> Eff es ()
compile program module_ = do
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

addMainFunction :: (?context :: LLVM.Context, IOE :> es) => Vega.GlobalName -> LLVM.Module -> Eff es ()
addMainFunction entryPoint module_ = do
    main <- LLVM.addFunction module_ "main" (LLVM.functionType [] LLVM.int32Type False)
    LLVM.setFunctionCallConv main LLVM.ccallConv

    builder <- LLVMBuilder.createBuilder
    initialBlock <- LLVM.appendBasicBlock main ""
    LLVMBuilder.positionBuilderAtEnd builder initialBlock

    entryPointFunction <-
        LLVM.getNamedFunction module_ (renderLLVMName entryPoint) >>= \case
            Nothing -> panic $ "Entry point not found: " <> Vega.prettyGlobal Vega.VarKind entryPoint
            Just entryPointFunction -> pure entryPointFunction
    callInstruction <- LLVMBuilder.buildCall builder (LLVM.functionType [] LLVM.voidType False) entryPointFunction [] ""
    LLVM.setInstructionCallConv callInstruction LLVM.tailCallConv
    _ <- LLVMBuilder.buildRet builder (LLVM.constInt LLVM.int32Type 0 False)
    pure ()

functionLLVMType ::
    (?context :: LLVM.Context, IOE :> es) =>
    Seq Layout ->
    Layout ->
    Eff es (AttributeFunctionType, "sretParameter" ? Maybe (Int, Layout))
functionLLVMType parameters returnLayout = do
    let baseParameterTypes = Witherable.mapMaybe Layout.llvmParameterType parameters

    (parameterTypes, returnType, usesSRet) <- case Layout.kind returnLayout of
        Layout.AggregatePointer -> do
            -- If we return a complex (AggregatePointer) value, we can't return it directly
            -- but instead we need to assign it to an sret parameter. This always needs to be the *first* parameter.
            --
            -- TODO: alignment?
            sretAttribute <- sretAttribute (Layout.llvmType returnLayout)
            alignmentAttribute <- alignAttribute (Layout.alignment returnLayout)
            pure ((LLVM.pointerType, [sretAttribute, alignmentAttribute]) :<| baseParameterTypes, LLVM.voidType, True)
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

        (functionTypeWithAttributes, _sret) <- functionLLVMType parameterLayouts returnLayout
        function <- addFunctionWithAttributes ?module_ (renderLLVMName name) functionTypeWithAttributes
        LLVM.setFunctionCallConv function LLVM.tailCallConv
        LLVM.setGC function "statepoint-example"

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

        let arguments = Storable.generate (Strict.length parameters) \i -> LLVM.getParam closureWrapper i
        result <- buildCallWithAttributes builder functionTypeWithAttributes function arguments ""
        LLVM.setTailCallKind result LLVM.TailCallKindTail
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
    MIR.DefineExternalFunction{name, externalName, parameterRepresentations, returnRepresentation} -> do
        externalParameterTypes <- for parameterRepresentations externalTypeForRepresentation
        externalReturnType <- externalTypeForRepresentation returnRepresentation
        let externalFunctionType = attributeFunctionType (viaList (fmap (\parameter -> (parameter, [])) externalParameterTypes)) (externalReturnType, [])

        -- We declare the actual external function first
        externalFunction <-
            LLVM.getNamedFunction ?module_ externalName >>= \case
                -- TODO: we should really check that both declarations use the same type here and throw an error if not
                Just previouslyDefinedFunction -> pure previouslyDefinedFunction
                Nothing -> do
                    externalFunction <- addFunctionWithAttributes ?module_ externalName externalFunctionType
                    LLVM.setFunctionCallConv externalFunction LLVM.ccallConv
                    pure externalFunction

        -- And then we define the vega wrapper that converts arguments as necessary
        parameterLayouts <- for parameterRepresentations Layout.representationLayout
        returnLayout <- Layout.representationLayout returnRepresentation
        (internalFunctionType, _sret) <- functionLLVMType parameterLayouts returnLayout

        wrapperFunction <- addFunctionWithAttributes ?module_ (renderLLVMName name) internalFunctionType
        LLVM.setFunctionCallConv wrapperFunction LLVM.tailCallConv

        block <- LLVM.appendBasicBlock wrapperFunction ""

        builder <- LLVMBuilder.createBuilder
        LLVMBuilder.positionBuilderAtEnd builder block

        result <- buildCallWithAttributes builder externalFunctionType externalFunction (viaList $ Seq.mapWithIndex (\i _ -> LLVM.getParam wrapperFunction i) parameterLayouts) ""
        case Layout.kind returnLayout of
            Layout.AggregatePointer -> undefined
            Layout.ZeroSized -> do
                _ <- LLVMBuilder.buildRetVoid builder
                pure ()
            Layout.LLVMScalar _ -> do
                _ <- LLVMBuilder.buildRet builder result
                pure ()

compileDeclaration ::
    ( ?context :: LLVM.Context
    , ?module_ :: LLVM.Module
    , ?runtimeDefinitions :: RuntimeDefinitions
    , IOE :> es
    , Trace :> es
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
            parameterLayouts <- for parameters \(_, representation) -> Layout.representationLayout representation
            returnLayout <- Layout.representationLayout returnRepresentation
            (_functionType, sretParameter) <- functionLLVMType parameterLayouts returnLayout

            function <-
                LLVM.getNamedFunction ?module_ (renderLLVMName name) >>= \case
                    Nothing -> panic $ "Unable to access function '" <> Vega.prettyGlobal Vega.VarKind name <> "' that should have been forward-declared."
                    Just function_ -> pure function_
            let ?function = function
            let ?functionEnv =
                    MkFunctionEnv
                        { sretVariable =
                            case sretParameter of
                                Just (position, returnLayout) -> Just (LLVM.getParam function position, returnLayout)
                                Nothing -> Nothing
                        }

            let isZeroSized layout = case Layout.kind layout of
                    Layout.ZeroSized -> True
                    _ -> False
            let (zeroSizedParameters, realParameters) = Seq.partition (isZeroSized . snd) (Seq.zip parameters parameterLayouts)
            for_ zeroSizedParameters \((variable, _), layout) -> do
                insertVarMapping variable zeroSizedDummyValue layout
            forIndexed_ realParameters \((variable, _representation), layout) index -> do
                let llvmValue = case sretParameter of
                        Nothing -> LLVM.getParam function index
                        -- The sret parameter is always the first one so we need to skip it
                        Just{} -> LLVM.getParam function (index + 1)
                insertVarMapping variable llvmValue layout

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
                                        Nothing -> panic $ "Unknown block descriptor: " <> pretty descriptor <> " in function " <> Vega.prettyGlobal Vega.VarKind name
                                        Just block -> block
                                compileRegisteredBlock builder descriptor block
                            go
            go
    MIR.DefineExternalFunction{} -> do
        -- We already defined everything for this in the forward declaration pass
        pure ()

compileRegisteredBlock :: (Compile es) => LLVMBuilder.Builder -> MIR.BlockDescriptor -> MIR.Block -> Eff es ()
compileRegisteredBlock builder descriptor block = do
    MkDeclarationState{registeredBlocks} <- get
    let llvmBlock = case HashMap.lookup descriptor registeredBlocks of
            Nothing -> panic $ "compileRegisteredBlock: Trying to compile unregistered MIR block " <> pretty descriptor
            Just llvmBlock -> llvmBlock
    LLVMBuilder.positionBuilderAtEnd builder llvmBlock
    phis <- readIORef block.phis
    compilePhis builder phis
    for_ block.instructions (compileInstruction builder)
    compileTerminator builder block.terminator

compilePhis :: (Compile es) => LLVMBuilder.Builder -> MIR.Phis -> Eff es ()
compilePhis builder (MIR.MkPhis phis) = do
    for_ (HashMap.toList phis) \(targetVar, (representation, incoming)) -> do
        incomingValues <-
            fromList <$> for (HashMap.toList incoming) \(block, variable) -> do
                (value, _) <- lookupVar variable
                block <- lookupBlock block
                pure (value, block)
        layout <- Layout.representationLayout representation
        case Layout.kind layout of
            Layout.ZeroSized -> pure ()
            Layout.LLVMScalar _; Layout.AggregatePointer -> do
                asVar_ targetVar layout $ LLVMBuilder.buildPhi builder (Layout.llvmType layout) incomingValues

compileInstruction :: (Compile es) => LLVMBuilder.Builder -> MIR.Instruction -> Eff es ()
compileInstruction builder = \case
    MIR.Identity var target -> do
        (targetValue, targetLayout) <- lookupVar target
        insertVarMapping var targetValue targetLayout
    MIR.ArithmeticOperator var operator -> do
        (value, layout) <- compileArithmeticOperator builder operator (renderVariable var)
        insertVarMapping var value layout
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
            Layout.LLVMScalar{} -> panic "Trying to construct an LLVM scalar from a product constructor"
            Layout.AggregatePointer -> do
                productPointer <- asVar var layout $ buildLayoutAlloca builder layout
                forIndexed_ llvmValues \value index -> do
                    let (offset, subLayout) = Layout.productOffsetAndLayout index layout
                    pointer <- case offset of
                        0 -> pure productPointer
                        _ -> buildGEPOffset builder productPointer offset ""
                    buildComplexStore builder subLayout value pointer
    MIR.SumConstructor{var, tag, payload, representation} -> do
        (value, _) <- lookupVar payload
        layout <- Layout.representationLayout representation

        sumPointer <- asVar var layout $ buildLayoutAlloca builder layout

        let tagLLVMType = LLVM.intType (Layout.sumTagSizeInBits layout)
        let tagValue = LLVM.constInt tagLLVMType (fromIntegral tag) False
        case Layout.sumTagOffset layout of
            Nothing -> do
                -- This sum is directly represented by its tag
                insertVarMapping var tagValue layout
            Just tagOffset -> do
                -- Store the tag
                tagPointer <- buildGEPOffset builder sumPointer tagOffset ""
                _ <- LLVMBuilder.buildStore builder tagValue tagPointer

                -- Storing the payload currently involves a single contiguous copy. This may change in the future
                -- if we add support for non-contiguous payloads.
                -- See NOTE: [Sum tags] in Vega.Compilation.LLVM.Layout for details.
                let (payloadOffset, payloadLayout) = Layout.sumOffsetAndLayout tag layout

                payloadPointer <- buildGEPOffset builder sumPointer payloadOffset ""
                buildComplexStore builder payloadLayout value payloadPointer
    MIR.LoadFunctionPointer{var, functionName} -> do
        functionPointer <-
            LLVM.getNamedFunction ?module_ (renderLLVMName functionName) >>= \case
                Nothing -> panic $ "Trying to create closure for non-existent top-level function: " <> Vega.prettyGlobal Vega.VarKind functionName
                Just function_ -> pure function_
        insertVarMapping var functionPointer Layout.rawPointerLayout
    MIR.LoadGlobalClosure{var, functionName} -> do
        asVar_ var (Layout.closureLayout Layout.boxedLayout) $ buildClosure builder functionName Layout.boxedLayout LLVM.constNullPointer
    MIR.LoadGlobal{var, globalName, representation} -> undefined
    MIR.LoadIntLiteral{var, literal, sizeInBits}
        | sizeInBits `mod` 8 /= 0 -> panic "Int layouts with non-byte sizes are not supported yet"
        | otherwise -> do
            let sizeInBytes = sizeInBits `div` 8
            insertVarMapping var (LLVM.constInt (LLVM.intType sizeInBits) (fromIntegral literal) True) (Layout.intLayoutInBytes sizeInBytes)
    MIR.LoadByteArrayLiteral{var, bytes} -> do
        global <- createStaticByteArray bytes

        -- The vega pointer should point after the header object
        pointer <- buildGEPOffset builder (LLVM.globalAsValue global) Heap.headerSize "bytes"

        insertVarMapping var pointer Layout.byteArrayLayout
    MIR.LoadSumTag{var, sum} -> do
        (sumValue, sumLayout) <- lookupVar sum
        let tagLayout = Layout.intLayoutInBytes (Layout.sumTagSizeInBytes sumLayout)
        case Layout.sumTagOffset sumLayout of
            Just offset -> do
                tagPointer <- buildGEPOffset builder sumValue offset "tagptr"
                asVar_ var tagLayout $ LLVMBuilder.buildLoad builder (Layout.llvmType tagLayout) tagPointer
            Nothing -> insertVarMapping var sumValue sumLayout
    MIR.CallDirect{var, functionName, arguments, representationArguments, returnRepresentation}
        | Just primop <- Builtins.asPrimop functionName -> do
            returnLayout <- Layout.representationLayout returnRepresentation
            asVar_ var returnLayout $ compilePrimopCall builder primop arguments representationArguments returnRepresentation
        | otherwise -> do
            let isNotZeroSized (_, layout) = case Layout.kind layout of
                    Layout.ZeroSized -> False
                    _ -> True
            (argumentValueSeq, argumentLayouts) <- Seq.unzip . Seq.filter isNotZeroSized <$> for arguments lookupVar
            let argumentValues = viaList argumentValueSeq
            returnLayout <- Layout.representationLayout returnRepresentation

            function <-
                LLVM.getNamedFunction ?module_ (renderLLVMName functionName) >>= \case
                    Nothing -> panic $ "Trying to generate call to non-existent function " <> pretty (Core.Global functionName)
                    Just function -> pure function

            (functionType, _) <- functionLLVMType argumentLayouts returnLayout

            callInstr <- case Layout.kind returnLayout of
                Layout.ZeroSized -> do
                    insertVarMapping var zeroSizedDummyValue returnLayout
                    buildCallWithAttributes builder functionType function argumentValues ""
                Layout.LLVMScalar _ -> asVar var returnLayout $ buildCallWithAttributes builder functionType function argumentValues
                Layout.AggregatePointer -> do
                    returnPointer <- asVar var returnLayout $ buildLayoutAlloca builder returnLayout
                    -- The sret parameter is always the first parameter
                    buildCallWithAttributes builder functionType function ([returnPointer] <> argumentValues) ""
            LLVM.setInstructionCallConv callInstr LLVM.tailCallConv
    MIR.CallClosure{var, closure, arguments, returnRepresentation} -> do
        (closureValue, closureLayout) <- lookupVar closure
        let (functionPointerOffset, _functionPointerLayout) = Layout.productOffsetAndLayout 0 closureLayout
        pointerToFunctionPointer <- buildGEPOffset builder closureValue functionPointerOffset ""
        functionPointer <- LLVMBuilder.buildLoad builder LLVM.pointerType pointerToFunctionPointer ""

        let (payloadOffset, payloadLayout) = Layout.productOffsetAndLayout 1 closureLayout
        pointerToPayload <- buildGEPOffset builder closureValue payloadOffset ""
        payload <- buildLoadOrKeepPointer builder payloadLayout pointerToPayload "payload"

        let isNotZeroSized (_, layout) = case Layout.kind layout of
                Layout.ZeroSized -> False
                _ -> True
        (argumentValuesWithoutPayload, argumentLayoutsWithoutPayload) <- Seq.unzip . Seq.filter isNotZeroSized <$> for arguments lookupVar

        let argumentLayouts = viaList $ argumentLayoutsWithoutPayload <> [Layout.boxedLayout]

        returnLayout <- Layout.representationLayout returnRepresentation

        (closureFunctionType, _) <- functionLLVMType argumentLayouts returnLayout

        case Layout.kind returnLayout of
            Layout.ZeroSized -> do
                callInstr <-
                    buildCallWithAttributes
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
                        buildCallWithAttributes
                            builder
                            closureFunctionType
                            functionPointer
                            (viaList $ argumentValuesWithoutPayload <> [payload])
                LLVM.setInstructionCallConv callInstr LLVM.tailCallConv
            Layout.AggregatePointer -> do
                returnPointer <- asVar var returnLayout $ buildLayoutAlloca builder returnLayout
                callInstr <-
                    buildCallWithAttributes
                        builder
                        closureFunctionType
                        functionPointer
                        (viaList $ [returnPointer] <> argumentValuesWithoutPayload <> [payload])
                        ""
                LLVM.setInstructionCallConv callInstr LLVM.tailCallConv

compileTerminator :: (Compile es) => LLVMBuilder.Builder -> MIR.Terminator -> Eff es ()
compileTerminator builder = \case
    MIR.Return variable -> do
        (value, layout) <- lookupVar variable

        buildComplexReturn builder layout value
    MIR.SwitchInt scrutinee alternatives default_ -> do
        (scrutineeValue, layout) <- lookupVar scrutinee
        let llvmType = Layout.llvmType layout

        cases <-
            viaList <$> for alternatives \(int, target) -> do
                targetLLVMBlock <- registerNewBlock target
                pure (LLVM.constInt llvmType (fromIntegral int) False, targetLLVMBlock)

        defaultBlock <- case default_ of
            Just block -> registerNewBlock block
            Nothing -> newUnreachableBlock

        _ <- LLVMBuilder.buildSwitch builder scrutineeValue cases defaultBlock
        pure ()
    MIR.TailCallDirect{functionName, arguments, representationArguments, returnRepresentation}
        | Just primop <- Builtins.asPrimop functionName -> do
            resultLayout <- Layout.representationLayout returnRepresentation
            result <- compilePrimopCall builder primop arguments representationArguments returnRepresentation "ret"
            buildComplexReturn builder resultLayout result
        | otherwise -> do
            let isNotZeroSized (_, layout) = case Layout.kind layout of
                    Layout.ZeroSized -> False
                    _ -> True
            (argumentValueSeq, argumentLayouts) <- Seq.unzip . Seq.filter isNotZeroSized <$> for arguments lookupVar
            let argumentValues = viaList argumentValueSeq
            returnLayout <- Layout.representationLayout returnRepresentation

            function <-
                LLVM.getNamedFunction ?module_ (renderLLVMName functionName) >>= \case
                    Nothing -> panic $ "Trying to generate call to non-existent function " <> pretty (Core.Global functionName)
                    Just function -> pure function

            (functionType, _) <- functionLLVMType argumentLayouts returnLayout

            callInstr <- case Layout.kind returnLayout of
                Layout.ZeroSized -> do
                    callInstr <- buildCallWithAttributes builder functionType function argumentValues ""
                    _ <- LLVMBuilder.buildRetVoid builder
                    pure callInstr
                Layout.LLVMScalar _ -> do
                    result <- buildCallWithAttributes builder functionType function argumentValues "ret"
                    _ <- LLVMBuilder.buildRet builder result
                    pure result
                Layout.AggregatePointer -> do
                    let sretPointer = case ?functionEnv.sretVariable of
                            Nothing -> panic "Trying to return AggregatePointer from function without sret variable"
                            Just (variable, _) -> variable

                    callInstr <- buildCallWithAttributes builder functionType function ([sretPointer] <> argumentValues) ""
                    _ <- LLVMBuilder.buildRetVoid builder
                    pure callInstr
            LLVM.setTailCallKind callInstr LLVM.TailCallKindTail
            LLVM.setInstructionCallConv callInstr LLVM.tailCallConv
    MIR.Jump targetBlock -> do
        targetLLVMBlock <- registerNewBlock targetBlock
        _ <- LLVMBuilder.buildBr builder targetLLVMBlock
        pure ()
    MIR.Unreachable -> do
        _ <- LLVMBuilder.buildUnreachable builder
        pure ()
    MIR.TailCallClosure{closure, arguments, returnRepresentation} -> do
        (closureValue, closureLayout) <- lookupVar closure
        let (functionPointerOffset, _functionPointerLayout) = Layout.productOffsetAndLayout 0 closureLayout
        pointerToFunctionPointer <- buildGEPOffset builder closureValue functionPointerOffset ""
        functionPointer <- LLVMBuilder.buildLoad builder LLVM.pointerType pointerToFunctionPointer ""

        let (payloadOffset, payloadLayout) = Layout.productOffsetAndLayout 1 closureLayout
        pointerToPayload <- buildGEPOffset builder closureValue payloadOffset ""
        payload <- buildLoadOrKeepPointer builder payloadLayout pointerToPayload "payload"

        let isNotZeroSized (_, layout) = case Layout.kind layout of
                Layout.ZeroSized -> False
                _ -> True
        (argumentValuesWithoutPayload, argumentLayoutsWithoutPayload) <- Seq.unzip . Seq.filter isNotZeroSized <$> for arguments lookupVar

        let argumentLayouts = viaList $ argumentLayoutsWithoutPayload <> [Layout.boxedLayout]

        returnLayout <- Layout.representationLayout returnRepresentation

        (closureFunctionType, _) <- functionLLVMType argumentLayouts returnLayout

        callInstr <- case Layout.kind returnLayout of
            Layout.ZeroSized -> do
                callInstr <-
                    buildCallWithAttributes
                        builder
                        closureFunctionType
                        functionPointer
                        (viaList $ argumentValuesWithoutPayload <> [payload])
                        ""
                _ <- LLVMBuilder.buildRetVoid builder
                pure callInstr
            Layout.LLVMScalar _ -> do
                result <-
                    buildCallWithAttributes
                        builder
                        closureFunctionType
                        functionPointer
                        (viaList $ argumentValuesWithoutPayload <> [payload])
                        "ret"
                _ <- LLVMBuilder.buildRet builder result
                pure result
            Layout.AggregatePointer -> do
                let sretPointer = case ?functionEnv.sretVariable of
                        Nothing -> panic "Trying to return AggregatePointer from function without sret variable"
                        Just (variable, _) -> variable

                callInstr <-
                    buildCallWithAttributes
                        builder
                        closureFunctionType
                        functionPointer
                        (viaList $ [sretPointer] <> argumentValuesWithoutPayload <> [payload])
                        ""
                _ <- LLVMBuilder.buildRetVoid builder
                pure callInstr
        LLVM.setTailCallKind callInstr LLVM.TailCallKindTail
        LLVM.setInstructionCallConv callInstr LLVM.tailCallConv

externalTypeForRepresentation :: (?context :: LLVM.Context) => Representation -> Eff es LLVM.Type
externalTypeForRepresentation representation = case representation of
    -- This is a vega boolean
    Core.SumRep [Core.ProductRep [], Core.ProductRep []] -> pure LLVM.int1Type
    Core.ProductRep [] -> pure LLVM.voidType
    Core.PrimitiveRep primitive -> case primitive of
        Vega.PointerRep -> pure LLVM.pointerType
        Vega.IntRep{sizeInBits} -> pure (LLVM.intType sizeInBits)
        Vega.DoubleRep -> pure LLVM.doubleType
        Vega.BoxedRep -> invalidRepresentation
    Core.ProductRep{} -> invalidRepresentation
    Core.SumRep{} -> invalidRepresentation
    Core.ArrayRep{} -> invalidRepresentation
    Core.ParameterRep{} -> invalidRepresentation
  where
    invalidRepresentation = panic $ "Invalid representation for external type: " <> pretty representation
compilePrimopCall ::
    (Compile es) =>
    LLVMBuilder.Builder ->
    Primop ->
    Seq MIR.Variable ->
    Seq Representation ->
    Representation ->
    Text ->
    Eff es LLVM.Value
compilePrimopCall builder primop arguments representationArguments returnRepresentation varName = do
    argumentValues <- for arguments lookupVarValue
    case primop of
        ReplicateMutableArray -> compileReplicateArray builder arguments returnRepresentation varName
        UnsafeUninitializedMutableArray -> compileUnsafeUninitializedMutableArray builder arguments representationArguments returnRepresentation varName
        EmptyArray -> do
            global <- createStaticByteArray mempty
            buildGEPOffset builder (LLVM.globalAsValue global) Heap.headerSize varName
        UnsafeReadArray -> compileUnsafeReadArray builder arguments returnRepresentation varName
        UnsafeReadMutableArray -> compileUnsafeReadArray builder arguments returnRepresentation varName
        UnsafeWriteMutableArray -> compileUnsafeWriteArray builder arguments returnRepresentation varName
        ArrayLength -> compileArrayLength builder arguments returnRepresentation varName
        MutableArrayLength -> compileArrayLength builder arguments returnRepresentation varName
        UnsafeArrayContents -> compileUnsafeArrayContents builder arguments returnRepresentation varName
        UnsafeFreezeArray -> compileUnsafeFreezeArray builder arguments returnRepresentation varName
        UnsafeThawArray -> compileUnsafeThawArray builder arguments returnRepresentation varName
        UnsafeMutableArrayContents -> compileUnsafeArrayContents builder arguments returnRepresentation varName
        NullPointer -> pure LLVM.constNullPointer
        OffsetPointerBytes -> compileOffsetPointerBytes builder arguments returnRepresentation varName
        CodePoints -> undefined
        Int8ToInt -> compileIntConversion Signed 64 builder arguments returnRepresentation varName
        UInt8ToInt -> compileIntConversion Unsigned 64 builder arguments returnRepresentation varName
        Int16ToInt -> compileIntConversion Signed 64 builder arguments returnRepresentation varName
        UInt16ToInt -> compileIntConversion Unsigned 64 builder arguments returnRepresentation varName
        Int32ToInt -> compileIntConversion Signed 64 builder arguments returnRepresentation varName
        UInt32ToInt -> compileIntConversion Unsigned 64 builder arguments returnRepresentation varName
        UIntToInt -> identity
        IntToInt8 -> compileIntConversion Signed 8 builder arguments returnRepresentation varName
        IntToUInt8 -> compileIntConversion Unsigned 8 builder arguments returnRepresentation varName
        IntToInt16 -> compileIntConversion Signed 16 builder arguments returnRepresentation varName
        IntToUInt16 -> compileIntConversion Unsigned 16 builder arguments returnRepresentation varName
        IntToInt32 -> compileIntConversion Signed 32 builder arguments returnRepresentation varName
        IntToUInt32 -> compileIntConversion Unsigned 32 builder arguments returnRepresentation varName
        IntToUInt -> identity
        UnsafeRem -> compileUnsafeRem builder arguments returnRepresentation varName
        Errno -> outOfLineBuiltin builder "vega_errno" argumentValues returnRepresentation varName
        DebugInt -> outOfLineBuiltin builder "vega_debug_int" argumentValues returnRepresentation varName
        Panic -> undefined
        UnsafeCoerce -> identity
  where
    identity = case arguments of
        [argument] -> lookupVarValue argument
        _ -> panic $ "identity operation called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"
compileUnsafeReadArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es LLVM.Value
compileUnsafeReadArray builder arguments returnRepresentation varName = case arguments of
    [array, index] -> do
        valueLayout <- Layout.representationLayout returnRepresentation
        array <- lookupVarValue array
        index <- lookupVarValue index

        buildArrayLoad builder valueLayout array index varName
    _ -> panic $ "unsafeReadArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeWriteArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es LLVM.Value
compileUnsafeWriteArray builder arguments _returnRepresentation _varName = case arguments of
    [array, index, value] -> do
        array <- lookupVarValue array
        index <- lookupVarValue index
        (value, valueLayout) <- lookupVar value

        buildArrayStore builder valueLayout array index value
        pure zeroSizedDummyValue
    _ -> panic $ "unsafeReadArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileReplicateArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es LLVM.Value
compileReplicateArray builder arguments returnRepresentation varName = case arguments of
    [size, initialMIRValue] -> do
        sizeValue <- lookupVarValue size
        (initialValue, valueLayout) <- lookupVar initialMIRValue

        incomingBlock <- LLVMBuilder.getInsertBlock builder

        infoTable <- getOrCreateArrayInfoTablePointer False valueLayout

        array <- outOfLineBuiltin builder "vega_allocate_uninitialized_array" [infoTable, sizeValue] returnRepresentation varName
        loopBlock <- LLVM.appendBasicBlock ?function "replicate"
        completedBlock <- LLVM.appendBasicBlock ?function ""
        isZero <- LLVMBuilder.buildICmp builder LLVM.IntEQ sizeValue (LLVM.constInt LLVM.int64Type 0 False) "isZero"
        _ <- LLVMBuilder.buildCondBr builder isZero completedBlock loopBlock

        LLVMBuilder.positionBuilderAtEnd builder loopBlock

        index <- LLVMBuilder.buildPhi builder LLVM.int64Type [(LLVM.constInt LLVM.int64Type 0 False, incomingBlock)] "index"

        _ <- buildArrayStore builder valueLayout array index initialValue

        incremented <- LLVMBuilder.buildNUWAdd builder index (LLVM.constInt LLVM.int64Type 1 False) ""
        LLVM.Phi.addIncoming index [(incremented, loopBlock)]
        isInRange <- LLVMBuilder.buildICmp builder LLVM.IntULT incremented sizeValue ""
        _ <- LLVMBuilder.buildCondBr builder isInRange loopBlock completedBlock

        LLVMBuilder.positionBuilderAtEnd builder completedBlock
        pure array
    _ -> panic $ "replicateArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeUninitializedMutableArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Seq Representation -> Representation -> Text -> Eff es LLVM.Value
compileUnsafeUninitializedMutableArray builder arguments representationArguments returnRepresentation varName = case arguments of
    [size] -> do
        sizeValue <- lookupVarValue size
        elementRepresentation <- case representationArguments of
            [elementRepresentation] -> pure elementRepresentation
            _ -> panic $ "compileUnsafeUninitializedMutableArray called with incorrect number of representation arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty representationArguments) <> "]"
        elementLayout <- Layout.representationLayout elementRepresentation

        infoTable <- getOrCreateArrayInfoTablePointer False elementLayout

        array <- outOfLineBuiltin builder "vega_allocate_zero_initialized_array" [infoTable, sizeValue] returnRepresentation varName
        pure array
    _ -> panic $ "unsafeUninitializedMutableArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileArrayLength :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es LLVM.Value
compileArrayLength builder arguments _returnRepresentation varName = case arguments of
    [array] -> do
        array <- lookupVarValue array
        lengthPointer <- buildGEPOffset builder array Heap.arrayLengthOffset "lengthPtr"
        LLVMBuilder.buildLoad builder LLVM.int64Type lengthPointer varName
    _ -> panic $ "arrayLength called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeArrayContents :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es LLVM.Value
compileUnsafeArrayContents builder arguments _returnRepresentation varName = case arguments of
    [array] -> do
        -- TODO: this might need to do a bitcast to turn this into an *unmanaged* pointer once we track GC roots
        array <- lookupVarValue array
        buildGEPOffset builder array (Heap.arrayContentOffset) varName
    _ -> panic $ "unsafeReadArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileOffsetPointerBytes :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es LLVM.Value
compileOffsetPointerBytes builder arguments _returnRepresentation varName = case arguments of
    [pointer, offset] -> do
        pointer <- lookupVarValue pointer
        offset <- lookupVarValue offset
        LLVMBuilder.buildGetElementPtr builder LLVM.int8Type pointer [offset] varName
    _ -> panic $ "offsetPointerBytes called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeFreezeArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es LLVM.Value
compileUnsafeFreezeArray _builder arguments _returnRepresentation _varName = case arguments of
    [array] -> lookupVarValue array
    _ -> panic $ "unsafeFreezeArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeThawArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es LLVM.Value
compileUnsafeThawArray _builder arguments _returnRepresentation _varName = case arguments of
    [array] -> lookupVarValue array
    _ -> panic $ "unsafeThawArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileIntConversion ::
    (Compile es) =>
    Sign ->
    Int ->
    LLVMBuilder.Builder ->
    Seq MIR.Variable ->
    Representation ->
    Text ->
    Eff es LLVM.Value
compileIntConversion sign width builder arguments _returnRepresentation varName = case arguments of
    [value] -> do
        value <- lookupVarValue value
        let isSigned = case sign of
                Signed -> True
                Unsigned -> False

        LLVMBuilder.buildIntCast builder value (LLVM.intType width) isSigned varName
    _ -> panic $ "integer conversion primop called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeRem :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es LLVM.Value
compileUnsafeRem builder arguments _returnRepresentation varName = case arguments of
    [dividend, divisor] -> do
        dividend <- lookupVarValue dividend
        divisor <- lookupVarValue divisor
        LLVMBuilder.buildSRem builder dividend divisor varName
    _ -> panic $ "unsafeRem called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

{- | Generate a call to a builtin function that is defined in the rust runtime rather than inline
TODO: it might be nice to have out of line functions defined directly in LLVM IR with tailcc instead of
having to jump through ccc every time?
-}
outOfLineBuiltin ::
    (Compile es) =>
    LLVMBuilder.Builder ->
    forall (functionName :: Symbol) ->
    (HasField functionName RuntimeDefinitions (LLVM.Value, AttributeFunctionType)) =>
    Seq LLVM.Value ->
    Representation ->
    Text ->
    Eff es LLVM.Value
outOfLineBuiltin builder functionName arguments returnRepresentation varName = do
    let (llvmFunctionValue, llvmFunctionType) = getField @functionName ?runtimeDefinitions
    returnLayout <- Layout.representationLayout returnRepresentation

    buildCCCCall builder llvmFunctionType llvmFunctionValue (viaList arguments) returnLayout varName

buildCCCCall ::
    (Compile es) =>
    LLVMBuilder.Builder ->
    AttributeFunctionType ->
    LLVM.Value ->
    Storable.Vector LLVM.Value ->
    Layout ->
    Text ->
    Eff es LLVM.Value
buildCCCCall builder functionType functionValue arguments returnLayout varName = do
    (returnValue, callInstr) <- case Layout.kind returnLayout of
        Layout.ZeroSized -> do
            callInstr <- buildCallWithAttributes builder functionType functionValue arguments ""
            pure (zeroSizedDummyValue, callInstr)
        Layout.LLVMScalar _ -> do
            callInstr <- buildCallWithAttributes builder functionType functionValue arguments varName
            pure (callInstr, callInstr)
        Layout.AggregatePointer -> do
            returnPointer <- buildLayoutAlloca builder returnLayout varName
            -- The sret parameter is always the first parameter
            callInstr <- buildCallWithAttributes builder functionType functionValue ([returnPointer] <> arguments) ""
            pure (returnPointer, callInstr)
    -- This is technically not necessary since ccc is the default but it's nice to be explicit
    LLVM.setInstructionCallConv callInstr LLVM.ccallConv
    pure returnValue

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
                                    { sizeInBytes = fromIntegral (Layout.sizeInBytes layout)
                                    , -- TODO: fill this in properly
                                      boxedCount = 0
                                    }
                                )
                        }
            (infoTableLLVMType, infoTableConstant) <- toLLVMConstant infoTable

            llvmInfoTableGlobal <- LLVM.addGlobal ?module_ infoTableLLVMType identifier
            LLVM.setInitializer llvmInfoTableGlobal infoTableConstant
            pure (LLVM.globalAsValue llvmInfoTableGlobal)

getOrCreateArrayInfoTablePointer :: (Compile es) => Bool -> Layout -> Eff es LLVM.Value
getOrCreateArrayInfoTablePointer static elementLayout = do
    let identifier = "info_array_" <> Layout.identifier elementLayout
    LLVM.getNamedGlobal ?module_ identifier >>= \case
        Just global -> pure (LLVM.globalAsValue global)
        Nothing -> do
            let infoTable =
                    Heap.MkInfoTable
                        { objectType = if static then Heap.StaticArray else Heap.Array
                        , layout =
                            Heap.ArrayLayout
                                ( Heap.MkArrayLayout
                                    { elementStrideInBytes = fromIntegral $ Layout.strideInBytes elementLayout
                                    , -- TODO
                                      elementBoxedCount = 0
                                    }
                                )
                        }
            (infoTableLLVMType, infoTableConstant) <- toLLVMConstant infoTable

            llvmInfoTableGlobal <- LLVM.addGlobal ?module_ infoTableLLVMType identifier
            LLVM.setInitializer llvmInfoTableGlobal infoTableConstant
            pure (LLVM.globalAsValue llvmInfoTableGlobal)

{- | Create a static byte array object from a statically known constant.
This returns a pointer to the object header.
Uses as a boxed vega pointer need to offset it by 'Heap.headerSize'.
-}
createStaticByteArray :: (Compile es) => ByteString -> Eff es LLVM.Global
createStaticByteArray bytes = do
    infoTable <- getOrCreateArrayInfoTablePointer True (Layout.intLayoutInBytes 1)
    unique <- liftIO newUnique

    let arrayHeapType = LLVM.structType [LLVM.pointerType, LLVM.int64Type, LLVM.arrayType LLVM.int8Type (fromIntegral (ByteString.length bytes))] False
    global <- LLVM.addGlobal ?module_ arrayHeapType ("string_" <> show (hashUnique unique))
    structValue <-
        LLVM.constStructInContext
            [ infoTable
            , LLVM.constInt LLVM.int64Type (fromIntegral (ByteString.length bytes)) False
            , LLVM.constDataArray LLVM.int8Type bytes
            ]
            False
    LLVM.setInitializer global structValue
    pure global

buildRuntimeCall ::
    (Compile es) =>
    LLVMBuilder.Builder ->
    forall (name :: Symbol) ->
    (HasField name RuntimeDefinitions (LLVM.Value, AttributeFunctionType)) =>
    Storable.Vector LLVM.Value ->
    Text ->
    Eff es LLVM.Value
buildRuntimeCall builder name arguments varName = do
    let (function, functionType) = getField @name ?runtimeDefinitions
    buildCallWithAttributes builder functionType function arguments varName

buildClosure :: (Compile es) => LLVMBuilder.Builder -> Vega.GlobalName -> Layout -> LLVM.Value -> Text -> Eff es LLVM.Value
buildClosure builder functionName payloadLayout closureValue varName = do
    functionPointer <-
        -- We need to use the closure wrapper instead of the actual function here. See Note: [Closure Representation].
        LLVM.getNamedFunction ?module_ (closureWrapperNameForFunction functionName) >>= \case
            Nothing -> panic $ "Trying to create closure for non-existent top-level function: " <> Vega.prettyGlobal Vega.VarKind functionName
            Just function_ -> pure function_
    let combinedLayout = Layout.closureLayout payloadLayout
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
buildComplexStore builder layout value pointer = case Layout.kind layout of
    Layout.LLVMScalar _scalar -> do
        store <- LLVMBuilder.buildStore builder value pointer
        LLVM.setAlignment store (Alignment.toInt (Layout.alignment layout))
        pure ()
    Layout.AggregatePointer -> do
        let alignment = Alignment.toInt (Layout.alignment layout)
        let size = LLVM.constInt LLVM.int64Type (fromIntegral (Layout.sizeInBytes layout)) False
        _ <- LLVMBuilder.buildMemCpy builder pointer alignment value alignment size
        pure ()
    Layout.ZeroSized -> pure ()

buildArrayStore :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> LLVM.Value -> LLVM.Value -> Eff es ()
buildArrayStore builder layout array index value = case Layout.kind layout of
    Layout.LLVMScalar scalar -> do
        contents <- buildGEPOffset builder array Heap.arrayContentOffset "contents"
        pointer <- LLVMBuilder.buildGetElementPtr builder scalar contents [index] ""
        _ <- LLVMBuilder.buildStore builder value pointer
        pure ()
    Layout.AggregatePointer -> do
        contents <- buildGEPOffset builder array Heap.arrayContentOffset "contents"
        pointer <- LLVMBuilder.buildGetElementPtr builder (LLVM.arrayType LLVM.int8Type (fromIntegral (Layout.sizeInBytes layout))) contents [index] ""
        buildComplexStore builder layout value pointer
        pure ()
    Layout.ZeroSized -> pure ()

buildArrayLoad :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> LLVM.Value -> Text -> Eff es LLVM.Value
buildArrayLoad builder layout array index varName = case Layout.kind layout of
    Layout.LLVMScalar scalar -> do
        contents <- buildGEPOffset builder array Heap.arrayContentOffset "contents"
        pointer <- LLVMBuilder.buildGetElementPtr builder scalar contents [index] ""
        LLVMBuilder.buildLoad builder scalar pointer varName
    Layout.AggregatePointer -> do
        contents <- buildGEPOffset builder array Heap.arrayContentOffset "contents"
        pointer <- LLVMBuilder.buildGetElementPtr builder (LLVM.arrayType LLVM.int8Type (fromIntegral (Layout.sizeInBytes layout))) contents [index] ""
        buildComplexLoad builder layout pointer varName
    Layout.ZeroSized -> pure zeroSizedDummyValue

buildComplexReturn :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> Eff es ()
buildComplexReturn builder layout value = do
    case Layout.kind layout of
        Layout.ZeroSized -> do
            _ <- LLVMBuilder.buildRetVoid builder
            pure ()
        Layout.LLVMScalar _ -> do
            _ <- LLVMBuilder.buildRet builder value
            pure ()
        Layout.AggregatePointer -> do
            case ?functionEnv.sretVariable of
                Nothing -> panic $ "Trying to return AggregatePointer layout from a function without sret variable: " <> show layout
                Just (sretVariable, _) -> do
                    buildComplexStore builder layout value sretVariable
                    _ <- LLVMBuilder.buildRetVoid builder
                    pure ()

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
        let size = LLVM.constInt LLVM.int64Type (fromIntegral (Layout.sizeInBytes layout)) False
        _ <- LLVMBuilder.buildMemCpy builder localMemory alignment pointer alignment size
        pure localMemory
    Layout.ZeroSized -> pure zeroSizedDummyValue

{- | Build a @getelementptr@ instruction pointing at a constant offset given in bytes.
The offset is assumed to be in-bounds.
-}
buildGEPOffset :: (Compile es) => LLVMBuilder.Builder -> LLVM.Value -> Int -> Text -> Eff es LLVM.Value
buildGEPOffset builder pointer offset name = case offset of
    0 -> pure pointer
    _ -> LLVMBuilder.buildInBoundsGetElementPtr builder LLVM.int8Type pointer [LLVM.constInt LLVM.int64Type (fromIntegral offset) False] name

buildLayoutAlloca :: (Compile es) => LLVMBuilder.Builder -> Layout -> Text -> Eff es LLVM.Value
buildLayoutAlloca builder layout varName = do
    alloca <- LLVMBuilder.buildAlloca builder (Layout.llvmType layout) varName
    LLVM.setAlignment alloca (Alignment.toInt (Layout.alignment layout))
    pure alloca

registerNewBlock :: (Compile es) => MIR.BlockDescriptor -> Eff es LLVM.BasicBlock
registerNewBlock descriptor = do
    state <- get @DeclarationState
    case HashMap.lookup descriptor state.registeredBlocks of
        Just block -> pure block
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

closureWrapperNameForFunction :: Vega.GlobalName -> Text
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
renderLLVMName :: Vega.GlobalName -> Text
renderLLVMName name = "_vega_" <> renderPackageName name.moduleName.package <> "::" <> Text.intercalate "/" (toList (name.moduleName.subModules)) <> "::" <> name.name

sretAttribute :: (?context :: LLVM.Context, IOE :> es) => LLVM.Type -> Eff es LLVM.Attribute
sretAttribute targetType = do
    kind <- LLVM.getEnumAttributeKindForName "sret"
    LLVM.createTypeAttribute kind targetType

alignAttribute :: (?context :: LLVM.Context, IOE :> es) => Alignment -> Eff es LLVM.Attribute
alignAttribute alignment = do
    kind <- LLVM.getEnumAttributeKindForName "align"
    LLVM.createEnumAttribute kind (fromIntegral (Alignment.toInt alignment))

{- | Zero sized values should never appear in the generated LLVM code, but
we sometimes still need to register a value for a MIR variable, so we
use this dummy value that will be very visible if it does end up in the generated code
-}
zeroSizedDummyValue :: (?context :: LLVM.Context) => LLVM.Value
zeroSizedDummyValue = LLVM.constString "USE_OF_ZERO_SIZED_VALUE" LLVM.Don'tNullTerminate

compileArithmeticOperator :: (Compile es) => LLVMBuilder.Builder -> MIR.ArithmeticExpr -> Text -> Eff es (LLVM.Value, Layout)
compileArithmeticOperator builder arithmeticExpr varName = case arithmeticExpr of
    MIR.Add var1 var2 -> do
        (arg1, representation) <- lookupVar var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildAdd builder arg1 arg2 varName
        pure (result, representation)
    MIR.Subtract var1 var2 -> do
        (arg1, representation) <- lookupVar var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildSub builder arg1 arg2 varName
        pure (result, representation)
    MIR.Multiply var1 var2 -> do
        (arg1, representation) <- lookupVar var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildMul builder arg1 arg2 varName
        pure (result, representation)
    MIR.Divide var1 var2 -> do
        (arg1, representation) <- lookupVar var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildSDiv builder arg1 arg2 varName
        pure (result, representation)
    MIR.Less var1 var2 -> do
        arg1 <- lookupVarValue var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildICmp builder LLVM.IntSLT arg1 arg2 varName
        pure (result, Layout.boolLayout)
    MIR.LessEqual var1 var2 -> do
        arg1 <- lookupVarValue var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildICmp builder LLVM.IntSLE arg1 arg2 varName
        pure (result, Layout.boolLayout)
    MIR.Equal var1 var2 -> do
        arg1 <- lookupVarValue var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildICmp builder LLVM.IntEQ arg1 arg2 varName
        pure (result, Layout.boolLayout)
    MIR.NotEqual var1 var2 -> do
        arg1 <- lookupVarValue var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildICmp builder LLVM.IntNE arg1 arg2 varName
        pure (result, Layout.boolLayout)

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
