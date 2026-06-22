{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}

module Vega.Compilation.LLVM.MIRToLLVM (compile, addMainFunction) where

import Relude hiding (NonEmpty, State, evalState, get, modify, prettyCallStack, put, trace)

import Data.ByteString qualified as ByteString
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Data.Traversable (for)
import Data.Unique (hashUnique, newUnique)
import Data.Vector.Generic qualified as Vector
import Data.Vector.Storable qualified as Storable hiding ((!))
import Data.Vector.Strict qualified as Strict hiding ((!))
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
import Vega.Compilation.LLVM.Layout (CompoundValue (..), Layout)
import Vega.Compilation.LLVM.Layout qualified as Layout
import Vega.Compilation.LLVM.Runtime (RuntimeDefinitions (..), declareRuntimeDefinitions)
import Vega.Compilation.LLVM.Runtime.Heap qualified as Heap
import Vega.Compilation.LLVM.Runtime.ToLLVMConstant (ToLLVMConstant (toLLVMConstant), size)
import Vega.Compilation.LLVM.Runtime.ToLLVMConstant qualified as ToLLVMConstant
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Debug (showHeadConstructor)
import Vega.Effect.ST (STE, liftST, runSTE)
import Vega.Effect.Trace (Category (..), Trace, trace, withTrace)
import Vega.OutArray qualified as OutArray
import Vega.Panic (panic, prettyCallStack)
import Vega.Pretty (Ann, Doc, pretty)
import Vega.Pretty qualified as Pretty
import Vega.Seq.NonEmpty (NonEmpty ((:<||)), pattern NonEmpty)
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Size qualified as Size
import Vega.Syntax (renderPackageName)
import Vega.Syntax qualified as Vega
import Vega.Util (Sign (..), assert, forIndexed_, viaList, type (?))
import Vega.Util qualified as Util
import Witherable qualified

data DeclarationState = MkDeclarationState
    { registeredBlocks :: HashMap MIR.BlockDescriptor LLVM.BasicBlock
    , outstandingBlocks :: Seq MIR.BlockDescriptor
    , variableMappings :: HashMap MIR.Variable (Layout.CompoundValue, Layout)
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
compile :: (?context :: LLVM.Context, IOE :> es, Trace :> es) => MIR.Program -> Eff es LLVM.Module
compile program = do
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
    let baseParameterTypes = foldMap Layout.llvmParameters parameters

    (parameterTypes, returnType, usesSRet) <- case Layout.returnConvention returnLayout of
        Layout.Void -> pure (baseParameterTypes, LLVM.voidType, False)
        Layout.SingleBoxed -> pure (baseParameterTypes, LLVM.pointerType, False)
        Layout.SingleScalar scalar -> pure (baseParameterTypes, scalar, False)
        Layout.SRetPointer -> do
            let returnLLVMType = case Layout.atRestLLVMType returnLayout of
                    Nothing -> panic "Trying to return zero-sized layout via an sret pointer"
                    Just llvmType -> llvmType
            -- The sret parameter always has to be the first parameter
            sretAttribute <- sretAttribute returnLLVMType
            alignmentAttribute <- alignAttribute (Layout.alignment returnLayout)
            pure ((LLVM.pointerType, [sretAttribute, alignmentAttribute]) :<| baseParameterTypes, LLVM.voidType, True)
        Layout.ScalarStruct -> do
            assert (Size.inBits (Layout.unboxedSize returnLayout) == 0)
            pure (baseParameterTypes, Layout.scalarStructType returnLayout, False)

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

        case Layout.returnConvention returnLayout of
            Layout.Void; Layout.SRetPointer -> do
                _ <- LLVMBuilder.buildRetVoid builder
                pure ()
            Layout.SingleScalar _; Layout.SingleBoxed; Layout.ScalarStruct -> do
                _ <- LLVMBuilder.buildRet builder result
                pure ()
    MIR.DefineExternalFunction{name, externalName, parameterRepresentations, returnRepresentation} -> do
        externalParameterTypes <- for parameterRepresentations externalTypeForRepresentation
        externalReturnType <- externalTypeForRepresentation returnRepresentation
        let externalFunctionType = attributeFunctionType (viaList (fmap (\parameter -> (parameter, [])) externalParameterTypes)) (externalReturnType, [])

        -- We declare the actual external function first
        externalFunction <- addFunctionWithAttributes ?module_ externalName externalFunctionType
        LLVM.setFunctionCallConv externalFunction LLVM.ccallConv

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
        case Layout.returnConvention returnLayout of
            Layout.Void; Layout.SRetPointer -> do
                _ <- LLVMBuilder.buildRetVoid builder
                pure ()
            Layout.SingleScalar _; Layout.SingleBoxed; Layout.ScalarStruct -> do
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
            parametersWithLayouts <- for parameters \(parameter, representation) -> (parameter,) <$> Layout.representationLayout representation
            let parameterLayouts = fmap snd parametersWithLayouts
            returnLayout <- Layout.representationLayout returnRepresentation
            -- TODO: that's a bit of an inefficient way of getting the sret parameter...
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

            let addParameterMappings (currentIndex :: Int) = \case
                    Empty -> pure ()
                    (parameter, layout) :<| rest -> do
                        let unboxedPointer = case Layout.parameterUnboxedIndex layout of
                                Nothing -> Nothing
                                Just unboxedIndex -> Just (LLVM.getParam function (currentIndex + unboxedIndex))
                        value <- runSTE \s -> do
                            valueBuilder <- Layout.newBuilderWithUnboxedPointer @s layout unboxedPointer
                            for_ @[] [0 .. Layout.boxedCount layout - 1] \boxedIndex -> do
                                Layout.fillBoxed valueBuilder boxedIndex (LLVM.getParam function (currentIndex + Layout.parameterBoxedIndex layout boxedIndex))
                            forIndexed_ (Layout.decomposedScalars layout) \_scalar scalarIndex -> do
                                Layout.fillDecomposed valueBuilder scalarIndex (LLVM.getParam function (currentIndex + Layout.parameterDecomposedScalarIndex layout scalarIndex))
                            Layout.buildValue valueBuilder
                        insertVarMapping parameter value layout
                        addParameterMappings (currentIndex + Layout.parameterCount layout) rest

            let initialIndex = case sretParameter of
                    Nothing -> 0
                    -- The sret parameter is always the first parameter so our actual parameters start at 1
                    Just{} -> 1
            addParameterMappings initialIndex parametersWithLayouts

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
    compilePhis builder block.phis
    for_ block.instructions (compileInstruction builder)
    compileTerminator builder block.terminator

compilePhis :: (Compile es) => LLVMBuilder.Builder -> MIR.Phis -> Eff es ()
compilePhis builder (MIR.MkPhis phis) = do
    for_ (HashMap.toList phis) \(targetVar, (representation, incoming)) -> runSTE \s -> do
        incomingValues <-
            fromList @(Strict.Vector _) <$> for (HashMap.toList incoming) \(block, variable) -> do
                (value, _) <- lookupVar variable
                block <- lookupBlock block

                pure (value, block)
        layout <- Layout.representationLayout representation

        let varName = renderVariable targetVar
        unboxedSegment <- case Size.inBytes (Layout.unboxedSize layout) of
            0 -> pure Nothing
            size -> do
                let incoming =
                        incomingValues & fmap \(compound, block) -> case Layout.unboxedPointer compound of
                            Nothing -> panic "Compound value without unboxed pointer has a layout with a non-empty unboxed segment"
                            Just unboxedPointer -> (unboxedPointer, block)
                Just <$> LLVMBuilder.buildPhi builder (LLVM.arrayType LLVM.int8Type size) incoming (varName <> ".unboxed")
        valueBuilder <- Layout.newBuilderWithUnboxedPointer @s layout unboxedSegment

        for_ @[] [0 .. Layout.boxedCount layout - 1] \boxedIndex -> do
            let incoming = fmap (\(compound, block) -> (Layout.boxedValues compound Vector.! boxedIndex, block)) incomingValues
            boxedValue <- LLVMBuilder.buildPhi builder LLVM.pointerType incoming (varName <> ".boxed")
            Layout.fillBoxed valueBuilder boxedIndex boxedValue
            registerGCRoot boxedValue
        forIndexed_ (Layout.decomposedScalars layout) \type_ scalarIndex -> do
            let incoming = fmap (\(compound, block) -> (Layout.decomposedScalarValues compound Vector.! scalarIndex, block)) incomingValues
            scalarValue <- LLVMBuilder.buildPhi builder type_ incoming (varName <> ".scalar")
            Layout.fillDecomposed valueBuilder scalarIndex scalarValue

        targetCompoundValue <- Layout.buildValue valueBuilder
        insertVarMapping targetVar targetCompoundValue layout

compileInstruction :: (Compile es) => LLVMBuilder.Builder -> MIR.Instruction -> Eff es ()
compileInstruction builder = \case
    MIR.Identity var target -> do
        (targetValue, targetLayout) <- lookupVar target
        insertVarMapping var targetValue targetLayout
    MIR.ArithmeticOperator var operator -> do
        (value, layout) <- compileArithmeticOperator builder operator (renderVariable var)
        insertVarMapping var (Layout.scalarCompoundValue value) layout
    MIR.AccessField{var, path, target = parent, fieldRepresentation} -> runSTE \s -> do
        (parentValue, parentLayout) <- lookupVar parent
        fieldLayout <- Layout.representationLayout fieldRepresentation

        fieldBuilder <- Layout.newBuilder @s builder fieldLayout

        let basePath = Layout.elementPathFromMIRPath path
        Layout.forContainedElements fieldLayout \elementPath targetLocation -> do
            let sourceLocation = accessElementByPath (basePath <> elementPath) parentLayout
            copyElement builder sourceLocation parentValue targetLocation fieldLayout fieldBuilder
        fieldValue <- Layout.buildValue fieldBuilder
        insertVarMapping var fieldValue fieldLayout
    MIR.Box{var, target} -> do
        -- TODO: we should probably inline the fast path for minor heap allocations here
        (targetValue, targetLayout) <- lookupVar target

        layoutInfoTablePointer <- getOrCreateLayoutInfoTablePointer targetLayout

        memoryPointer <- buildRuntimeCall builder "vega_allocate_boxed" [layoutInfoTablePointer] (renderVariable var)
        let boxedCompoundValue = Layout.boxedCompoundValue memoryPointer
        insertVarMapping var boxedCompoundValue Layout.boxedLayout

        buildComplexStore builder targetLayout targetValue memoryPointer
    MIR.Unbox{var, boxedTarget, representation} -> do
        (targetValue, _) <- lookupVar boxedTarget
        layout <- Layout.representationLayout representation

        Util.assert (Vector.null (Layout.decomposedScalarValues targetValue))
        Util.assert (isNothing (Layout.unboxedPointer targetValue))
        case Layout.boxedValues targetValue of
            [pointerValue] -> asVar_ var layout $ buildComplexLoad builder layout pointerValue
            _ -> panic $ "Trying to unbox non-boxed compound value " <> pretty targetValue
    MIR.ProductConstructor{var, values, representation} -> runSTE \s -> do
        llvmValuesWithLayouts <- for values lookupVar
        layout <- Layout.representationLayout representation

        valueBuilder <- Layout.newBuilder @s builder layout

        Layout.forContainedElements layout \path targetLocation -> do
            case path of
                (Layout.ProductField index :<| sourcePath) -> do
                    let (sourceValue, sourceLayout) = llvmValuesWithLayouts `Seq.index` index
                    let sourceLocation = accessElementByPath sourcePath sourceLayout
                    copyElement builder sourceLocation sourceValue targetLocation layout valueBuilder
                _ -> panic $ "Element with non-ProductField path in product layout: " <> show path

        builtValue <- Layout.buildValue valueBuilder
        insertVarMapping var builtValue layout
    MIR.SumConstructor{var, tag, payload, representation} -> runSTE \s -> do
        (payload, payloadLayout) <- lookupVar payload
        layout <- Layout.representationLayout representation
        valueBuilder <- Layout.newBuilder @s builder layout

        let (tagLocation, tagSize) = case Layout.details layout of
                Layout.TopLevelSumLayout{tagSize, tagLocation} -> (tagLocation, tagSize)
                _ -> panic "Non-TopLevelSum layout in SumConstructor instruction"
        -- We currently round up the tag size to the nearest number of bytes here.
        -- This might change in the future, especially if we implement some form of
        -- niche filling optimization
        let tagValue = LLVM.constInt (LLVM.intType (Size.inBytes tagSize)) (fromIntegral tag) False
        fillLocation builder valueBuilder tagLocation tagValue

        Layout.forContainedElementsAtSumConstructorIndex tag layout \path targetLocation -> do
            let sourceLocation = accessElementByPath path payloadLayout
            copyElement builder sourceLocation payload targetLocation layout valueBuilder
        value <- Layout.buildValue valueBuilder
        insertVarMapping var value layout
    MIR.LoadFunctionPointer{var, functionName, asGlobalClosure, representationArguments} -> do
        assert (representationArguments == [])
        let llvmFunctionName = case asGlobalClosure of
                False -> renderLLVMName functionName
                True -> closureWrapperNameForFunction functionName
        functionPointer <-
            LLVM.getNamedFunction ?module_ llvmFunctionName >>= \case
                Nothing -> panic $ "Trying to create function pointer for non-existent function: " <> Vega.prettyGlobal Vega.VarKind functionName
                Just function_ -> pure function_
        insertVarMapping var (Layout.scalarCompoundValue functionPointer) Layout.rawPointerLayout
    MIR.LoadGlobal{var, globalName, representation} -> undefined
    MIR.LoadIntLiteral{var, literal, sizeInBits}
        | sizeInBits `mod` 8 /= 0 -> panic "Int layouts with non-byte sizes are not supported yet"
        | otherwise -> do
            let value = Layout.scalarCompoundValue (LLVM.constInt (LLVM.intType sizeInBits) (fromIntegral literal) True)
            insertVarMapping var value (Layout.intLayout (Size.fromBits sizeInBits))
    MIR.LoadByteArrayLiteral{var, bytes} -> do
        global <- createStaticByteArray bytes

        -- The vega pointer should point after the header object
        pointer <- buildGEPOffset builder (LLVM.globalAsValue global) Heap.headerSize "bytes"

        insertVarMapping var (Layout.boxedCompoundValue pointer) Layout.byteArrayLayout
    MIR.LoadSumTag{var, sum} -> do
        (sumValue, sumLayout) <- lookupVar sum
        let (tagSize, tagLocation) = case Layout.details sumLayout of
                Layout.Simple nested -> panic $ "Trying to load a sum tag from a non-sum and non-primitive layout: " <> showHeadConstructor nested
                Layout.TopLevelSumLayout{tagSize, tagLocation} -> (tagSize, tagLocation)

        let tagLayout = Layout.intLayout tagSize
        asVar_ var tagLayout $ accessLocation builder sumValue tagLayout tagLocation
    MIR.LoadBoxedNull{var} -> do
        insertVarMapping var (Layout.boxedCompoundValue (LLVM.constNullPointer)) Layout.boxedLayout
    MIR.CallDirect{var, functionName, arguments, representationArguments, returnRepresentation}
        | Just primop <- Builtins.asPrimop functionName -> do
            returnLayout <- Layout.representationLayout returnRepresentation
            asVar_ var returnLayout $ compilePrimopCall builder primop arguments representationArguments returnRepresentation
        | otherwise -> do
            argumentsWithLayouts <- for arguments lookupVar
            let (argumentValues, argumentLayouts) = Seq.unzip argumentsWithLayouts

            returnLayout <- Layout.representationLayout returnRepresentation

            function <-
                LLVM.getNamedFunction ?module_ (renderLLVMName functionName) >>= \case
                    Nothing -> panic $ "Trying to generate call to non-existent function " <> pretty (Core.Global functionName)
                    Just function -> pure function

            (functionType, _) <- functionLLVMType argumentLayouts returnLayout

            compileNonTailCall builder var returnLayout functionType function argumentValues
    MIR.CallClosure{var, closure, arguments, returnRepresentation} -> do
        (closureValue, closureLayout) <- lookupVar closure

        functionPointer <- Layout.assertScalar <$> accessLocation builder closureValue closureLayout Layout.closureFunctionPointer "functionPointer"
        payload <- accessLocation builder closureValue closureLayout Layout.closurePayload "payload"

        baseArgumentsWithLayouts <- for arguments lookupVar
        let (baseArguments, baseArgumentLayouts) = Seq.unzip baseArgumentsWithLayouts

        let argumentLayouts = viaList $ baseArgumentLayouts <> [Layout.boxedLayout]

        returnLayout <- Layout.representationLayout returnRepresentation

        (closureFunctionType, _) <- functionLLVMType argumentLayouts returnLayout

        let arguments = baseArguments <> [payload]

        compileNonTailCall builder var returnLayout closureFunctionType functionPointer arguments

compileTerminator :: (Compile es) => LLVMBuilder.Builder -> MIR.Terminator -> Eff es ()
compileTerminator builder = \case
    MIR.Return variable -> do
        (value, layout) <- lookupVar variable

        buildComplexReturn builder layout value
    MIR.SwitchInt scrutinee alternatives default_ -> do
        scrutineeValue <- Layout.assertScalar <$> lookupVarValue scrutinee
        let scrutineeType = LLVM.typeOf scrutineeValue

        cases <-
            viaList <$> for alternatives \(int, target) -> do
                targetLLVMBlock <- registerNewBlock target
                pure (LLVM.constInt scrutineeType (fromIntegral int) False, targetLLVMBlock)

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
            argumentsWithLayouts <- for arguments lookupVar
            let (argumentCompounds, argumentLayouts) = Seq.unzip argumentsWithLayouts

            returnLayout <- Layout.representationLayout returnRepresentation

            function <-
                LLVM.getNamedFunction ?module_ (renderLLVMName functionName) >>= \case
                    Nothing -> panic $ "Trying to generate call to non-existent function " <> pretty (Core.Global functionName)
                    Just function -> pure function

            (functionType, _) <- functionLLVMType argumentLayouts returnLayout

            compileTailCall builder returnLayout functionType function argumentCompounds
    MIR.Jump targetBlock -> do
        targetLLVMBlock <- registerNewBlock targetBlock
        _ <- LLVMBuilder.buildBr builder targetLLVMBlock
        pure ()
    MIR.Unreachable -> do
        _ <- LLVMBuilder.buildUnreachable builder
        pure ()
    MIR.TailCallClosure{closure, arguments, returnRepresentation} -> do
        (closureValue, closureLayout) <- lookupVar closure

        functionPointer <- Layout.assertScalar <$> accessLocation builder closureValue closureLayout Layout.closureFunctionPointer "functionPointer"
        payload <- accessLocation builder closureValue closureLayout Layout.closurePayload "payload"

        baseArgumentsWithLayouts <- for arguments lookupVar
        let (baseArguments, baseArgumentLayouts) = Seq.unzip baseArgumentsWithLayouts

        let argumentLayouts = viaList $ baseArgumentLayouts <> [Layout.boxedLayout]

        returnLayout <- Layout.representationLayout returnRepresentation

        (closureFunctionType, _) <- functionLLVMType argumentLayouts returnLayout

        let arguments = baseArguments <> [payload]

        compileTailCall builder returnLayout closureFunctionType functionPointer arguments

compileNonTailCall ::
    (Compile es) =>
    LLVMBuilder.Builder ->
    MIR.Variable ->
    Layout ->
    AttributeFunctionType ->
    LLVM.Value ->
    Seq CompoundValue ->
    Eff es ()
compileNonTailCall builder var returnLayout functionType function argumentCompounds = do
    let argumentValues = viaList $ foldMap Layout.compoundAsFunctionArguments argumentCompounds
    callInstr <- case Layout.returnConvention returnLayout of
        Layout.Void -> do
            insertVarMapping var Layout.unitCompoundValue returnLayout
            buildCallWithAttributes builder functionType function argumentValues ""
        Layout.SingleScalar _ -> do
            result <- buildCallWithAttributes builder functionType function argumentValues (renderVariable var)
            insertVarMapping var (Layout.scalarCompoundValue result) returnLayout
            pure result
        Layout.SingleBoxed -> do
            result <- buildCallWithAttributes builder functionType function argumentValues (renderVariable var)
            insertVarMapping var (Layout.boxedCompoundValue result) returnLayout
            pure result
        Layout.ScalarStruct -> do
            struct <- buildCallWithAttributes builder functionType function argumentValues (renderVariable var)
            asVar_ var returnLayout $ deconstructScalarStruct builder returnLayout struct
            pure struct
        Layout.SRetPointer -> do
            -- sret pointers return a value *at rest* so we first need to store this value in an alloca
            -- (and we *cannot* use the automatic CompoundValueBuilder alloca since that is used for values
            -- in-flight and will only allocate for the unboxed segment)
            returnedValueAtRestPointer <- Layout.buildAtRestAlloca builder returnLayout "sret"
            -- The sret parameter is always the first parameter
            callInstr <- buildCallWithAttributes builder functionType function ([returnedValueAtRestPointer] <> argumentValues) ""

            -- We can keep the alloca for the unboxed segment here since it's gointo hg ave the exact same lifetime as the loaded value anyway
            asVar_ var returnLayout $ buildLoadAsReference builder returnLayout returnedValueAtRestPointer

            pure callInstr
    LLVM.setInstructionCallConv callInstr LLVM.tailCallConv

compileTailCall ::
    (Compile es) =>
    LLVMBuilder.Builder ->
    Layout ->
    AttributeFunctionType ->
    LLVM.Value ->
    Seq CompoundValue ->
    Eff es ()
compileTailCall builder returnLayout functionType function argumentCompounds = do
    let argumentValues = viaList $ foldMap Layout.compoundAsFunctionArguments argumentCompounds
    callInstr <- case Layout.returnConvention returnLayout of
        Layout.Void -> do
            callInstr <- buildCallWithAttributes builder functionType function argumentValues ""
            _ <- LLVMBuilder.buildRetVoid builder
            pure callInstr
        Layout.SingleScalar _
        Layout.SingleBoxed
        Layout.ScalarStruct -> do
                result <- buildCallWithAttributes builder functionType function argumentValues "ret"
                _ <- LLVMBuilder.buildRet builder result
                pure result
        Layout.SRetPointer -> do
            let sretPointer = case ?functionEnv.sretVariable of
                    Nothing -> panic "Trying to return via SRretPointer from function without sret variable"
                    Just (variable, _) -> variable

            callInstr <- buildCallWithAttributes builder functionType function ([sretPointer] <> argumentValues) ""
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
    Eff es CompoundValue
compilePrimopCall builder primop arguments representationArguments returnRepresentation varName = do
    argumentValues <- for arguments lookupVarValue
    let ~simpleArgumentValues = fmap Layout.assertSingleValue argumentValues
    case primop of
        ReplicateMutableArray -> compileReplicateArray builder arguments returnRepresentation varName
        UnsafeUninitializedMutableArray -> compileUnsafeUninitializedMutableArray builder arguments representationArguments returnRepresentation varName
        EmptyArray -> do
            -- TODO: it's a bit silly to re-create a new array here every time
            global <- createStaticByteArray mempty
            Layout.boxedCompoundValue <$> buildGEPOffset builder (LLVM.globalAsValue global) Heap.headerSize varName
        UnsafeReadArray -> compileUnsafeReadArray builder arguments returnRepresentation varName
        UnsafeReadMutableArray -> compileUnsafeReadArray builder arguments returnRepresentation varName
        UnsafeWriteMutableArray -> compileUnsafeWriteArray builder arguments returnRepresentation varName
        ArrayLength -> compileArrayLength builder arguments returnRepresentation varName
        MutableArrayLength -> compileArrayLength builder arguments returnRepresentation varName
        UnsafeArrayContents -> compileUnsafeArrayContents builder arguments returnRepresentation varName
        UnsafeFreezeArray -> compileUnsafeFreezeArray builder arguments returnRepresentation varName
        UnsafeThawArray -> compileUnsafeThawArray builder arguments returnRepresentation varName
        UnsafeMutableArrayContents -> compileUnsafeArrayContents builder arguments returnRepresentation varName
        NullPointer -> pure $ Layout.scalarCompoundValue LLVM.constNullPointer
        OffsetPointerBytes -> compileOffsetPointerBytes builder arguments returnRepresentation varName
        CodePoints -> undefined
        Int8ToInt -> compileIntConversion Signed 64 builder arguments returnRepresentation varName
        UInt8ToInt -> compileIntConversion Signed 64 builder arguments returnRepresentation varName
        Int16ToInt -> compileIntConversion Signed 64 builder arguments returnRepresentation varName
        UInt16ToInt -> compileIntConversion Signed 64 builder arguments returnRepresentation varName
        Int32ToInt -> compileIntConversion Signed 64 builder arguments returnRepresentation varName
        UInt32ToInt -> compileIntConversion Signed 64 builder arguments returnRepresentation varName
        UIntToInt -> identity
        IntToInt8 -> compileIntConversion Signed 8 builder arguments returnRepresentation varName
        IntToUInt8 -> compileIntConversion Unsigned 8 builder arguments returnRepresentation varName
        IntToInt16 -> compileIntConversion Signed 16 builder arguments returnRepresentation varName
        IntToUInt16 -> compileIntConversion Unsigned 16 builder arguments returnRepresentation varName
        IntToInt32 -> compileIntConversion Signed 32 builder arguments returnRepresentation varName
        IntToUInt32 -> compileIntConversion Unsigned 32 builder arguments returnRepresentation varName
        IntToUInt -> identity
        UnsafeRem -> compileUnsafeRem builder arguments returnRepresentation varName
        Errno -> outOfLineBuiltin builder "vega_errno" simpleArgumentValues returnRepresentation varName
        DebugInt -> outOfLineBuiltin builder "vega_debug_int" simpleArgumentValues returnRepresentation varName
        Panic -> undefined
        UnsafeCoerce -> identity
  where
    identity = case arguments of
        [argument] -> lookupVarValue argument
        _ -> panic $ "identity operation called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"
compileUnsafeReadArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es CompoundValue
compileUnsafeReadArray builder arguments returnRepresentation varName = case arguments of
    [array, index] -> do
        valueLayout <- Layout.representationLayout returnRepresentation
        array <- Layout.assertBoxed <$> lookupVarValue array
        index <- Layout.assertScalar <$> lookupVarValue index

        buildArrayLoad builder valueLayout array index varName
    _ -> panic $ "unsafeReadArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeWriteArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es CompoundValue
compileUnsafeWriteArray builder arguments _returnRepresentation _varName = case arguments of
    [array, index, value] -> do
        array <- Layout.assertBoxed <$> lookupVarValue array
        index <- Layout.assertScalar <$> lookupVarValue index
        (value, valueLayout) <- lookupVar value

        buildArrayStore builder valueLayout array index value
        pure Layout.unitCompoundValue
    _ -> panic $ "unsafeReadArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileReplicateArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es CompoundValue
compileReplicateArray builder arguments returnRepresentation varName = case arguments of
    [size, initialMIRValue] -> do
        sizeValue <- Layout.assertScalar <$> lookupVarValue size
        (initialValue, valueLayout) <- lookupVar initialMIRValue

        incomingBlock <- LLVMBuilder.getInsertBlock builder

        infoTable <- getOrCreateArrayInfoTablePointer False valueLayout

        array <- Layout.assertBoxed <$> outOfLineBuiltin builder "vega_allocate_uninitialized_array" [infoTable, sizeValue] returnRepresentation varName
        registerGCRoot array
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
        pure $ Layout.boxedCompoundValue array
    _ -> panic $ "replicateArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeUninitializedMutableArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Seq Representation -> Representation -> Text -> Eff es CompoundValue
compileUnsafeUninitializedMutableArray builder arguments representationArguments returnRepresentation varName = case arguments of
    [size] -> do
        sizeValue <- Layout.assertScalar <$> lookupVarValue size
        elementRepresentation <- case representationArguments of
            [elementRepresentation] -> pure elementRepresentation
            _ -> panic $ "compileUnsafeUninitializedMutableArray called with incorrect number of representation arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty representationArguments) <> "]"
        elementLayout <- Layout.representationLayout elementRepresentation

        infoTable <- getOrCreateArrayInfoTablePointer False elementLayout

        array <- outOfLineBuiltin builder "vega_allocate_zero_initialized_array" [infoTable, sizeValue] returnRepresentation varName
        pure array
    _ -> panic $ "unsafeUninitializedMutableArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileArrayLength :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es CompoundValue
compileArrayLength builder arguments _returnRepresentation varName = case arguments of
    [array] -> do
        array <- Layout.assertBoxed <$> lookupVarValue array
        lengthPointer <- buildGEPOffset builder array Heap.arrayLengthOffset "lengthPtr"
        Layout.scalarCompoundValue <$> LLVMBuilder.buildLoad builder LLVM.int64Type lengthPointer varName
    _ -> panic $ "arrayLength called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeArrayContents :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es CompoundValue
compileUnsafeArrayContents builder arguments _returnRepresentation varName = case arguments of
    [array] -> do
        -- TODO: this might need to do a bitcast to turn this into an *unmanaged* pointer once we track GC roots
        array <- Layout.assertBoxed <$> lookupVarValue array
        Layout.scalarCompoundValue <$> buildGEPOffset builder array (Heap.arrayContentOffset) varName
    _ -> panic $ "unsafeReadArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileOffsetPointerBytes :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es CompoundValue
compileOffsetPointerBytes builder arguments _returnRepresentation varName = case arguments of
    [pointer, offset] -> do
        pointer <- Layout.assertScalar <$> lookupVarValue pointer
        offset <- Layout.assertScalar <$> lookupVarValue offset
        Layout.scalarCompoundValue <$> LLVMBuilder.buildGetElementPtr builder LLVM.int8Type pointer [offset] varName
    _ -> panic $ "offsetPointerBytes called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeFreezeArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es CompoundValue
compileUnsafeFreezeArray _builder arguments _returnRepresentation _varName = case arguments of
    [array] -> lookupVarValue array
    _ -> panic $ "unsafeFreezeArray called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeThawArray :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es CompoundValue
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
    Eff es CompoundValue
compileIntConversion sign width builder arguments _returnRepresentation varName = case arguments of
    [value] -> do
        value <- Layout.assertScalar <$> lookupVarValue value
        let isSigned = case sign of
                Signed -> True
                Unsigned -> False

        Layout.scalarCompoundValue <$> LLVMBuilder.buildIntCast builder value (LLVM.intType width) isSigned varName
    _ -> panic $ "integer conversion primop called with incorrect number of arguments: [" <> Pretty.intercalateDoc ", " (fmap pretty arguments) <> "]"

compileUnsafeRem :: (Compile es) => LLVMBuilder.Builder -> Seq MIR.Variable -> Representation -> Text -> Eff es CompoundValue
compileUnsafeRem builder arguments _returnRepresentation varName = case arguments of
    [dividend, divisor] -> do
        dividend <- Layout.assertScalar <$> lookupVarValue dividend
        divisor <- Layout.assertScalar <$> lookupVarValue divisor
        Layout.scalarCompoundValue <$> LLVMBuilder.buildSRem builder dividend divisor varName
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
    Eff es CompoundValue
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
    Eff es CompoundValue
buildCCCCall builder functionType functionValue arguments returnLayout varName = do
    (returnValue, callInstr) <- case Layout.returnConvention returnLayout of
        Layout.Void -> do
            callInstr <- buildCallWithAttributes builder functionType functionValue arguments ""
            pure (Layout.unitCompoundValue, callInstr)
        Layout.SingleBoxed -> do
            callInstr <- buildCallWithAttributes builder functionType functionValue arguments varName
            registerGCRoot callInstr
            pure (Layout.boxedCompoundValue callInstr, callInstr)
        Layout.SingleScalar _scalarType -> do
            callInstr <- buildCallWithAttributes builder functionType functionValue arguments varName
            pure (Layout.scalarCompoundValue callInstr, callInstr)
        Layout.ScalarStruct -> do
            callInstr <- buildCallWithAttributes builder functionType functionValue arguments ""
            returnValue <- deconstructScalarStruct builder returnLayout callInstr varName

            pure (returnValue, callInstr)
        Layout.SRetPointer -> do
            returnPointer <- buildAtRestAlloca builder returnLayout "sret"
            -- The sret parameter is always the first parameter
            callInstr <- buildCallWithAttributes builder functionType functionValue ([returnPointer] <> arguments) ""

            returnValue <- buildComplexLoad builder returnLayout returnPointer varName

            pure (returnValue, callInstr)
    -- This is technically not necessary since ccc is the default but it's nice to be explicit
    LLVM.setInstructionCallConv callInstr LLVM.ccallConv
    pure returnValue

constructScalarStruct :: (Compile es) => LLVMBuilder.Builder -> Layout -> CompoundValue -> Text -> Eff es LLVM.Value
constructScalarStruct builder layout value varName = do
    assert (isNothing (Layout.unboxedPointer value))
    assert (Size.inBits (Layout.unboxedSize layout) == 0)
    assert (Layout.boxedCount layout == length (Layout.boxedValues value))
    assert (length (Layout.decomposedScalars layout) == length (Layout.decomposedScalarValues value))

    emptyStruct <- LLVM.getPoison (Layout.scalarStructType layout)
    let insert struct (index, value) = do
            LLVMBuilder.buildInsertValue builder struct value index varName
    foldlM insert emptyStruct (Vector.indexed (Layout.boxedValues value <> Layout.decomposedScalarValues value))

deconstructScalarStruct :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> Text -> Eff es CompoundValue
deconstructScalarStruct builder layout struct varName = runSTE \(type s) -> do
    assert (Size.inBytes (Layout.unboxedSize layout) == 0)

    valueBuilder <- Layout.newBuilder @s builder layout
    for_ @[] [0 .. Layout.boxedCount layout - 1] \i -> do
        boxedValue <- LLVMBuilder.buildExtractValue builder struct i (varName <> ".boxed")
        registerGCRoot boxedValue
        Layout.fillBoxed valueBuilder i boxedValue

    forIndexed_ (Layout.decomposedScalars layout) \_ i -> do
        scalar <- LLVMBuilder.buildExtractValue builder struct i (varName <> ".scalar")
        Layout.fillDecomposed valueBuilder i scalar

    Layout.buildValue valueBuilder

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
                                    { sizeInBytes = fromIntegral (Size.inBytes (Layout.sizeAtRest layout))
                                    , boxedCount = fromIntegral (Layout.boxedCount layout)
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
                                    { elementStrideInBytes = fromIntegral $ Size.inBytes (Layout.strideAtRest elementLayout)
                                    , elementBoxedCount = fromIntegral (Layout.boxedCount elementLayout)
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
    infoTable <- getOrCreateArrayInfoTablePointer True (Layout.intLayout (Size.fromBytes 1))
    unique <- liftIO newUnique

    let arrayHeapType = LLVM.structType [LLVM.pointerType, LLVM.int64Type, LLVM.arrayType LLVM.int8Type (ByteString.length bytes)] False
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

accessLocation :: (HasCallStack, Compile es) => LLVMBuilder.Builder -> CompoundValue -> Layout -> Layout.ElementLocation -> Text -> Eff es CompoundValue
accessLocation builder value layout location varName = case location of
    Layout.BoxedScalar index -> pure $ Layout.boxedCompoundValue $ Layout.boxedValues value Vector.! index
    Layout.DecomposedScalar index -> pure $ Layout.scalarCompoundValue $ Layout.decomposedScalarValues value Vector.! index
    Layout.UnboxedOffset{inFlightOffsetInBytes} -> do
        let unboxedPointer = case Layout.unboxedPointer value of
                Nothing -> panic "Trying to access unboxed offset on compound value without unboxed segment"
                Just unboxedPointer -> unboxedPointer
        elementPointer <- buildGEPOffset builder unboxedPointer inFlightOffsetInBytes ""
        buildComplexLoad builder layout elementPointer varName

accessElementByPath :: (HasCallStack) => Layout.ElementPath -> Layout -> Layout.ElementLocation
accessElementByPath path layout = case Layout.details layout of
    Layout.TopLevelSumLayout{tagSize = _, tagLocation, constructors} -> case path of
        Layout.SumConstructor index :<| rest -> go rest (constructors `NonEmpty.index` index)
        Layout.SumTag :<| Empty -> tagLocation
        Layout.SumTag :<| _ -> panic $ "non-final sum tag in elment path: " <> show path
        Layout.ProductField _ :<| _ -> panic $ "Trying to access element at product path on TopLevelSumLayout: " <> show path
        Empty -> panic "Trying to access non-primitive path as element"
    Layout.Simple nestedLayout -> go path nestedLayout
  where
    go path nestedLayout = case path of
        Empty -> case nestedLayout of
            Layout.Primitive location -> location
            _ -> panic $ "Trying to access non-primitive path as element"
        path@(Layout.SumConstructor _ :<| _) -> case nestedLayout of
            Layout.NestedSumLayout{boxedIndices, decomposedIndices, unboxedOffset, layout} -> do
                let innerElement = accessElementByPath path layout
                case innerElement of
                    Layout.BoxedScalar innerIndex -> Layout.BoxedScalar (boxedIndices `Seq.index` innerIndex)
                    Layout.DecomposedScalar innerIndex -> Layout.DecomposedScalar (decomposedIndices `Seq.index` innerIndex)
                    Layout.UnboxedOffset offset size alignment -> case unboxedOffset of
                        Nothing -> panic $ "Returned UnboxedOffset location for a layout without an unboxed segment"
                        Just innerOffset -> Layout.UnboxedOffset (innerOffset + offset) size alignment
            _ -> mismatched "sum"
        Layout.ProductField index :<| rest -> case nestedLayout of
            Layout.ProductLayout inner -> go rest (inner `Seq.index` index)
            _ -> mismatched "product"
        Layout.SumTag :<| _ -> panic "Trying to access nested sum layout with a SumTag path"
    mismatched :: (HasCallStack) => Doc Ann -> a
    mismatched kind = panic $ "Trying to use a " <> kind <> " path to access a non-" <> kind <> " layout"

copyElement ::
    (STE s :> es, Compile es) =>
    LLVMBuilder.Builder ->
    Layout.ElementLocation ->
    Layout.CompoundValue ->
    Layout.ElementLocation ->
    Layout ->
    Layout.CompoundValueBuilder s ->
    Eff es ()
copyElement builder sourceLocation sourceValue targetLocation targetLayout targetValueBuilder = do
    elementValueOrOffset <- case sourceLocation of
        Layout.BoxedScalar index -> pure $ Left $ Layout.boxedValues sourceValue Vector.! index
        Layout.DecomposedScalar index -> pure $ Left $ Layout.decomposedScalarValues sourceValue Vector.! index
        Layout.UnboxedOffset{inFlightOffsetInBytes, size, alignment} -> case Layout.unboxedPointer sourceValue of
            Nothing -> panic "Trying to copy from unboxed offset in layout without unboxed segment"
            Just basePointer -> do
                pointer <- buildGEPOffset builder basePointer inFlightOffsetInBytes ""
                pure $ Right (pointer, size, alignment)
    case targetLocation of
        Layout.BoxedScalar index -> case elementValueOrOffset of
            Left elementValue -> Layout.fillBoxed targetValueBuilder index elementValue
            Right (pointer, _size, alignment) -> do
                elementValue <- LLVMBuilder.buildLoad builder LLVM.pointerType pointer "source"
                LLVM.setAlignment elementValue (Alignment.toInt alignment)
                Layout.fillBoxed targetValueBuilder index elementValue
        Layout.DecomposedScalar index -> case elementValueOrOffset of
            Left elementValue -> Layout.fillDecomposed targetValueBuilder index elementValue
            Right (pointer, _size, alignment) -> do
                let llvmType = Layout.decomposedScalars targetLayout `Seq.index` index

                elementValue <- LLVMBuilder.buildLoad builder llvmType pointer "source"
                LLVM.setAlignment elementValue (Alignment.toInt alignment)
                Layout.fillDecomposed targetValueBuilder index elementValue
        Layout.UnboxedOffset{inFlightOffsetInBytes=targetOffset, size=targetSize, alignment=targetAlignment} -> case Layout.unboxedBuilderPointer targetValueBuilder of
            Nothing -> panic "Trying to copy to unboxed offset of a value builder without an unboxed segment"
            Just targetBasePointer -> case elementValueOrOffset of
                Left elementValue -> do
                    targetPointer <- buildGEPOffset builder targetBasePointer targetOffset "target"
                    storeInstruction <- LLVMBuilder.buildStore builder elementValue targetPointer
                    LLVM.setAlignment storeInstruction (Alignment.toInt targetAlignment)
                    pure ()
                Right (sourcePointer, sourceSize, sourceAlignment) -> do
                    assert (Size.inBits sourceSize == Size.inBits targetSize)
                    targetPointer <- buildGEPOffset builder targetBasePointer targetOffset "target"
                    _ <-
                        LLVMBuilder.buildMemCpy
                            builder
                            targetPointer
                            (Alignment.toInt sourceAlignment)
                            sourcePointer
                            (Alignment.toInt targetAlignment)
                            (LLVM.constInt LLVM.int64Type (fromIntegral (Size.inBytes sourceSize)) False)
                    pure ()

buildAtRestAlloca :: (Compile es) => LLVMBuilder.Builder -> Layout -> Text -> Eff es LLVM.Value
buildAtRestAlloca builder layout varName = do
    LLVMBuilder.buildAlloca builder (LLVM.arrayType LLVM.int8Type (Size.inBytes (Layout.sizeAtRest layout))) varName

buildComplexStore :: (Compile es) => LLVMBuilder.Builder -> Layout -> CompoundValue -> LLVM.Value -> Eff es ()
buildComplexStore builder layout value baseTargetPointer = do
    assert (Layout.boxedCount layout == length (Layout.boxedValues value))
    forIndexed_ (Layout.boxedValues value) \boxedValue boxedIndex -> do
        targetPointer <- buildGEPOffset builder baseTargetPointer (Layout.atRestBoxedOffset layout boxedIndex) "target_ptr.boxed"
        _ <- LLVMBuilder.buildStore builder boxedValue targetPointer
        pure ()

    assert (length (Layout.decomposedScalars layout) == length (Layout.decomposedScalarValues value))
    forIndexed_ (Layout.decomposedScalarValues value) \scalarValue scalarIndex -> do
        targetPointer <- buildGEPOffset builder baseTargetPointer (Layout.atRestDecomposedScalarOffset layout scalarIndex) "target_ptr.scalar"
        _ <- LLVMBuilder.buildStore builder scalarValue targetPointer
        pure ()

    for_ @Maybe (Layout.unboxedPointer value) \unboxedSourcePointer -> do
        targetPointer <- buildGEPOffset builder baseTargetPointer (Layout.atRestUnboxedOffset layout) "target_ptr.unboxed"
        let alignment = Alignment.toInt (Layout.unboxedAlignment layout)
        let size = LLVM.constInt LLVM.int64Type (fromIntegral (Size.inBytes (Layout.unboxedSize layout))) False

        LLVMBuilder.buildMemCpy builder targetPointer alignment unboxedSourcePointer alignment size

buildArrayStore :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> LLVM.Value -> CompoundValue -> Eff es ()
buildArrayStore builder layout array index value = do
    contents <- buildGEPOffset builder array Heap.arrayContentOffset "contents"
    pointer <- LLVMBuilder.buildGetElementPtr builder (LLVM.arrayType LLVM.int8Type (Size.inBytes (Layout.strideAtRest layout))) contents [index] ""
    buildComplexStore builder layout value pointer

buildArrayLoad :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> LLVM.Value -> Text -> Eff es CompoundValue
buildArrayLoad builder layout array index varName = do
    contents <- buildGEPOffset builder array Heap.arrayContentOffset "contents"
    pointer <- LLVMBuilder.buildGetElementPtr builder (LLVM.arrayType LLVM.int8Type (Size.inBytes (Layout.strideAtRest layout))) contents [index] ""
    buildComplexLoad builder layout pointer varName

buildComplexReturn :: (Compile es) => LLVMBuilder.Builder -> Layout -> CompoundValue -> Eff es ()
buildComplexReturn builder layout value = case Layout.returnConvention layout of
    Layout.Void -> do
        _ <- LLVMBuilder.buildRetVoid builder
        pure ()
    Layout.SingleBoxed -> do
        _ <- LLVMBuilder.buildRet builder (Layout.assertBoxed value)
        pure ()
    Layout.SingleScalar _ -> do
        _ <- LLVMBuilder.buildRet builder (Layout.assertScalar value)
        pure ()
    Layout.SRetPointer -> do
        case ?functionEnv.sretVariable of
            Nothing -> panic $ "Trying to return layout with SRetPointer return convention from a function without sret variable: " <> show layout
            Just (sretVariable, _) -> do
                buildComplexStore builder layout value sretVariable
                _ <- LLVMBuilder.buildRetVoid builder
                pure ()
    Layout.ScalarStruct -> do
        structToReturn <- constructScalarStruct builder layout value "ret"

        _ <- LLVMBuilder.buildRet builder structToReturn
        pure ()

{- | Load from a pointer while keeping the unboxed segment as a pointer.
This is only valid if the pointee lives at least as long as the value returned from this
-}
buildLoadAsReference :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> Text -> Eff es CompoundValue
buildLoadAsReference builder layout basePointer varName = runSTE \s -> do
    unboxedPointer <- buildGEPOffset builder basePointer (Layout.atRestUnboxedOffset layout) (varName <> ".unboxed_ref")

    valueBuilder <- Layout.newBuilderWithUnboxedPointer @s layout (Just unboxedPointer)

    for_ @[] [0 .. Layout.boxedCount layout - 1] \boxedIndex -> do
        boxPointer <- buildGEPOffset builder basePointer (Layout.atRestBoxedOffset layout boxedIndex) (varName <> ".boxed")
        value <- LLVMBuilder.buildLoad builder LLVM.pointerType boxPointer ""
        registerGCRoot value
        Layout.fillBoxed valueBuilder boxedIndex value
    forIndexed_ (Layout.decomposedScalars layout) \scalarType scalarIndex -> do
        scalarPointer <- buildGEPOffset builder basePointer (Layout.atRestDecomposedScalarOffset layout scalarIndex) (varName <> ".scalar")
        value <- LLVMBuilder.buildLoad builder scalarType scalarPointer ""
        Layout.fillBoxed valueBuilder scalarIndex value

    Layout.buildValue valueBuilder

buildComplexLoad :: (Compile es) => LLVMBuilder.Builder -> Layout -> LLVM.Value -> Text -> Eff es CompoundValue
buildComplexLoad builder layout basePointer varName = runSTE \s -> do
    valueBuilder <- Layout.newBuilder @s builder layout

    for_ @[] [0 .. Layout.boxedCount layout - 1] \boxedIndex -> do
        boxPointer <- buildGEPOffset builder basePointer (Layout.atRestBoxedOffset layout boxedIndex) (varName <> ".boxed")
        value <- LLVMBuilder.buildLoad builder LLVM.pointerType boxPointer ""
        registerGCRoot value
        Layout.fillBoxed valueBuilder boxedIndex value
    forIndexed_ (Layout.decomposedScalars layout) \scalarType scalarIndex -> do
        scalarPointer <- buildGEPOffset builder basePointer (Layout.atRestDecomposedScalarOffset layout scalarIndex) (varName <> ".scalar")
        value <- LLVMBuilder.buildLoad builder scalarType scalarPointer ""
        Layout.fillDecomposed valueBuilder scalarIndex value
    for_ @Maybe (Layout.unboxedBuilderPointer valueBuilder) \targetPointer -> do
        sourcePointer <- buildGEPOffset builder basePointer (Layout.atRestUnboxedOffset layout) ""
        let alignment = Alignment.toInt (Layout.unboxedAlignment layout)
        let size = LLVM.constInt LLVM.int64Type (fromIntegral $ Size.inBytes (Layout.unboxedSize layout)) False
        LLVMBuilder.buildMemCpy builder targetPointer alignment sourcePointer alignment size

    Layout.buildValue valueBuilder

fillLocation :: (STE s :> es, Compile es, HasCallStack) => LLVMBuilder.Builder -> Layout.CompoundValueBuilder s -> Layout.ElementLocation -> LLVM.Value -> Eff es ()
fillLocation builder valueBuilder location value = case location of
    Layout.BoxedScalar index -> Layout.fillBoxed valueBuilder index value
    Layout.DecomposedScalar index -> Layout.fillDecomposed valueBuilder index value
    Layout.UnboxedOffset offset _size alignment -> case Layout.unboxedBuilderPointer valueBuilder of
        Nothing -> panic "Trying to fill unboxed offset location of a value builder without an unboxed segment"
        Just pointer -> do
            contentPointer <- buildGEPOffset builder pointer offset ""
            storeInstruction <- LLVMBuilder.buildStore builder contentPointer value
            -- We don't need the size here, but the alignment could be higher than the natural alignment that
            -- LLVM expects so we can set it explicitly
            LLVM.setAlignment storeInstruction (Alignment.toInt alignment)

{- | Build a @getelementptr@ instruction pointing at a constant offset given in bytes.
The offset is assumed to be in-bounds.
-}
buildGEPOffset :: (Compile es) => LLVMBuilder.Builder -> LLVM.Value -> Int -> Text -> Eff es LLVM.Value
buildGEPOffset builder pointer offset name = case offset of
    0 -> pure pointer
    _ -> LLVMBuilder.buildInBoundsGetElementPtr builder LLVM.int8Type pointer [LLVM.constInt LLVM.int64Type (fromIntegral offset) False] name

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

asVar :: (Compile es) => MIR.Variable -> Layout -> (Text -> Eff es CompoundValue) -> Eff es CompoundValue
asVar var layout cont = do
    llvmValue <- cont (renderVariable var)
    insertVarMapping var llvmValue layout
    pure llvmValue

insertVarMapping :: (Compile es) => MIR.Variable -> CompoundValue -> Layout -> Eff es ()
insertVarMapping var llvmValue layout = modify (\state -> state{variableMappings = HashMap.insert var (llvmValue, layout) state.variableMappings})

asVar_ :: (Compile es) => MIR.Variable -> Layout -> (Text -> Eff es CompoundValue) -> Eff es ()
asVar_ var layout cont = do
    _ <- asVar var layout cont
    pure ()

closureWrapperNameForFunction :: Vega.GlobalName -> Text
closureWrapperNameForFunction coreName = renderLLVMName coreName <> "__closure"

lookupVar :: (HasCallStack, Compile es) => MIR.Variable -> Eff es (Layout.CompoundValue, Layout)
lookupVar variable = do
    MkDeclarationState{variableMappings} <- get
    case HashMap.lookup variable variableMappings of
        Nothing -> panic $ "Trying to use MIR variable without associated LLVM value: " <> pretty variable
        Just value -> pure value

lookupVarValue :: (HasCallStack, Compile es) => MIR.Variable -> Eff es CompoundValue
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

compileArithmeticOperator :: (Compile es) => LLVMBuilder.Builder -> MIR.ArithmeticExpr -> Text -> Eff es (LLVM.Value, Layout)
compileArithmeticOperator builder arithmeticExpr varName = case arithmeticExpr of
    MIR.Add var1 var2 -> do
        (arg1, representation) <- lookupVar var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildAdd builder (Layout.assertScalar arg1) (Layout.assertScalar arg2) varName
        pure (result, representation)
    MIR.Subtract var1 var2 -> do
        (arg1, representation) <- lookupVar var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildSub builder (Layout.assertScalar arg1) (Layout.assertScalar arg2) varName
        pure (result, representation)
    MIR.Multiply var1 var2 -> do
        (arg1, representation) <- lookupVar var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildMul builder (Layout.assertScalar arg1) (Layout.assertScalar arg2) varName
        pure (result, representation)
    MIR.Divide var1 var2 -> do
        (arg1, representation) <- lookupVar var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildSDiv builder (Layout.assertScalar arg1) (Layout.assertScalar arg2) varName
        pure (result, representation)
    MIR.Less var1 var2 -> do
        arg1 <- lookupVarValue var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildICmp builder LLVM.IntSLT (Layout.assertScalar arg1) (Layout.assertScalar arg2) varName
        pure (result, Layout.boolLayout)
    MIR.LessEqual var1 var2 -> do
        arg1 <- lookupVarValue var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildICmp builder LLVM.IntSLE (Layout.assertScalar arg1) (Layout.assertScalar arg2) varName
        pure (result, Layout.boolLayout)
    MIR.Equal var1 var2 -> do
        arg1 <- lookupVarValue var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildICmp builder LLVM.IntEQ (Layout.assertScalar arg1) (Layout.assertScalar arg2) varName
        pure (result, Layout.boolLayout)
    MIR.NotEqual var1 var2 -> do
        arg1 <- lookupVarValue var1
        arg2 <- lookupVarValue var2
        result <- LLVMBuilder.buildICmp builder LLVM.IntNE (Layout.assertScalar arg1) (Layout.assertScalar arg2) varName
        pure (result, Layout.boolLayout)

registerGCRoot :: (Compile es) => LLVM.Value -> Eff es ()
registerGCRoot _ = do
    -- TODO
    pure ()

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
