module Vega.Compilation.LLVM.Layout (
    -- * Layout Generation
    Layout,
    representationLayout,

    -- * Layout Properties
    sizeAtRest,
    strideAtRest,
    alignment,
    unboxedAlignment,
    boxedCount,
    unboxedSize,
    decomposedScalars,
    decomposedStride,
    atRestBoxedOffset,
    atRestDecomposedScalarOffset,
    atRestUnboxedOffset,
    atRestOffsetInBytes,
    atRestLLVMType,
    buildAtRestAlloca,
    llvmParameters,
    parameterCount,
    parameterBoxedIndex,
    parameterDecomposedScalarIndex,
    parameterUnboxedIndex,
    identifier,
    details,
    forContainedElements,
    forContainedElementsAtSumConstructorIndex,
    ElementPathSegment (..),
    ElementPath,
    elementPathFromMIRPath,
    returnConvention,
    ReturnConvention (..),
    scalarStructType,

    -- * Compound Values
    CompoundValue,
    boxedValues,
    decomposedScalarValues,
    unboxedPointer,
    boxedCompoundValue,
    scalarCompoundValue,
    unitCompoundValue,
    compoundAsFunctionArguments,

    -- ** Compund Value Builder
    CompoundValueBuilder,
    newBuilder,
    newBuilderWithUnboxedPointer,
    fillBoxed,
    fillRemainingBoxedWithNull,
    fillDecomposed,
    unboxedBuilderPointer,
    buildValue,

    -- * Layout Details
    TopLevelLayoutDetails (..),
    NestedLayoutDetails (..),
    ElementLocation (..),

    -- * Specific Layouts
    unitLayout,
    boolLayout,
    boxedLayout,
    rawPointerLayout,
    intLayout,
    byteArrayLayout,
    closureLayout,

    -- * Convenience Accesses

    -- These are useful for common cases where we know the (simple) layout statically and just need to extract the actual
    -- underlying LLVM value
    assertBoxed,
    assertScalar,
    assertSingleValue,
    closurePayload,
    closureFunctionPointer,
) where

import Control.Exception (assert)
import Data.Bits qualified as Bits
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Data.Vector.Storable qualified as Storable
import Data.Vector.Strict (Vector)
import Data.Vector.Generic qualified as Vector
import Effectful (Eff, IOE, runPureEff, (:>))
import LLVM.Core qualified as LLVM
import LLVM.Core.Context qualified as LLVM
import LLVM.InstructionBuilder qualified as LLVMBuilder
import Relude hiding (NonEmpty, catMaybes, mapMaybe)
import System.IO.Unsafe (unsafePerformIO)
import Text.Show (Show (..))
import Vega.Alignment (Alignment)
import Vega.Alignment qualified as Alignment
import Vega.Compilation.Core.Syntax (Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Debug (showHeadConstructor)
import Vega.Effect.ST (STE, runSTE)
import Vega.OutArray (OutArray)
import Vega.OutArray qualified as OutArray
import Vega.Panic (panic)
import Vega.Pretty (Pretty, number, pretty, (<+>))
import Vega.Pretty qualified as Pretty
import Vega.Seq.NonEmpty (NonEmpty ((:<||)), maximum, pattern NonEmpty)
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Size (Size)
import Vega.Size qualified as Size
import Vega.Syntax qualified as Vega
import Vega.Util (forAccumLM, forIndexed, forIndexed_, mapAccumLM, smallestPowerOfTwoFitting)
import Vega.Util qualified as Util
import Witherable (catMaybes, mapMaybe, wither)

{- Note [At-rest vs in-flight]:
-------------------------------

Runtime values can occur in two states:
-   "in-flight" values are values that are actively being manipulated.
    if these are large, they may be stored in an alloca allocation (in 'CompoundValue.unboxedPointer')
    similarly to values at rest, but if they are small enough, we will decompose them into separate
    llvm scalar values. In particular, individual scalar representations like IntRep become
    values with a single "decomposed" scalar variable.
    Boxed values occuring in a product or sum are always decomposed into their own Seq of variables.
    This is important since we need to be able to mark them as stack roots for the garbage collector.

    This representation also affects how values are passed to functions. Any decomposed or boxed values are
    passed directly as LLVM variables, while unboxed pointers are passed as byval pointer arguments.

-   Values "at-rest" are values that are stored in memory somewhere. In particular, these are values stored in boxed
    heap objects or arrays.
    In this case, all values are stored in memory, but in order to simplify loads and stores, they are stored in a very similar
    format to in-flight values. The exact sizes and offsets can be computed based on the value's 'Layout'.
    +---------------------+------------------------------+--------------------+
    | boxed (n x 8 bytes) | decomposedScalars (variable) | unboxed (variable) |
    +---------------------+------------------------------+--------------------+

-}

data Layout = MkLayout
    { size :: Size
    , alignment :: Alignment
    , boxedCount :: Int
    , -- decomposed scalars store their LLVM type and at rest offset *from the decomposed section*
      -- (see Note [At-rest vs in-flight])
      decomposedScalars :: Seq (LLVM.Type, Int)
    , unboxedAlignment :: Alignment
    , unboxedSize :: Size
    , details :: TopLevelLayoutDetails
    }
    deriving (Show)

alignment :: Layout -> Alignment
alignment layout = layout.alignment

{- | The alignment of the unboxed segment of the layout.
This might be smaller than the total alignment (but will never be larger).

In particular, this will happen with representations like (Int8Rep * Boxed) where
we will decompose the Boxed pointer out such that the alignment is 8, but the unboxedAlignment
is only 1.
-}
unboxedAlignment :: Layout -> Alignment
unboxedAlignment layout = layout.unboxedAlignment

boxedCount :: Layout -> Int
boxedCount layout = layout.boxedCount

unboxedSize :: Layout -> Size
unboxedSize layout = layout.unboxedSize

{- | The actual size taken up by the value.
Unlike 'strideAtRest', this is *NOT* rounded up to a multiple of 'alignment'
so this cannot be used to calculate offsets into arrays or other homogenous structures.

Use 'strideAtRest' if you need to do that.
-}
sizeAtRest :: Layout -> Size
sizeAtRest layout = layout.size

{- | The size taken up by the value rounded up to the next multiple of 'alignment'.

This has the property that @n@ properly aligned values will have stride @n * strideAtRest layout@ and
so we can use this to calculate offsets into arrays or other homogenous structures.
-}
strideAtRest :: Layout -> Size
strideAtRest layout = Size.fromBytes (Alignment.align (alignment layout) (Size.inBytes (sizeAtRest layout)))

decomposedScalars :: Layout -> Seq LLVM.Type
decomposedScalars layout = fmap fst layout.decomposedScalars

details :: Layout -> TopLevelLayoutDetails
-- I don't love having to expose the entirity of LayoutDetails here but i'm not sure how else we would do nested product/sum constructors
details layout = layout.details

llvmParameters :: (?context :: LLVM.Context) => Layout -> Seq (LLVM.Type, Seq LLVM.Attribute)
llvmParameters layout = do
    let boxedParameters = Seq.replicate (boxedCount layout) (LLVM.pointerType, [])
    let scalarParameters = fmap (\type_ -> (type_, [])) (decomposedScalars layout)
    let unboxedParameter = case Size.inBytes (unboxedSize layout) of
            0 -> []
            _ -> do
                let llvmType = LLVM.arrayType LLVM.int8Type (Size.inBytes (unboxedSize layout))
                [(LLVM.pointerType, [byvalAttribute llvmType])]
    boxedParameters <> scalarParameters <> unboxedParameter

byvalAttribute :: (?context :: LLVM.Context) => LLVM.Type -> LLVM.Attribute
-- TODO: this should all really be pure in llvm-ng
byvalAttribute llvmType = unsafePerformIO do
    byvalAttributeKind <- LLVM.getEnumAttributeKindForName "byval"
    LLVM.createTypeAttribute byvalAttributeKind llvmType

-- | Specifies how values of this layout should be returned by functions
returnConvention :: Layout -> ReturnConvention
returnConvention layout = case (boxedCount layout, layout.decomposedScalars, Size.inBytes (unboxedSize layout)) of
    (0, [], 0) -> Void
    (1, [], 0) -> SingleBoxed
    (0, [(scalarType, _)], 0) -> SingleScalar scalarType
    (_, _, 0) -> ScalarStruct
    _ -> SRetPointer

forContainedElements :: Layout -> (ElementPath -> ElementLocation -> Eff es ()) -> Eff es ()
forContainedElements layout run = case details layout of
    Simple inner -> forContainedElementsNested [] inner run
    TopLevelSumLayout{tagSize = _, tagLocation, constructors} -> do
        run [SumTag] tagLocation
        forIndexed_ constructors \details index ->
            forContainedElementsNested [SumConstructor index] details run

forContainedElementsAtSumConstructorIndex :: (HasCallStack) => Int -> Layout -> (ElementPath -> ElementLocation -> Eff es ()) -> Eff es ()
forContainedElementsAtSumConstructorIndex index layout run = case details layout of
    Simple _ -> panic "Trying to access elements of Non-TopLevelSum constructor"
    TopLevelSumLayout{constructors} -> do
        forContainedElementsNested [] (constructors `NonEmpty.index` index) run

forContainedElementsNested :: (HasCallStack) => ElementPath -> NestedLayoutDetails -> (ElementPath -> ElementLocation -> Eff es ()) -> Eff es ()
forContainedElementsNested pathSoFar details run = case details of
    Primitive location -> run pathSoFar location
    ProductLayout subLayouts -> forIndexed_ subLayouts \details index -> do
        forContainedElementsNested (pathSoFar :|> ProductField index) details run
    NestedSumLayout{boxedIndices, decomposedIndices, unboxedOffset, layout} -> do
        forContainedElements layout \innerPath innerLocation -> do
            let realLocation = case innerLocation of
                    BoxedScalar innerIndex -> BoxedScalar{inFlightIndex = (boxedIndices `Seq.index` innerIndex)}
                    DecomposedScalar innerIndex -> DecomposedScalar{inFlightIndex = (decomposedIndices `Seq.index` innerIndex)}
                    UnboxedOffset innerOffset size alignment -> case unboxedOffset of
                        Nothing -> panic "NestedSumLayout without unboxed segment contained element at unboxed offset"
                        Just outerOffset -> UnboxedOffset{inFlightOffsetInBytes = (outerOffset + innerOffset), size, alignment}
            run (pathSoFar <> innerPath) realLocation

data ElementPathSegment
    = ProductField Int
    | SumConstructor Int
    | SumTag
    deriving (Show)

type ElementPath = Seq ElementPathSegment

elementPathFromMIRPath :: MIR.Path -> ElementPath
elementPathFromMIRPath = fmap \case
    MIR.ProductFieldPath index -> ProductField index
    MIR.SumConstructorPath index -> SumConstructor index

data ReturnConvention
    = SingleBoxed
    | SingleScalar LLVM.Type
    | {- | This layout should be returned as a struct of scalars.
      INVARIANT: A layout that is returned this way must not have an unboxed section
      -}
      ScalarStruct
    | -- | This layout is zero-sized
      Void
    | -- | The layout should be returned via an sret pointer that stores the value *at rest*
      SRetPointer

{- | The llvm type of the scalar struct that is used to return this layout from function calls.

This is only valid if its 'returnConvention' is 'ScalarStruct'.
-}
scalarStructType :: (?context :: LLVM.Context) => Layout -> LLVM.Type
scalarStructType layout = assert (case returnConvention layout of ScalarStruct -> True; _ -> False) do
    LLVM.structType
        ( Storable.replicate (boxedCount layout) LLVM.pointerType
            <> Util.viaList (decomposedScalars layout)
        )
        False

-- | The stride of the decomposed values in a layout at rest *including padding*.
decomposedStride :: Layout -> Size
decomposedStride layout =
    Size.fromBytes $
        Size.inBytes layout.size
            - Size.inBytes layout.unboxedSize
            - layout.boxedCount * Size.inBytes pointerSize

-- | Return a 'Text' identifier that uniquely identifies this layout for the purposes of info-table generation
identifier :: Layout -> Text
identifier layout = "layout[size=" <> Relude.show @_ @Int (Size.inBytes layout.size) <> ",boxed=" <> Relude.show @_ @Int layout.boxedCount <> "]"

atRestBoxedOffset :: Layout -> Int -> Int
-- See Note [At-rest vs in-flight] for why we can compute these offsets this way
atRestBoxedOffset layout boxedIndex = boxedIndex * Size.inBytes pointerSize

atRestDecomposedScalarOffset :: Layout -> Int -> Int
atRestDecomposedScalarOffset layout scalarIndex = do
    let (_, scalarSegmentOffset) = layout.decomposedScalars `Seq.index` scalarIndex
    layout.boxedCount * Size.inBytes pointerSize + scalarSegmentOffset

atRestUnboxedOffset :: Layout -> Int
atRestUnboxedOffset layout = layout.boxedCount * Size.inBytes pointerSize + Size.inBytes (decomposedStride layout)

-- | Returns an LLVM representation of this type at rest or Nothing if it is zero-sized
atRestLLVMType :: (?context :: LLVM.Context) => Layout -> Maybe LLVM.Type
atRestLLVMType layout
    | Size.inBits (layout.size) == 0 = Nothing
    -- This type only contains non-pointer data
    | layout.boxedCount == 0 = Just (LLVM.arrayType LLVM.int8Type (Size.inBytes layout.unboxedSize + Size.inBytes (decomposedStride layout)))
    -- This type only contains pointers
    | Size.inBits layout.unboxedSize == 0 && length layout.decomposedScalars == 0 = do
        Just (LLVM.arrayType LLVM.pointerType layout.boxedCount)
    | otherwise = do
        let pointers = LLVM.arrayType LLVM.pointerType layout.boxedCount
        let unboxed = LLVM.arrayType LLVM.int8Type (Size.inBytes layout.unboxedSize + Size.inBytes (decomposedStride layout))
        Just (LLVM.structType [pointers, unboxed] False)

{- | Create an alloca for this type when stored *at rest* (e.g. when returned via an sret pointer).
This is only valid if the type is not zero-sized.
-}
buildAtRestAlloca :: (HasCallStack, ?context :: LLVM.Context, MonadIO io) => LLVMBuilder.Builder -> Layout -> Text -> io LLVM.Value
buildAtRestAlloca builder layout varName = case atRestLLVMType layout of
    Nothing -> panic "unable to construct alloca for zero sized layout"
    -- TODO: it might make sense to use something custom here that allocates something of size `atRest*Stride* layout`.
    -- LLVM might be able to compile the associated memcpys more efficiently if they have a more aligned  size
    -- and we can afford the extra <= 7 bytes of stack space
    Just llvmType -> LLVMBuilder.buildAlloca builder llvmType varName

-- | The index of the function parameter corresponding to the i-th boxed component
parameterBoxedIndex :: (HasCallStack) => Layout -> Int -> Int
parameterBoxedIndex layout index = assertInBounds index (boxedCount layout) do
    index

-- | The index of the function parameter corresponding to the i-th decomposed scalar
parameterDecomposedScalarIndex :: (HasCallStack) => Layout -> Int -> Int
parameterDecomposedScalarIndex layout index = assertInBounds index (length (decomposedScalars layout)) do
    boxedCount layout + index

assertInBounds :: (HasCallStack) => Int -> Int -> a -> a
assertInBounds value size result
    | value >= 0 && value < size = result
    | otherwise = panic $ "Access at index " <> number value <> " out of bounds for size " <> number size

{- | The index of the pointer corresponding to the unboxed segment of the layout when passed as a function parameter
This is 'Nothing' if the layout does not have an unboxed segment
-}
parameterUnboxedIndex :: Layout -> Maybe Int
parameterUnboxedIndex layout = case Size.inBytes (unboxedSize layout) of
    0 -> Nothing
    _ -> Just (boxedCount layout + length (decomposedScalars layout))

{- | The number of LLVM parameters that funcitons taking this layout will accept.

This is equivalent to @length (llvmParameters layout)@ but much more efficient
-}
parameterCount :: Layout -> Int
parameterCount layout = do
    let unboxedParameter = case Size.inBytes (unboxedSize layout) of
            0 -> 0
            _ -> 1

    boxedCount layout + length (decomposedScalars layout) + unboxedParameter

data CompoundValue = MkCompoundValue
    { boxed :: Vector LLVM.Value
    , decomposedScalars :: Vector LLVM.Value
    , unboxedPointer :: Maybe LLVM.Value
    }

instance Pretty CompoundValue where
    pretty (MkCompoundValue{boxed, decomposedScalars, unboxedPointer}) =
        Pretty.lparen "("
            <> prettyValues boxed
                <+> Pretty.keyword "|"
                <+> prettyValues decomposedScalars
                <+> Pretty.keyword "|"
                <+> prettyValues unboxedPointer
            <> Pretty.rparen ")"
      where
        prettyValues :: (Foldable f, Functor f) => f LLVM.Value -> Pretty.Doc Pretty.Ann
        prettyValues values = Pretty.intercalateDoc (Pretty.keyword ", ") (fmap (\llvmValue -> Pretty.literal (Relude.show llvmValue)) values)

boxedValues :: CompoundValue -> Vector LLVM.Value
boxedValues compoundValue = compoundValue.boxed

decomposedScalarValues :: CompoundValue -> Vector LLVM.Value
decomposedScalarValues compoundValue = compoundValue.decomposedScalars

unboxedPointer :: CompoundValue -> Maybe LLVM.Value
unboxedPointer compoundValue = compoundValue.unboxedPointer

-- | Helper function to avoid going through a value builder for the common case where a value is a single boxed pointer
boxedCompoundValue :: LLVM.Value -> CompoundValue
boxedCompoundValue value = MkCompoundValue{boxed = [value], decomposedScalars = [], unboxedPointer = Nothing}

-- | Helper function to avoid going through a value builder for the common case where a value is a single scalar
scalarCompoundValue :: LLVM.Value -> CompoundValue
scalarCompoundValue value = MkCompoundValue{boxed = [], decomposedScalars = [value], unboxedPointer = Nothing}

unitCompoundValue :: CompoundValue
unitCompoundValue = MkCompoundValue{boxed = [], decomposedScalars = [], unboxedPointer = Nothing}

compoundAsFunctionArguments :: CompoundValue -> Seq LLVM.Value
compoundAsFunctionArguments MkCompoundValue{boxed, decomposedScalars, unboxedPointer} =
    Util.viaList boxed <> Util.viaList decomposedScalars <> fromList (toList unboxedPointer)

data CompoundValueBuilder s = MkCompoundValueBuilder
    { boxed :: OutArray s LLVM.Value
    , decomposedScalars :: OutArray s LLVM.Value
    , unboxedPointer :: Maybe LLVM.Value
    }

newBuilderWithUnboxedPointer :: (STE s :> es) => Layout -> Maybe LLVM.Value -> Eff es (CompoundValueBuilder s)
newBuilderWithUnboxedPointer layout unboxedPointer = do
    boxed <- OutArray.new (boxedCount layout)
    decomposedScalars <- OutArray.new (length (decomposedScalars layout))
    pure (MkCompoundValueBuilder{boxed, decomposedScalars, unboxedPointer})

newBuilder :: (STE s :> es, IOE :> es, ?context :: LLVM.Context) => LLVMBuilder.Builder -> Layout -> Eff es (CompoundValueBuilder s)
newBuilder builder layout = do
    unboxedPointer <- case Size.inBytes (unboxedSize layout) of
        0 -> pure Nothing
        size -> do
            -- TODO: we should really hoist allocas to the first block because that's where LLVM will optimize them properly
            pointer <- LLVMBuilder.buildAlloca builder (LLVM.arrayType LLVM.int8Type size) "unboxed"
            LLVM.setAlignment pointer (Alignment.toInt (unboxedAlignment layout))
            pure (Just pointer)
    newBuilderWithUnboxedPointer layout unboxedPointer

fillBoxed :: (STE s :> es, HasCallStack) => CompoundValueBuilder s -> Int -> LLVM.Value -> Eff es ()
fillBoxed builder index value = OutArray.fill builder.boxed index value

fillRemainingBoxedWithNull :: (STE s :> es, HasCallStack, ?context :: LLVM.Context) => CompoundValueBuilder s -> Eff es ()
fillRemainingBoxedWithNull builder = OutArray.fillRemaining builder.boxed LLVM.constNullPointer

fillDecomposed :: (STE s :> es, HasCallStack) => CompoundValueBuilder s -> Int -> LLVM.Value -> Eff es ()
fillDecomposed builder index value = OutArray.fill builder.decomposedScalars index value

unboxedBuilderPointer :: CompoundValueBuilder s -> Maybe LLVM.Value
unboxedBuilderPointer builder = builder.unboxedPointer

buildValue :: (STE s :> es, HasCallStack) => CompoundValueBuilder s -> Eff es CompoundValue
buildValue builder = do
    boxed <- OutArray.initializedToVector builder.boxed
    decomposedScalars <- OutArray.initializedToVector builder.decomposedScalars
    pure (MkCompoundValue{boxed, decomposedScalars, unboxedPointer = builder.unboxedPointer})

data ElementLocation
    = BoxedScalar {inFlightIndex :: Int}
    | DecomposedScalar {inFlightIndex :: Int}
    | UnboxedOffset {inFlightOffsetInBytes :: Int, size :: Size, alignment :: Alignment}
    deriving (Generic, Show)

atRestOffsetInBytes :: ElementLocation -> Layout -> Int
atRestOffsetInBytes location layout = case location of
    BoxedScalar{inFlightIndex} -> atRestBoxedOffset layout inFlightIndex
    DecomposedScalar{inFlightIndex} -> undefined
    UnboxedOffset{inFlightOffsetInBytes} -> Alignment.align layout.unboxedAlignment (atRestUnboxedOffset layout) + inFlightOffsetInBytes

data TopLevelLayoutDetails
    = Simple NestedLayoutDetails
    | TopLevelSumLayout {tagSize :: Size, tagLocation :: ElementLocation, constructors :: NonEmpty NestedLayoutDetails}
    deriving (Generic, Show)

data NestedLayoutDetails
    = ProductLayout {elements :: Seq NestedLayoutDetails}
    | NestedSumLayout {boxedIndices :: Seq Int, decomposedIndices :: Seq Int, unboxedOffset :: Maybe Int, layout :: Layout}
    | Primitive ElementLocation
    deriving (Generic, Show)

data LayoutContext = MkLayoutContext
    { boxedCountSoFar :: Int
    , inFlightUnboxedOffsetSoFar :: Int
    , alignmentSoFar :: Alignment
    , unboxedAlignmentSoFar :: Alignment
    }

-- TODO: cache this
representationLayout :: (?context :: LLVM.Context) => Representation -> Eff es Layout
representationLayout representation = do
    case tryDecomposedRepresentationLayout representation of
        Just layout -> pure layout
        Nothing -> do
            let initialContext =
                    MkLayoutContext
                        { boxedCountSoFar = 0
                        , alignmentSoFar = Alignment.fromValue 1
                        , unboxedAlignmentSoFar = Alignment.fromValue 1
                        , inFlightUnboxedOffsetSoFar = 0
                        }
            (context, details) <- case representation of
                Core.SumRep constructorRepresentations -> topLevelSum initialContext constructorRepresentations
                _ -> do
                    (context, nestedDetails) <- go initialContext representation
                    pure (context, Simple nestedDetails)

            let size = Size.fromBytes (context.boxedCountSoFar * Size.inBytes pointerSize + context.inFlightUnboxedOffsetSoFar)
            pure
                MkLayout
                    { size
                    , alignment = context.alignmentSoFar
                    , boxedCount = context.boxedCountSoFar
                    , -- We *currently* either decompose everything or nothing.
                      -- It might make sense to change this in the future
                      decomposedScalars = []
                    , unboxedAlignment = context.unboxedAlignmentSoFar
                    , unboxedSize = Size.fromBytes context.inFlightUnboxedOffsetSoFar
                    , details
                    }
  where
    topLevelSum context (constructors :: Seq Core.Representation) = case constructors of
        Empty -> pure (context, Simple (ProductLayout []))
        [Core.ProductRep [], Core.ProductRep []] -> do
            let (context, nestedDetails) = asUnboxedPrimitive context (Size.fromBits 1) (Alignment.fromValue 1)
            pure (context, Simple nestedDetails)
        NonEmpty constructors -> do
            -- TODO: we could filter out Empty's here (and possibly get rid of the sum alltogether)
            -- if we do, we need to maintain the correct constructor indices though
            (contexts, constructorDetails) <- NonEmpty.unzip <$> for constructors (go context)
            let combinedContext =
                    MkLayoutContext
                        { boxedCountSoFar = maximum (fmap (\context -> context.boxedCountSoFar) contexts)
                        , inFlightUnboxedOffsetSoFar = maximum (fmap (\context -> context.inFlightUnboxedOffsetSoFar) contexts)
                        , alignmentSoFar = maximum (fmap (\context -> context.alignmentSoFar) contexts)
                        , unboxedAlignmentSoFar = maximum (fmap (\context -> context.unboxedAlignmentSoFar) contexts)
                        }
            -- We store the tag after everything else in order to waste a little less space
            let tagSize = Size.fromBits (smallestPowerOfTwoFitting (length constructors))
            -- It's extremely unlikely for this to not be 1 but we still need to cover the case where it isn't
            let tagAlignment = Alignment.fromValue (Size.inBytes tagSize)
            let tagLocation =
                    UnboxedOffset
                        { inFlightOffsetInBytes = combinedContext.inFlightUnboxedOffsetSoFar
                        , size = tagSize
                        , alignment = tagAlignment
                        }

            -- We don't currently use the fact that the tag size can be smaller than a byte
            let contextWithTag =
                    MkLayoutContext
                        { inFlightUnboxedOffsetSoFar = Alignment.align tagAlignment combinedContext.inFlightUnboxedOffsetSoFar + Size.inBytes tagSize
                        , --
                          alignmentSoFar = max tagAlignment context.alignmentSoFar
                        , unboxedAlignmentSoFar = max tagAlignment context.unboxedAlignmentSoFar
                        , boxedCountSoFar = combinedContext.boxedCountSoFar
                        }

            pure (contextWithTag, TopLevelSumLayout{tagSize, tagLocation, constructors = constructorDetails})
    go context = \case
        Core.ProductRep elements -> do
            -- TODO: reorder elements based on their size.
            -- We don't actually know the real size here so we need some sort of approximation,
            -- but naively approximating on every element is going to be quadratic so we need to
            -- pre-compute our approximations
            (newContext, elementDetails) <- mapAccumLM go context elements
            pure (newContext, ProductLayout elementDetails)
        -- Booleans have a special-cased layout
        Core.SumRep [Core.ProductRep [], Core.ProductRep []] -> do
            let offset = context.inFlightUnboxedOffsetSoFar
            let (context, _) = asUnboxedPrimitive context (Size.fromBits 1) (Alignment.fromValue 1)
            pure (context, NestedSumLayout{boxedIndices = [], decomposedIndices = [], unboxedOffset = Just offset, layout = boolLayout})
        Core.SumRep Empty -> do
            pure (context, ProductLayout{elements = []})
        representation@(Core.SumRep (NonEmpty _)) -> do
            layout <- representationLayout representation

            let boxedIndices = [context.boxedCountSoFar .. (context.boxedCountSoFar + layout.boxedCount - 1)]

            -- We currently never produce decomposed scalars for (regular) sums so we can ignore them here.
            -- This might change in the future! If it does, we need to actually incorporate them here by
            -- either keeping them decomposed (and recording them in the context accordingly) or (more likely)
            -- extending the unboxed section with them like we would for values at-rest
            -- (although we *cannot* do this for boxed values since we still need to access them decomposed as GC roots)
            let !() = assert (Seq.null layout.decomposedScalars) ()
            let unboxedOffset = case context.inFlightUnboxedOffsetSoFar + Size.inBytes (unboxedSize layout) of
                    0 -> Nothing
                    offset -> Just offset

            let details = NestedSumLayout{layout, boxedIndices, decomposedIndices = [], unboxedOffset}

            pure
                ( MkLayoutContext
                    { boxedCountSoFar = context.boxedCountSoFar + layout.boxedCount
                    , inFlightUnboxedOffsetSoFar = context.inFlightUnboxedOffsetSoFar + Size.inBytes (unboxedSize layout)
                    , alignmentSoFar = max context.alignmentSoFar layout.alignment
                    , unboxedAlignmentSoFar = max context.unboxedAlignmentSoFar layout.unboxedAlignment
                    }
                , details
                )
        Core.ArrayRep _elementRep -> go context (Core.PrimitiveRep Vega.BoxedRep)
        Core.PrimitiveRep primitive -> case primitive of
            Vega.BoxedRep -> do
                pure
                    ( MkLayoutContext
                        { boxedCountSoFar = context.boxedCountSoFar + 1
                        , alignmentSoFar = max context.alignmentSoFar pointerAlignment
                        , --
                          inFlightUnboxedOffsetSoFar = context.inFlightUnboxedOffsetSoFar
                        , unboxedAlignmentSoFar = context.unboxedAlignmentSoFar
                        }
                    , Primitive (BoxedScalar{inFlightIndex = context.boxedCountSoFar})
                    )
            Vega.IntRep{sizeInBits} -> do
                let size = Size.fromBits sizeInBits
                pure $ asUnboxedPrimitive context size (Alignment.fromValue (Size.inBytes size))
            Vega.PointerRep -> pure $ asUnboxedPrimitive context pointerSize pointerAlignment
            Vega.DoubleRep -> pure $ asUnboxedPrimitive context (Size.fromBytes 8) (Alignment.fromValue 8)
        rep@Core.ParameterRep{} -> panic $ "Non-monomorphized parameter representation in layout generation: " <> pretty rep
    asUnboxedPrimitive context size alignment = do
        let ownInFlightUnboxedOffset = Alignment.align alignment context.inFlightUnboxedOffsetSoFar
        ( MkLayoutContext
                { inFlightUnboxedOffsetSoFar = ownInFlightUnboxedOffset + Size.inBytes size
                , alignmentSoFar = max context.alignmentSoFar alignment
                , unboxedAlignmentSoFar = max context.unboxedAlignmentSoFar alignment
                , --
                  boxedCountSoFar = context.boxedCountSoFar
                }
            , Primitive (UnboxedOffset{inFlightOffsetInBytes = ownInFlightUnboxedOffset, size, alignment})
            )

tryDecomposedRepresentationLayout :: (?context :: LLVM.Context) => Representation -> Maybe Layout
tryDecomposedRepresentationLayout representation = case representation of
    -- We currently only decompose up to two elements (which is also what rustc does)
    -- It might be nice to decompose more? idk
    Core.ProductRep Empty -> Just unitLayout
    Core.ProductRep (NonEmpty elements)
        | length elements <= 2 -> do
            ((boxedCount, _), layouts) <- forAccumLM (0, 0) elements \(boxedCount, unboxedScalarCount) element -> do
                layout <- asDecomposedScalar element (boxedCount, unboxedScalarCount)
                Just ((boxedCount + layout.boxedCount, unboxedScalarCount + length layout.decomposedScalars), layout)
            Just $
                MkLayout
                    { size = totalSize $ fmap (\layout -> (layout.size, layout.alignment)) layouts
                    , alignment = maximum (fmap (\layout -> layout.alignment) layouts)
                    , boxedCount
                    , decomposedScalars = computeScalarOffsets $ foldMap (\layout -> layout.decomposedScalars) layouts
                    , unboxedAlignment = Alignment.fromValue 1
                    , unboxedSize = Size.fromBytes 0
                    , details = Simple $ ProductLayout (fmap (\layout -> layout.details) (NonEmpty.toSeq layouts))
                    }
        | otherwise -> Nothing
    _ -> completeLayout <$> asDecomposedScalar representation (0, 0)
  where
    asDecomposedScalar representation (boxedIndex, unboxedIndex) = case representation of
        Core.PrimitiveRep primitive -> case primitive of
            Vega.BoxedRep ->
                Just $
                    MkPartialLayout
                        { size = Size.fromBytes 8
                        , alignment = Alignment.fromValue 8
                        , boxedCount = 1
                        , decomposedScalars = []
                        , unboxedAlignment = Alignment.fromValue 1
                        , unboxedSize = Size.fromBytes 0
                        , details = Primitive (BoxedScalar boxedIndex)
                        }
            Vega.PointerRep -> scalarAsLayout unboxedIndex (Size.fromBytes 8) (Alignment.fromValue 8) LLVM.pointerType
            Vega.IntRep{sizeInBits} -> do
                let size = Size.fromBits sizeInBits
                scalarAsLayout unboxedIndex size (Alignment.fromValue (Size.inBytes size)) (LLVM.intType sizeInBits)
            Vega.DoubleRep -> scalarAsLayout unboxedIndex (Size.fromBytes 8) (Alignment.fromValue 8) LLVM.doubleType
        -- It's important that we include this here so that `((), Int)` will be decomposed to a single `i64` scalar
        Core.ProductRep Empty -> Just partialUnitLayout
        Core.SumRep Empty -> Just partialUnitLayout
        Core.SumRep [Core.ProductRep Empty, Core.ProductRep Empty] -> Just (partialBoolLayout unboxedIndex)
        Core.SumRep{} -> Nothing
        Core.ProductRep{} -> Nothing
        Core.ArrayRep{} -> asDecomposedScalar (Core.PrimitiveRep Vega.BoxedRep) (boxedIndex, unboxedIndex)
        rep@Core.ParameterRep{} -> panic $ "Non-monomorphized parameter representation in layout generation: " <> pretty rep
    scalarAsLayout index size alignment type_ =
        Just
            MkPartialLayout
                { size
                , alignment
                , boxedCount = 0
                , decomposedScalars = [(type_, size, alignment)]
                , unboxedAlignment = Alignment.fromValue 1
                , unboxedSize = Size.fromBytes 0
                , details = Primitive (DecomposedScalar index)
                }

{- | Like regular layouts but keeps *nested* layout details
This is relevant for (simple) scalar decomposition where we never generate
a top-level sum anyway since we (currently) only decompose all or nothing
-}
data PartialLayout = MkPartialLayout
    { size :: Size
    , alignment :: Alignment
    , boxedCount :: Int
    , decomposedScalars :: Seq (LLVM.Type, Size, Alignment)
    , unboxedAlignment :: Alignment
    , unboxedSize :: Size
    , details :: NestedLayoutDetails
    }
    deriving (Show)

completeLayout :: PartialLayout -> Layout
completeLayout MkPartialLayout{size, alignment, boxedCount, decomposedScalars, unboxedAlignment, unboxedSize, details} =
    case details of
        -- Nested sums already store their own representation so we can skip the partial layout information we have in that case
        NestedSumLayout{layout} -> layout
        _ ->
            MkLayout
                { size
                , alignment
                , boxedCount
                , decomposedScalars = computeScalarOffsets decomposedScalars
                , unboxedAlignment
                , unboxedSize
                , details = Simple details
                }

computeScalarOffsets :: Seq (LLVM.Type, Size, Alignment) -> Seq (LLVM.Type, Int)
computeScalarOffsets partialScalars = flip evalState 0 $ for partialScalars \(type_, size, alignment) -> do
    currentOffset <- get
    let offset = Alignment.align alignment currentOffset
    put $ currentOffset + Size.inBytes size
    pure (type_, offset)

totalSize :: (Foldable f) => f (Size, Alignment) -> Size
totalSize foldable = Size.fromBytes $ foldl' addElement 0 foldable
  where
    addElement currentSizeInBytes (size, alignment) =
        Alignment.align alignment currentSizeInBytes + Size.inBytes size

pointerAlignment :: Alignment
pointerAlignment = Alignment.fromValue 8

pointerSize :: Size
pointerSize = Size.fromBytes 8

partialUnitLayout :: PartialLayout
partialUnitLayout =
    MkPartialLayout
        { size = Size.fromBytes 0
        , alignment = Alignment.fromValue 1
        , boxedCount = 0
        , decomposedScalars = []
        , unboxedAlignment = Alignment.fromValue 1
        , unboxedSize = Size.fromBytes 0
        , details = ProductLayout []
        }

unitLayout :: (?context :: LLVM.Context) => Layout
-- We don't currently need the context here but it's better not to leak this to usages unnecessarily
-- in case it changes in the future.
unitLayout = completeLayout partialUnitLayout

partialBoolLayout :: (?context :: LLVM.Context) => Int -> PartialLayout
partialBoolLayout decomposedIndex =
    MkPartialLayout
        { size = Size.fromBytes 1
        , alignment = Alignment.fromValue 1
        , boxedCount = 0
        , decomposedScalars = [(LLVM.int1Type, Size.fromBits 1, Alignment.fromValue 1)]
        , unboxedAlignment = Alignment.fromValue 1
        , unboxedSize = Size.fromBytes 0
        , details =
            NestedSumLayout{boxedIndices = [], decomposedIndices = [decomposedIndex], unboxedOffset = Nothing, layout = boolLayout}
        }
boolLayout :: (?context :: LLVM.Context) => Layout
boolLayout =
    MkLayout
        { size = Size.fromBytes 1
        , alignment = Alignment.fromValue 1
        , boxedCount = 0
        , decomposedScalars = [(LLVM.int1Type, 0)]
        , unboxedAlignment = Alignment.fromValue 1
        , unboxedSize = Size.fromBytes 0
        , details =
            TopLevelSumLayout
                { tagSize = Size.fromBits 1
                , tagLocation = DecomposedScalar 0
                , constructors = (ProductLayout [] :<|| [ProductLayout []])
                }
        }

boxedLayout :: (?context :: LLVM.Context) => Layout
boxedLayout = runPureEff $ representationLayout $ Core.PrimitiveRep Vega.BoxedRep

rawPointerLayout :: (?context :: LLVM.Context) => Layout
rawPointerLayout = runPureEff $ representationLayout $ Core.PrimitiveRep Vega.PointerRep

intLayout :: (?context :: LLVM.Context) => Size -> Layout
intLayout size = runPureEff $ representationLayout $ Core.PrimitiveRep (Vega.IntRep{sizeInBits = Size.inBits size})

byteArrayLayout :: (?context :: LLVM.Context) => Layout
byteArrayLayout = runPureEff $ representationLayout $ Core.ArrayRep (Core.PrimitiveRep (Vega.IntRep{sizeInBits = 8}))

closureLayout :: (?context :: LLVM.Context) => Layout
closureLayout = runPureEff $ representationLayout $ Core.functionRepresentation

assertBoxed :: (HasCallStack) => CompoundValue -> LLVM.Value
assertBoxed = \case
    MkCompoundValue{boxed = [boxed], decomposedScalars = [], unboxedPointer = Nothing} -> boxed
    value -> panic $ "Unexpected non-boxed compound value " <> pretty value

assertScalar :: (HasCallStack) => CompoundValue -> LLVM.Value
assertScalar = \case
    MkCompoundValue{boxed = [], decomposedScalars = [scalar], unboxedPointer = Nothing} -> scalar
    value -> panic $ "Unexpected non-scalar compound value " <> pretty value

{- | Assert that this only contains a single decomposed LLVM Value. This value might however
be boxed or a regular decomposed scalar.

If possible, you should use assertBoxed or assertScalar instead of this since we need to treat boxed values
a bit differently and these kinds of bugs are very hard to catch otherwise
-}
assertSingleValue :: (HasCallStack) => CompoundValue -> LLVM.Value
assertSingleValue = \case
    MkCompoundValue{boxed = [boxed], decomposedScalars = [], unboxedPointer = Nothing} -> boxed
    MkCompoundValue{boxed = [], decomposedScalars = [scalar], unboxedPointer = Nothing} -> scalar
    value -> panic $ "Unexpected complex compound value " <> pretty value

closurePayload :: (?context :: LLVM.Context) => ElementLocation
closurePayload = case details closureLayout of
    Simple (ProductLayout [_functionPointer, Primitive location]) -> location
    _ -> panic $ "unexpected closure layout"

closureFunctionPointer :: (?context :: LLVM.Context) => ElementLocation
closureFunctionPointer = case details closureLayout of
    Simple (ProductLayout [Primitive location, _payload]) -> location
    _ -> panic "unexpected closure layout"