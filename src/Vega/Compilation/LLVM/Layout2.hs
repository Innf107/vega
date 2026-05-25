module Vega.Compilation.LLVM.Layout2 (
    Layout,
    representationLayout,
    CompoundValue (..),
) where

import Data.Bits qualified as Bits
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Effectful (Eff)
import LLVM.Core qualified as LLVM
import LLVM.Core.Context qualified as LLVM
import Relude hiding (NonEmpty, catMaybes, mapMaybe)
import System.IO.Unsafe (unsafePerformIO)
import Text.Show (Show (..))
import Vega.Alignment (Alignment)
import Vega.Alignment qualified as Alignment
import Vega.Alignment qualified as Vega
import Vega.Compilation.Core.Syntax (Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Debug (showHeadConstructor)
import Vega.Panic (panic)
import Vega.Pretty (number, pretty)
import Vega.Seq.NonEmpty (NonEmpty, maximum, pattern NonEmpty)
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Size (Size)
import Vega.Size qualified as Size
import Vega.Syntax qualified as Vega
import Vega.Util (forAccumLM, forIndexed, smallestPowerOfTwoFitting)
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
    , alignment :: Vega.Alignment
    , boxedCount :: Int
    , decomposedScalars :: Seq (LLVM.Type, Size, Alignment)
    , unboxedAlignment :: Vega.Alignment
    , unboxedSize :: Size
    , details :: LayoutDetails
    }
    deriving (Show)

-- | The size of the decomposed values in a layout at rest *including padding*.
decomposedStride :: Layout -> Size
decomposedStride layout =
    Size.fromBytes $
        Size.inBytes layout.size
            - Size.inBytes layout.unboxedSize
            - layout.boxedCount * Size.inBytes pointerSize

atRestUnboxedOffset :: Layout -> Int
atRestUnboxedOffset layout =
    layout.boxedCount * Size.inBytes pointerSize + Size.inBytes (decomposedStride layout)

data CompoundValue = MkCompoundValue
    { boxed :: Seq LLVM.Value
    , decomposedScalars :: Seq LLVM.Value
    , unboxedPointer :: Maybe LLVM.Value
    }

data ElementLocation
    = BoxedScalar {inFlightIndex :: Int}
    | DecomposedScalar {inFlightIndex :: Int}
    | UnboxedOffset {inFlightOffsetInBytes :: Int}
    deriving (Generic, Show)

atRestOffsetInBytes :: ElementLocation -> Layout -> Int
atRestOffsetInBytes location layout = case location of
    -- See Note [At-rest vs in-flight] for why we can compute these offsets this way
    BoxedScalar{inFlightIndex} -> inFlightIndex * Size.inBytes pointerSize
    DecomposedScalar{inFlightIndex} -> undefined
    UnboxedOffset{inFlightOffsetInBytes} -> Alignment.align layout.unboxedAlignment (atRestUnboxedOffset layout) + inFlightOffsetInBytes

data LayoutDetails
    = ProductLayout {elements :: Seq LayoutDetails}
    | SumLayout {tagSize :: Size, inFlightTagOffsetInBytes :: Int, constructors :: NonEmpty LayoutDetails}
    | Primitive ElementLocation
    deriving (Generic, Show)

data LayoutContext = MkLayoutContext
    { boxedCountSoFar :: Int
    , inFlightUnboxedOffsetSoFar :: Int
    , alignmentSoFar :: Alignment
    , unboxedAlignmentSoFar :: Alignment
    }

representationLayout :: (?context :: LLVM.Context) => Representation -> Layout
representationLayout representation = do
    case tryDecomposedRepresentationLayout representation of
        Just layout -> layout
        Nothing -> do
            let initialContext =
                    MkLayoutContext
                        { boxedCountSoFar = 0
                        , alignmentSoFar = Alignment.fromValue 1
                        , unboxedAlignmentSoFar = Alignment.fromValue 1
                        , inFlightUnboxedOffsetSoFar = 0
                        }
            let (context, details) = go initialContext representation

            let size = Size.fromBytes (context.boxedCountSoFar * Size.inBytes pointerSize + context.inFlightUnboxedOffsetSoFar)
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
    go context = \case
        Core.ProductRep elements -> do
            -- TODO: reorder elements based on their size.
            -- We don't actually know the real size here so we need some sort of approximation,
            -- but naively approximating on every element is going to be quadratic so we need to
            -- pre-compute our approximations
            let (newContext, elementDetails) = mapAccumL go context elements
            (newContext, ProductLayout elementDetails)
        -- Booleans have a special-cased layout
        Core.SumRep [Core.ProductRep [], Core.ProductRep []] -> do
            asUnboxedPrimitive context (Size.fromBits 1) (Alignment.fromValue 1)
        Core.SumRep Empty -> do
            (context, ProductLayout{elements = []})
        Core.SumRep (NonEmpty constructors) -> do
            -- TODO: we could filter out Empty's here (and possibly get rid of the sum alltogether)
            -- if we do, we need to maintain the correct constructor indices though
            let (contexts, constructorDetails) = NonEmpty.unzip $ fmap (go context) constructors
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
            let inFlightTagOffsetInBytes = combinedContext.inFlightUnboxedOffsetSoFar

            -- We don't currently use the fact that the tag size can be smaller than a byte
            let contextWithTag =
                    MkLayoutContext
                        { inFlightUnboxedOffsetSoFar = Alignment.align tagAlignment combinedContext.inFlightUnboxedOffsetSoFar + Size.inBytes tagSize
                        , --
                          alignmentSoFar = max tagAlignment context.alignmentSoFar
                        , unboxedAlignmentSoFar = max tagAlignment context.unboxedAlignmentSoFar
                        , boxedCountSoFar = combinedContext.boxedCountSoFar
                        }

            (contextWithTag, SumLayout{tagSize, inFlightTagOffsetInBytes, constructors = constructorDetails})
        Core.ArrayRep _elementRep -> go context (Core.PrimitiveRep Vega.BoxedRep)
        Core.PrimitiveRep primitive -> case primitive of
            Vega.BoxedRep -> do
                ( MkLayoutContext
                        { boxedCountSoFar = context.boxedCountSoFar + 1
                        , alignmentSoFar = max context.alignmentSoFar pointerAlignment
                        , --
                          inFlightUnboxedOffsetSoFar = context.inFlightUnboxedOffsetSoFar
                        , unboxedAlignmentSoFar = context.unboxedAlignmentSoFar
                        }
                    , Primitive (BoxedScalar{inFlightIndex = context.boxedCountSoFar})
                    )
            Vega.IntRep{sizeInBits} -> asUnboxedPrimitive context (Size.fromBits sizeInBits) (Alignment.fromValue (8 * sizeInBits))
            Vega.PointerRep -> asUnboxedPrimitive context pointerSize pointerAlignment
            Vega.DoubleRep -> asUnboxedPrimitive context (Size.fromBytes 8) (Alignment.fromValue 8)
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
            , Primitive (UnboxedOffset{inFlightOffsetInBytes = ownInFlightUnboxedOffset})
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
                    , decomposedScalars = foldMap (\layout -> layout.decomposedScalars) layouts
                    , unboxedAlignment = Alignment.fromValue 1
                    , unboxedSize = Size.fromBytes 0
                    , details = ProductLayout (fmap (\layout -> layout.details) (NonEmpty.toSeq layouts))
                    }
        | otherwise -> Nothing
    _ -> asDecomposedScalar representation (0, 0)
  where
    asDecomposedScalar representation (boxedIndex, unboxedIndex) = case representation of
        Core.PrimitiveRep primitive -> case primitive of
            Vega.BoxedRep ->
                Just $
                    MkLayout
                        { size = Size.fromBytes 8
                        , alignment = Alignment.fromValue 8
                        , boxedCount = 1
                        , decomposedScalars = []
                        , unboxedAlignment = Alignment.fromValue 1
                        , unboxedSize = Size.fromBytes 0
                        , details = Primitive (BoxedScalar boxedIndex)
                        }
            Vega.PointerRep -> scalarAsLayout unboxedIndex (Size.fromBytes 8) (Alignment.fromValue 8) LLVM.pointerType
            Vega.IntRep{sizeInBits} -> scalarAsLayout unboxedIndex (Size.fromBits sizeInBits) (Alignment.fromValue (8 * sizeInBits)) (LLVM.intType (8 * sizeInBits))
            Vega.DoubleRep -> scalarAsLayout unboxedIndex (Size.fromBytes 8) (Alignment.fromValue 8) LLVM.doubleType
        -- It's important that we include this here so that `((), Int)` will be decomposed to a single `i64` scalar
        Core.ProductRep Empty -> Just unitLayout
        Core.SumRep Empty -> Just unitLayout
        Core.SumRep [Core.ProductRep Empty, Core.ProductRep Empty] ->
            scalarAsLayout unboxedIndex (Size.fromBits 1) (Alignment.fromValue 1) LLVM.int1Type
        Core.SumRep{} -> Nothing
        Core.ProductRep{} -> Nothing
        Core.ArrayRep{} -> asDecomposedScalar (Core.PrimitiveRep Vega.BoxedRep) (boxedIndex, unboxedIndex)
        rep@Core.ParameterRep{} -> panic $ "Non-monomorphized parameter representation in layout generation: " <> pretty rep
    scalarAsLayout index size alignment type_ =
        Just
            MkLayout
                { size
                , alignment
                , boxedCount = 0
                , decomposedScalars = [(type_, size, alignment)]
                , unboxedAlignment = Alignment.fromValue 1
                , unboxedSize = Size.fromBytes 0
                , details = Primitive (DecomposedScalar index)
                }

totalSize :: (Foldable f) => f (Size, Alignment) -> Size
totalSize foldable = Size.fromBytes $ foldl' addElement 0 foldable
  where
    addElement currentSizeInBytes (size, alignment) =
        Alignment.align alignment currentSizeInBytes + Size.inBytes size

unitLayout :: Layout
unitLayout =
    MkLayout
        { size = Size.fromBytes 0
        , alignment = Alignment.fromValue 1
        , boxedCount = 0
        , decomposedScalars = []
        , unboxedAlignment = Alignment.fromValue 1
        , unboxedSize = Size.fromBytes 0
        , details = ProductLayout []
        }

pointerAlignment :: Alignment
pointerAlignment = Alignment.fromValue 8

pointerSize :: Size
pointerSize = Size.fromBytes 8
