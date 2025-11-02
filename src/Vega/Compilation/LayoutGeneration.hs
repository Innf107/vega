module Vega.Compilation.LayoutGeneration where

import Effectful
import Relude hiding (NonEmpty, Type)

import Data.Bits (FiniteBits (countLeadingZeros), finiteBitSize)
import Data.Sequence (Seq (..))
import Vega.Compilation.LIR.Syntax (Layout (..), UnboxedLayout (..))
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Seq.NonEmpty (pattern NonEmpty)
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Syntax (PrimitiveRep (..), Type (..))
import Vega.Util (These (..), forIndexed, zipWithLongest)

-- Unboxed layouts are sorted, first by 'type' (floats come before ints)
-- and then by size. We choose this order to simplify compaction.
-- Sums only need to add their tag at the back to (ideally) have it merged with
-- the remaining values.
newtype ValueSequence = UncheckedMkSortedValueSequence (Seq UnboxedLayout)

data ReverseProjection
    = FullType
    | -- | Projections where several values are packed into one 'slot'
      ReverseProjectPacked
        { baseProjection :: ReverseProjection
        , offset :: Int
        , nextProjection :: ReverseProjection
        }
    | ReverseProjectProduct Int ReverseProjection
    | ReverseProjectSum Int ReverseProjection
    | NoProjection
    | UnionReverseProjection ReverseProjection ReverseProjection

data TypeLayoutBuilder = TypeLayoutBuilder
    { boxedPointers :: Seq ReverseProjection
    , values :: Seq (ReverseProjection, UnboxedLayout)
    }

buildLayout :: TypeLayoutBuilder -> TypeLayout
buildLayout builder = do
    undefined

data TypeLayout = TypeLayout
    { numberOfBoxedPointers :: Int
    , values :: ValueSequence
    , projection :: LayoutProjection
    }

data LayoutProjection
    = ProjectSingleton
        { offsetInBits :: Int
        }
    | ProjectProduct
        { numberOfFields :: Int
        , projectedPositions :: HashMap Int LayoutProjection
        }
    | ProjectSum
        { numberOfConstructors :: Int
        , projectedSubLayouts :: HashMap Int LayoutProjection
        }

unitLayout :: TypeLayoutBuilder
unitLayout = TypeLayoutBuilder{boxedPointers = [], values = []}

singletonLayout :: ReverseProjection -> Layout -> TypeLayoutBuilder
singletonLayout reverseProjection = \case
    BoxedLayout -> TypeLayoutBuilder{boxedPointers = [reverseProjection], values = []}
    UnboxedLayout layout -> TypeLayoutBuilder{boxedPointers = [], values = [(reverseProjection, layout)]}

concatenateLayout :: TypeLayoutBuilder -> TypeLayoutBuilder -> TypeLayoutBuilder
concatenateLayout layout1 layout2 = do
    TypeLayoutBuilder
        { boxedPointers = layout1.boxedPointers <> layout2.boxedPointers
        , values = mergeValueConcatenation layout1.values layout2.values
        }

unionLayout :: TypeLayoutBuilder -> TypeLayoutBuilder -> TypeLayoutBuilder
unionLayout layout1 layout2 = do
    let mergeBoxedPointer = \case
            This reverseProjection -> reverseProjection
            That reverseProjection -> reverseProjection
            Both reverseProjection1 reverseProjection2 -> do
                UnionReverseProjection reverseProjection1 reverseProjection2

    TypeLayoutBuilder
        { boxedPointers = zipWithLongest mergeBoxedPointer layout1.boxedPointers layout2.boxedPointers
        , values = mergeValueUnion layout1.values layout2.values
        }

mergeValueConcatenation :: Seq (ReverseProjection, UnboxedLayout) -> Seq (ReverseProjection, UnboxedLayout) -> Seq (ReverseProjection, UnboxedLayout)
mergeValueConcatenation values1 values2 = case (values1, values2) of
    (Empty, values2) -> values2
    (values1, Empty) -> values1
    ((projection1, FloatLayout size1) :<| rest1, (projection2, FloatLayout size2) :<| rest2)
        | size1 + size2 <= maxFloatSize ->
            (ReverseProjectPacked projection1 size1 projection2, FloatLayout (size1 + size2)) :<| mergeValueConcatenation rest1 rest2
        | size1 > size2 ->
            (projection1, FloatLayout size1)
                :<| (projection2, FloatLayout size2)
                :<| mergeValueConcatenation rest1 rest2
        | otherwise ->
            (projection2, FloatLayout size2)
                :<| (projection1, FloatLayout size1)
                :<| mergeValueConcatenation rest1 rest2
    ((projection1, IntLayout size1) :<| rest1, (projection2, IntLayout size2) :<| rest2)
        | size1 + size2 <= maxIntSize ->
            (ReverseProjectPacked projection1 size1 projection2, IntLayout (size1 + size2))
                :<| mergeValueConcatenation rest1 rest2
        | size1 > size2 ->
            (projection1, IntLayout size1)
                :<| (projection2, IntLayout size2)
                :<| mergeValueConcatenation rest1 rest2
        | otherwise ->
            (projection2, IntLayout size2)
                :<| (projection1, IntLayout size1)
                :<| mergeValueConcatenation rest1 rest2
    ((projection1, FloatLayout size1) :<| rest1, values2@((_, IntLayout _) :<| _)) ->
        -- Floats are sorted before ints
        (projection1, FloatLayout size1) :<| mergeValueConcatenation rest1 values2
    (values1@((_, IntLayout _) :<| _), (projection2, FloatLayout size2) :<| rest2) ->
        (projection2, FloatLayout size2) :<| mergeValueConcatenation values1 rest2

mergeValueUnion :: Seq (ReverseProjection, UnboxedLayout) -> Seq (ReverseProjection, UnboxedLayout) -> Seq (ReverseProjection, UnboxedLayout)
mergeValueUnion values1 values2 = go values1 values2
  where
    go :: Seq (ReverseProjection, UnboxedLayout) -> Seq (ReverseProjection, UnboxedLayout) -> Seq (ReverseProjection, UnboxedLayout)
    go values1 values2 = case (values1, values2) of
        (Empty, values2) -> values2
        (values1, Empty) -> values1
        (values1@((_, IntLayout size1) :<| _), values2@((_, IntLayout size2) :<| _)) -> do
            let size = max size1 size2
            let (projection1, rest1) = dropIntPrefixSummingTo size values1
            let (projection2, rest2) = dropIntPrefixSummingTo size values2
            (UnionReverseProjection projection1 projection2, IntLayout size) :<| go rest1 rest2
        (values1@((_, FloatLayout size1) :<| _), values2@((_, FloatLayout size2) :<| _)) -> do
            let size = max size1 size2
            let (projection1, rest1) = dropFloatPrefixSummingTo size values1
            let (projection2, rest2) = dropFloatPrefixSummingTo size values2
            (UnionReverseProjection projection1 projection2, FloatLayout size) :<| go rest1 rest2
        ((projection1, FloatLayout size1) :<| rest1, layouts2@((_, IntLayout _) :<| _)) -> do
            -- floats are sorted before ints
            (projection1, FloatLayout size1) :<| go rest1 layouts2
        (layouts1@((_, IntLayout _) :<| _), (projection2, FloatLayout size2) :<| rest2) -> do
            -- floats are sorted before ints
            (projection2, FloatLayout size2) :<| go layouts1 rest2

    dropIntPrefixSummingTo size = \case
        ((projection, IntLayout smaller) :<| rest)
            | smaller <= size ->
                case dropIntPrefixSummingTo (size - smaller) rest of
                    (NoProjection, layouts) -> (projection, layouts)
                    (nextProjection, layouts) -> (ReverseProjectPacked projection smaller nextProjection, layouts)
        layouts -> (NoProjection, layouts)
    dropFloatPrefixSummingTo size = \case
        ((projection, FloatLayout smaller) :<| rest)
            | smaller <= size ->
                case dropFloatPrefixSummingTo (size - smaller) rest of
                    (NoProjection, layouts) -> (projection, layouts)
                    (nextProjection, layouts) -> (ReverseProjectPacked projection smaller nextProjection, layouts)
        layouts -> (NoProjection, layouts)

layoutBuilderForRep :: (IOE :> es, GraphPersistence :> es) => ReverseProjection -> Type -> Eff es TypeLayoutBuilder
layoutBuilderForRep baseProjection = \case
    ProductRep elements -> do
        case elements of
            Empty -> pure unitLayout
            NonEmpty elements -> do
                elementLayouts <- forIndexed elements \elementRep index -> do
                    layoutBuilderForRep (ReverseProjectProduct index baseProjection) elementRep
                pure $ NonEmpty.foldl1' concatenateLayout elementLayouts
    SumRep alternatives -> do
        case alternatives of
            Empty -> pure unitLayout
            NonEmpty alternatives -> do
                alternativeLayouts <- forIndexed alternatives \alternativeRep index -> do
                    layoutBuilderForRep (ReverseProjectSum index baseProjection) alternativeRep
                let tag = UnboxedLayout (IntLayout (closestPowerOfTwo (length alternatives)))
                pure $ concatenateLayout (NonEmpty.foldl1' unionLayout alternativeLayouts) (singletonLayout NoProjection tag)
    PrimitiveRep rep -> case rep of
        UnitRep -> pure unitLayout
        -- TODO: can we use the fact that this won't ever happen and poison the entire layout or something?
        EmptyRep -> pure unitLayout
        BoxedRep -> pure (singletonLayout baseProjection BoxedLayout)
        IntRep -> pure (singletonLayout baseProjection (UnboxedLayout (IntLayout 64)))
        DoubleRep -> pure (singletonLayout baseProjection (UnboxedLayout (FloatLayout 64)))
    type_ -> panic $ "Trying to generate layout for non-representation type: " <> pretty type_

layoutForRep :: (IOE :> es, GraphPersistence :> es) => Type -> Eff es TypeLayout
layoutForRep rep = buildLayout <$> layoutBuilderForRep FullType rep

closestPowerOfTwo :: Int -> Int
closestPowerOfTwo x = finiteBitSize x - countLeadingZeros x

maxIntSize :: Int
maxIntSize = 64

maxFloatSize :: Int
maxFloatSize = 64
