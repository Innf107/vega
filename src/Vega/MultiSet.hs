{- | A multiset supporting negative multiplicities and fast unions.

In all complexities in this module `n` is the number of *distinct* entries
-}
module Vega.MultiSet (
    MultiSet,
    isEmpty,
    member,
    toMultiplicityList,
    multiplicities,
    distinctKeys,
    empty,
    negate,
    mapMultiplicity,
    scaleMultiplicity,
    union,
    partition,
    mapMultiplicityNonZero,
    deleteAll,
    fromMultiplicityList,
) where

import Data.Map.Merge.Strict qualified as Map.Merge
import Data.Map.Strict qualified as Map
import GHC.IsList (IsList (..))
import Relude hiding (empty, negate)

-- | A multiset supporting negative multiplicities and fast unions
newtype MultiSet a = MkMultiSet (Map a Int)

-- We cannot use HashMap here since we need fast unions on our multisets and HashMap unions are linear
type role MultiSet nominal

-- | O(1)
isEmpty :: MultiSet a -> Bool
isEmpty (MkMultiSet set) = Map.null set

-- | O(n)
toMultiplicityList :: MultiSet a -> [(a, Int)]
toMultiplicityList (MkMultiSet set) = Map.toList set

-- | O(n log(n))
fromMultiplicityList :: (Ord a) => [(a, Int)] -> MultiSet a
fromMultiplicityList multiplicities = MkMultiSet $ Map.fromList (filter (\(_, multiplicity) -> multiplicity /= 0) multiplicities)

-- | O(n)
multiplicities :: MultiSet a -> [Int]
multiplicities (MkMultiSet set) = Relude.toList set

-- | O(n)
distinctKeys :: MultiSet a -> [a]
distinctKeys (MkMultiSet map) = Map.keys map

empty :: MultiSet a
empty = MkMultiSet Map.empty

-- | O(log(n))
member :: (Ord a) => a -> MultiSet a -> Bool
member x (MkMultiSet set) = Map.member x set

{- | Negate the multiplicities of all elements
O(n)
-}
negate :: (Ord a) => MultiSet a -> MultiSet a
negate (MkMultiSet set) = MkMultiSet $ fmap (\x -> -x) set

-- | O(n)
mapMultiplicity :: (Ord a) => (Int -> Int) -> MultiSet a -> MultiSet a
mapMultiplicity f (MkMultiSet set) = MkMultiSet $ Map.mapMaybe (\x -> case f x of 0 -> Nothing; y -> Just y) set

-- Apply a function to every element of the map under the assumption that it never returns 0.
-- This condition is NOT checked.

-- | O(n)
mapMultiplicityNonZero :: (Ord a) => (Int -> Int) -> MultiSet a -> MultiSet a
mapMultiplicityNonZero f (MkMultiSet set) = MkMultiSet $ Map.map f set

-- Equivalent to @mapMultiplicity (* scale)@ but more efficient

-- | O(n)
scaleMultiplicity :: (Ord a) => Int -> MultiSet a -> MultiSet a
scaleMultiplicity 0 _ = empty
scaleMultiplicity scale (MkMultiSet multiset) = MkMultiSet $ fmap (* scale) multiset

-- | O(log(n)) (probably, Map.Merge.Strict.merge doesn't actually specify its complexity)
union :: (Ord a) => MultiSet a -> MultiSet a -> MultiSet a
union (MkMultiSet set1) (MkMultiSet set2) =
    MkMultiSet $ Map.Merge.merge Map.Merge.preserveMissing Map.Merge.preserveMissing (Map.Merge.zipWithMaybeMatched addMaybe) set1 set2
  where
    addMaybe _key x y = case x + y of
        0 -> Nothing
        sum -> Just sum

-- | O(n)
partition :: (Ord a) => (a -> Bool) -> MultiSet a -> (MultiSet a, MultiSet a)
partition f (MkMultiSet set) = do
    let !(passed, failed) = Map.partitionWithKey (\key _ -> f key) set
    (MkMultiSet passed, MkMultiSet failed)

-- | O(log(n))
deleteAll :: (Ord a) => a -> MultiSet a -> MultiSet a
deleteAll key (MkMultiSet set) = MkMultiSet (Map.delete key set)

instance (Ord a) => Semigroup (MultiSet a) where
    (<>) = union

instance (Ord a) => Monoid (MultiSet a) where
    mempty = empty

instance (Ord a) => IsList (MultiSet a) where
    type Item (MultiSet a) = a
    toList set = concatMap (\(x, count) -> replicate count x) (toMultiplicityList set)
    fromList :: (Ord a) => [Item (MultiSet a)] -> MultiSet a
    fromList list = MkMultiSet $ Map.fromListWith (+) (fmap (,1) list)

instance (Eq a) => Eq (MultiSet a) where
    MkMultiSet map1 == MkMultiSet map2 = map1 == map2
