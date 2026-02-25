module Vega.VectorMap (
    VectorMap,
    fromList,
    toList,
    sortedKeys,
    sortedValues,
    lookup,
    lookupIndex,
    size,
    find,
) where

import Relude hiding (find, fromList, toList)

import GHC.Exts qualified as Exts

import Data.Vector.Strict qualified as Strict
import Text.Show qualified as Show

data VectorMap k v = MkVectorMap
    { keys :: Strict.Vector k
    , values :: Strict.Vector v
    }
    deriving (Functor)

instance (Ord k) => Exts.IsList (VectorMap k v) where
    type Item (VectorMap k v) = (k, v)

    fromList = fromList
    toList = toList

instance (Show k, Show v) => Show (VectorMap k v) where
    show map = "fromList " <> show (toList map)

fromList :: (Ord k) => [(k, v)] -> VectorMap k v
fromList elements = do
    let sorted = sortBy (compare `on` fst) elements
    MkVectorMap
        { keys = Strict.fromList (map fst sorted)
        , values = Strict.fromList (map snd sorted)
        }

toList :: VectorMap k v -> [(k, v)]
toList map = zip (Strict.toList map.keys) (Strict.toList map.values)

instance Foldable (VectorMap k) where
    foldMap f map = foldMap f map.values

instance Traversable (VectorMap k) where
    traverse f map = do
        values <- traverse f map.values
        pure (map{values})

-- | O(1)
sortedKeys :: VectorMap k v -> Strict.Vector k
sortedKeys map = map.keys

-- | O(1)
sortedValues :: VectorMap k v -> Strict.Vector v
sortedValues map = map.values

-- | O(log(n))
lookup :: (Ord k) => k -> VectorMap k v -> Maybe v
lookup key map = do
    index <- lookupIndex key map
    pure (map.values Strict.! index)

find :: (HasCallStack, Ord k) => k -> VectorMap k v -> v
find key map = case lookup key map of
    Just value -> value
    Nothing -> error "VectorMap.find: key not found"

-- | O(log(n))
lookupIndex :: (Ord k) => k -> VectorMap k v -> Maybe Int
lookupIndex key map = do
    let go start end
            | end <= start = -1
            | otherwise = do
                let pivot = (start + end) `div` 2
                case compare key (map.keys Strict.! pivot) of
                    EQ -> pivot
                    LT -> go start pivot
                    GT -> go (pivot + 1) end
    case go 0 (size map) of
        -1 -> Nothing
        index -> Just index

-- | O(1)
size :: VectorMap k v -> Int
size map = Strict.length map.keys
