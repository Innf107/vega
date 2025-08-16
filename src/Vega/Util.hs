{-# LANGUAGE AllowAmbiguousTypes #-}

module Vega.Util (
    seqAny2,
    zipWithSeqM,
    compose,
    unzip3Seq,
    findSeq,
    mapAccumLM,
    forAccumLM,
    viaList,
    constructorNames,
    Untagged (..),
    assert,
    for2,
    partitionWithSeq,
    frequencies,
) where

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import GHC.Base qualified
import GHC.Exts (IsList (..))
import GHC.Generics (C1, Generic (Rep), M1, Meta (..), (:+:))
import GHC.TypeLits (KnownSymbol, symbolVal)
import Relude hiding (toList)

{- | Check if any two elements in two @Seq@s zipped together pairwise satisfy some predicate.

    If one of the Seqs is longer than the other, the remaining elements of that Seq are discarded.

    O(min(n,m)) if none of the elements satisfy the predicate or O(i) if the predicate first becomes true at index i
-}
seqAny2 :: (a -> b -> Bool) -> Seq a -> Seq b -> Bool
seqAny2 _predicate Empty _ = False
seqAny2 _predicate _ Empty = False
seqAny2 predicate (x :<| xs) (y :<| ys) = predicate x y || seqAny2 predicate xs ys

zipWithSeqM :: (Applicative f) => (a -> b -> f c) -> Seq a -> Seq b -> f (Seq c)
zipWithSeqM _ Empty _ = pure Empty
zipWithSeqM _ _ Empty = pure Empty
zipWithSeqM f (x :<| xs) (y :<| ys) = do
    z <- f x y
    rest <- zipWithSeqM f xs ys
    pure (z :<| rest)

compose :: (Foldable f) => f (a -> a) -> a -> a
compose functions = coerce $ foldMap Endo functions

unzip3Seq :: Seq (a, b, c) -> (Seq a, Seq b, Seq c)
unzip3Seq Empty = (Empty, Empty, Empty)
unzip3Seq ((a, b, c) :<| rest) = do
    let (as, bs, cs) = unzip3Seq rest
    (a :<| as, b :<| bs, c :<| cs)

findSeq :: (a -> Bool) -> Seq a -> Maybe a
findSeq _predicate Empty = Nothing
findSeq predicate (x :<| rest)
    | predicate x = Just x
    | otherwise = findSeq predicate rest

mapAccumLM :: (Monad m, Traversable t) => (s -> a -> m (s, b)) -> s -> t a -> m (s, t b)
mapAccumLM f initial traversable =
    swap <$> flip runStateT initial do
        traverse
            ( \a -> do
                current <- get
                (next, b) <- lift $ f current a
                put next
                pure b
            )
            traversable

forAccumLM :: (Monad m, Traversable t) => s -> t a -> (s -> a -> m (s, b)) -> m (s, t b)
forAccumLM initial traversable f = mapAccumLM f initial traversable

constructorNames :: forall a. (ConstructorNamesG (Rep a)) => Seq Text
constructorNames = constructorNamesG @(Rep a)

viaList :: forall list1 list2. (IsList list1, IsList list2, Item list1 ~ Item list2) => list1 -> list2
viaList = fromList . toList

class ConstructorNamesG f where
    constructorNamesG :: Seq Text

instance {-# OVERLAPPING #-} (KnownSymbol name) => ConstructorNamesG (C1 (MetaCons name _fixity _strictness) _f) where
    constructorNamesG = [fromString (symbolVal (Proxy :: Proxy name))]

instance (ConstructorNamesG f, ConstructorNamesG g) => ConstructorNamesG (f :+: g) where
    constructorNamesG = constructorNamesG @f <> constructorNamesG @g

instance {-# OVERLAPPABLE #-} (ConstructorNamesG f) => ConstructorNamesG (M1 _i _c f) where
    constructorNamesG = constructorNamesG @f

newtype Untagged a = MkUntagged a

assert :: (HasCallStack, Applicative f) => Bool -> f ()
assert ~condition = GHC.Base.assert condition (pure ())

for2 :: forall f a b c d. (Monad f) => Seq a -> Seq b -> (a -> b -> f (c, d)) -> f (Seq c, Seq d)
for2 xs ys f = go [] [] xs ys
  where
    go leftAcc rightAcc Empty _ = pure (leftAcc, rightAcc)
    go leftAcc rightAcc _ Empty = pure (leftAcc, rightAcc)
    go leftAcc rightAcc (x :<| xs) (y :<| ys) = do
        (x', y') <- f x y
        go (leftAcc :|> x') (rightAcc :|> y') xs ys

partitionWithSeq :: forall a b c. Seq a -> (a -> Either b c) -> (Seq b, Seq c)
partitionWithSeq seq f = do
    let (list1, list2) = partitionWith f (toList seq)
    (viaList list1, viaList list2)

frequencies :: (Foldable f, Hashable a) => f a -> HashMap a Int
frequencies foldable = flip execState mempty do
    for_ foldable \x -> do
        let update = \case
                Nothing -> Just 1
                Just n -> Just (n + 1)
        modify' (HashMap.alter update x)

