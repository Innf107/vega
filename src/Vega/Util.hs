module Vega.Util (
    seqAny2,
    zipWithSeqM,
    compose,
    unzip3Seq,
) where

import Data.Sequence (Seq (..))
import Relude

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
