module Vega.Util (seqAny2) where

import Relude
import Data.Sequence (Seq(Empty, (:<|)))

{-| Check if any two elements in two @Seq@s zipped together pairwise satisfy some predicate.
    
    If one of the Seqs is longer than the other, the remaining elements of that Seq are discarded.
    
    O(min(n,m)) if none of the elements satisfy the predicate or O(i) if the predicate first becomes true at index i -}
seqAny2 :: (a -> b -> Bool) -> Seq a -> Seq b -> Bool
seqAny2 _predicate Empty _ = False
seqAny2 _predicate _ Empty = False
seqAny2 predicate (x :<| xs) (y :<| ys) = predicate x y || seqAny2 predicate xs ys
