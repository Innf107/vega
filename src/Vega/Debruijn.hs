module Vega.Debruijn (Index, toInt, Limit, initial, new, size) where

import Relude

newtype Index = MkIndex Int
    deriving stock (Show, Eq, Ord)
    deriving newtype (Hashable)

toInt :: Index -> Int
toInt (MkIndex index) = index

newtype Limit = MkLimit {nextIndex :: Int}

initial :: Limit
initial = MkLimit 0

new :: Limit -> (Limit, Index)
new limit = (limit{nextIndex = limit.nextIndex + 1}, MkIndex limit.nextIndex)

size :: Limit -> Int
size limit = limit.nextIndex
