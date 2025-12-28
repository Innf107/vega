module Vega.Debruijn (Index, Limit, initial, new, size) where

import Relude
import Vega.Pretty (Pretty)
import Vega.Pretty qualified as Pretty

newtype Index = MkIndex Int
    deriving stock (Show, Eq, Ord)
    deriving newtype (Hashable)

instance Pretty Index where
    pretty (MkIndex i) = Pretty.localIdentText ("$" <> show i)

newtype Limit = MkLimit {nextIndex :: Int}

initial :: Limit
initial = MkLimit 0

new :: Limit -> (Limit, Index)
new limit = (limit{nextIndex = limit.nextIndex + 1}, MkIndex limit.nextIndex)

size :: Limit -> Int
size limit = limit.nextIndex
