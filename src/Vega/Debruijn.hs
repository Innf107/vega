module Vega.Debruijn (
    Index,
    lookup,
    Limit,
    all,
    initial,
    new,
    size,
) where

import Data.Sequence qualified as Seq
import Relude hiding (all)
import Vega.Pretty (Pretty)
import Vega.Pretty qualified as Pretty

newtype Index = MkIndex Int
    deriving stock (Show, Eq, Ord)
    deriving newtype (Hashable)

instance Pretty Index where
    pretty (MkIndex i) = Pretty.localIdentText ("$" <> show i)

newtype Limit = MkLimit {nextIndex :: Int}

all :: Limit -> Seq Index
all (MkLimit{nextIndex}) = coerce @(Seq _) [0 .. nextIndex - 1]

initial :: Limit
initial = MkLimit 0

new :: Limit -> (Limit, Index)
new limit = (limit{nextIndex = limit.nextIndex + 1}, MkIndex limit.nextIndex)

size :: Limit -> Int
size limit = limit.nextIndex

lookup :: Index -> Seq a -> Maybe a
lookup (MkIndex i) seq = seq Seq.!? i
