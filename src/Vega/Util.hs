module Vega.Util (
    Untagged (..),
    Fix (..),
    unfix,
    viaList,
) where

import Vega.Prelude

import GHC.IsList (IsList (Item))

newtype Untagged a = MkUntagged a

newtype Fix f = MkFix (f (Fix f))

unfix :: Fix f -> f (Fix f)
unfix (MkFix f) = f

viaList :: (Foldable list1, IsList list2, Item list2 ~ a) => list1 a -> list2
viaList = fromList . toList
