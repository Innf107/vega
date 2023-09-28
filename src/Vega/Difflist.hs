module Vega.Difflist (Difflist) where

import Vega.Prelude as Prelude

import GHC.Exts as Exts (IsList (..))

newtype Difflist a = MkDifflist ([a] -> [a])

instance IsList (Difflist a) where
    type Item (Difflist a) = a
    fromList list = MkDifflist (\rest -> list <> rest)
    toList (MkDifflist difflist) = difflist []

instance Semigroup (Difflist a) where
    (MkDifflist left) <> (MkDifflist right) = MkDifflist (left . right)

instance Monoid (Difflist a) where
    mempty = MkDifflist id

instance Foldable Difflist where
    foldr f initial difflist = foldr f initial (Exts.toList difflist)
    toList = Exts.toList