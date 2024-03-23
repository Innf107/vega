module Vega.Util (
    Untagged (..),
    Fix (..),
    unfix,
    viaList,
    Uncons (..),
    pattern Nil,
    pattern (:::),
) where

import Vega.Prelude

import Data.Vector qualified as Vector
import GHC.IsList (IsList (Item))

newtype Untagged a = MkUntagged a

newtype Fix f = MkFix (f (Fix f))

unfix :: Fix f -> f (Fix f)
unfix (MkFix f) = f

viaList :: forall list1 list2 a. (Foldable list1, IsList list2, Item list2 ~ a) => list1 a -> list2
viaList = fromList . toList

class Uncons t a | t -> a where
    uncons :: t -> Maybe (a, t)

pattern Nil :: (Uncons t a) => t
pattern Nil <- (uncons -> Nothing)

pattern (:::) :: (Uncons t a) => a -> t -> t
pattern x ::: xs <- (uncons -> Just (x, xs))

{-# COMPLETE Nil, (:::) #-}

instance Uncons [a] a where
    uncons [] = Nothing
    uncons (x : xs) = Just (x, xs)

instance Uncons (Seq a) a where
    uncons Empty = Nothing
    uncons (x :<| xs) = Just (x, xs)

instance Uncons (Vector a) a where
    uncons = Vector.uncons
