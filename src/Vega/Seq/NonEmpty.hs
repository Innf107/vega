{-# LANGUAGE QuantifiedConstraints #-}

module Vega.Seq.NonEmpty (
    NonEmpty ((:<||), (:||>)),
    pattern NonEmpty,
    toSeq,
    toNonEmptyList,
    castToSeq,
    unzip,
    first,
    last,
    mapWithIndex,
) where

import Relude hiding (NonEmpty, first, last, unzip)
import Relude qualified

import Data.Foldable1 (Foldable1)
import Data.Sequence qualified as Seq

newtype NonEmpty a = MkNonEmpty (Seq a)
    deriving newtype
        ( Functor
        , Applicative
        , Monad
        , Semigroup
        , Monoid
        , Foldable
        , Eq
        , Ord
        , Show
        , Hashable
        )

instance Traversable NonEmpty where
    traverse f (MkNonEmpty xs) = MkNonEmpty <$> traverse f xs

toNonEmptyList :: NonEmpty a -> Relude.NonEmpty a
toNonEmptyList (x :<|| xs) = (x :| toList xs)

toSeq :: NonEmpty a -> Seq a
toSeq = coerce

-- | Zero-cost conversion from NonEmpty to Seq within any type constructor (with a representable type role)
castToSeq :: (forall a b. (Coercible a b) => Coercible (f a) (f b)) => f (NonEmpty a) -> f (Seq a)
castToSeq = coerce

pattern (:<||) :: a -> Seq a -> NonEmpty a
pattern x :<|| xs = MkNonEmpty (x Seq.:<| xs)

pattern (:||>) :: Seq a -> a -> NonEmpty a
pattern xs :||> x = MkNonEmpty (xs Seq.:|> x)

{-# COMPLETE (:<||) #-}
{-# COMPLETE (:||>) #-}

pattern NonEmpty :: NonEmpty a -> Seq a
pattern NonEmpty nonEmpty <- (asNonEmpty -> Just nonEmpty)

{-# COMPLETE Seq.Empty, NonEmpty #-}

asNonEmpty :: Seq a -> Maybe (NonEmpty a)
asNonEmpty = \case
    Seq.Empty -> Nothing
    (x Seq.:|> xs) -> Just (x :||> xs)

unzip :: NonEmpty (a, b) -> (NonEmpty a, NonEmpty b)
unzip (MkNonEmpty seq) = coerce (Seq.unzip seq)

first :: NonEmpty a -> a
first (x :<|| _) = x

last :: NonEmpty a -> a
last (_ :||> x) = x

mapWithIndex :: (Int -> a -> b) -> NonEmpty a -> NonEmpty b
mapWithIndex f = coerce (Seq.mapWithIndex f)
