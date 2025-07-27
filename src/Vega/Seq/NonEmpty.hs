{-# LANGUAGE QuantifiedConstraints #-}

module Vega.Seq.NonEmpty (NonEmpty ((:<||), (:||>)), toSeq, castToSeq, unzip, first, last) where

import Relude hiding (NonEmpty, unzip, first, last)

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

unzip :: NonEmpty (a, b) -> (NonEmpty a, NonEmpty b)
unzip (MkNonEmpty seq) = coerce (Seq.unzip seq)

first :: NonEmpty a -> a
first (x :<|| _) = x

last :: NonEmpty a -> a
last (_ :||> x) = x
