module Vega.Prelude (
  module Export,
  assert,
  assertM,
  compose,
  mapAccumLM,
  findM,
  findMapM,
  findMap,
  intercalate,
  intercalateMap,
  HSType,
  HSConstraint,
) where

import Control.Exception (assert)
import Control.Monad.Except as Export (throwError)
import Data.Kind qualified
import Data.Unique as Export (Unique, hashUnique)
import Relude as Export hiding (Type, intercalate, words, trace)
import Relude.Extra as Export

import Data.Sequence as Export (Seq (..))
import Data.Vector as Export (MVector, Vector)

import Control.Monad.ST as Export
import Data.STRef as Export

import Control.Monad.Zip as Export

assertM :: (Applicative f, HasCallStack) => Bool -> f ()
assertM cond = assert cond (pure ())

compose :: (Foldable f) => f (a -> a) -> a -> a
compose foldable = appEndo $ foldMap Endo foldable

mapAccumLM :: (Traversable t, Monad m) => (s -> a -> m (s, b)) -> s -> t a -> m (s, t b)
mapAccumLM f initial traversable = fmap swap $ runStateT (go traversable) initial
 where
  go traversable = flip traverse traversable \x -> do
    state <- get
    (state, result) <- lift (f state x)
    put state
    pure result

findM :: (Foldable f, Monad m) => (a -> m Bool) -> f a -> m (Maybe a)
findM predicateM foldable =
  findMapM
    ( \x ->
        predicateM x <&> \case
          True -> Just x
          False -> Nothing
    )
    foldable

findMapM :: (Foldable f, Monad m) => (a -> m (Maybe b)) -> f a -> m (Maybe b)
findMapM f foldable =
  foldr
    ( \x next ->
        f x >>= \case
          Just result -> pure (Just result)
          Nothing -> next
    )
    (pure Nothing)
    foldable

findMap :: (Foldable f) => (a -> Maybe b) -> f a -> Maybe b
findMap f foldable = coerce $ foldMap (First . f) foldable


intercalate :: (Foldable f, Monoid m) => m -> f m -> m
intercalate separator foldable =
  mconcat $ intersperse separator (toList foldable)

intercalateMap :: (Foldable f, Monoid m) => m -> (a -> m) -> f a -> m
intercalateMap separator f foldable =
  intercalate separator (map f (toList foldable))

type HSType = Data.Kind.Type
type HSConstraint = Data.Kind.Constraint
