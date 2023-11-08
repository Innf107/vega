module Vega.Monad.Unique (MonadUnique (..)) where

import Vega.Prelude

import Vega.Name

import Data.Unique qualified as Unique

class Monad m => MonadUnique m where
    freshName :: Text -> m Name
    newUnique :: m Unique

instance MonadUnique IO where
    freshName = freshNameIO
    newUnique = Unique.newUnique
