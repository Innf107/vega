module Vega.Monad.Unique (MonadUnique (..)) where

import Vega.Prelude

import Vega.Name

import Data.Unique qualified as Unique

{- | MonadUnique represents the ability to generate *globally* unique values
    as given by 'Data.Unique' and to generate fresh 'Name's based on this value.

    Since the only way to generate 'Unique's is through IO, this is effectively
    a constrained version of MonadIO
-}
class (Monad m) => MonadUnique m where
    -- |  Generate a fresh, globally unique 'Name' from a text. This should satisfy @fmap original (freshName x) = pure x@
    freshName :: Text -> m Name

    -- | Generate a fresh globally unique 'Unique' just like 'Data.Unique.newUnique'
    newUnique :: m Unique

instance MonadUnique IO where
    freshName = freshNameIO
    newUnique = Unique.newUnique
