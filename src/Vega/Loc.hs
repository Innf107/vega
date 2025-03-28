module Vega.Loc (Loc (..), HasLoc (..)) where

import Relude

import GHC.Generics (Generically (..), K1 (..), M1 (..), Rep (..), V1, (:*:) (..), (:+:) (..))

data Loc = MkLoc
    { startLine :: Int
    , startColumn :: Int
    , endLine :: Int
    , endColumn :: Int
    , file :: Text
    }
    deriving (Show, Eq, Ord, Generic)

instance Semigroup Loc where
    MkLoc{startLine, startColumn, file = file1}
        <> MkLoc{endLine, endColumn, file = file2}
            | file1 /= file2 = error ("(<>) @Loc: trying to merge locations from different files")
            | otherwise = MkLoc{file = file1, startLine, startColumn, endLine, endColumn}

class HasLoc a where
    getLoc :: a -> Loc
    default getLoc :: (Generic a, HasLocGeneric (Rep a)) => a -> Loc
    getLoc x = getLocG (from x)

instance HasLoc Loc where
    getLoc = id

instance HasLoc (Loc, a)

class HasLocGeneric f where
    getLocG :: f p -> Loc

instance HasLocGeneric V1 where
    getLocG x = case x of {}

instance (HasLocGeneric f, HasLocGeneric g) => HasLocGeneric (f :+: g) where
    getLocG (L1 left) = getLocG left
    getLocG (R1 right) = getLocG right

-- The location needs to be the first argument for this
instance (HasLocGeneric f) => HasLocGeneric (f :*: g) where
    getLocG (x :*: _) = getLocG x

instance (HasLoc c) => HasLocGeneric (K1 i c) where
    getLocG (K1 x) = getLoc x

instance (HasLocGeneric f) => HasLocGeneric (M1 i t f) where
    getLocG (M1 x) = getLocG x
