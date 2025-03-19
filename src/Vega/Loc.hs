module Vega.Loc (Loc (..), HasLoc (..)) where

import Relude

import GHC.Generics (Generically (..), K1 (..), M1 (..), Rep (..), V1, (:*:) (..), (:+:) (..))

-- | Stub so we can exclude it from Diff
data Loc = MkLoc
    deriving (Show, Eq, Ord, Generic)

deriving via Generically Loc instance Semigroup Loc

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
