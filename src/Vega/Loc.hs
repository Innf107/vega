module Vega.Loc (
    Loc (..),
    HasLoc (..),
    merge,
    prettyErrorLoc,
) where

import Vega.Prelude

import Vega.Pretty

import Vega.Util (Untagged (..))

import GHC.Generics

data Loc = Loc
    { fileName :: Text
    , startLine :: {-# UNPACK #-} Int
    , startColumn :: {-# UNPACK #-} Int
    , endLine :: {-# UNPACK #-} Int
    , endColumn :: {-# UNPACK #-} Int
    }
    deriving (Show)

class HasLoc a where
    getLoc :: a -> Loc
    default getLoc :: (Generic a, HasLocGeneric (Rep a)) => a -> Loc
    getLoc x = getLocG (from x)

instance HasLoc Loc where
    getLoc = id

instance HasLoc (Loc, a)

merge :: (HasLoc loc1, HasLoc loc2) => loc1 -> loc2 -> Loc
merge hasLoc1 hasLoc2 = do
    let loc1 = getLoc hasLoc1
    let loc2 = getLoc hasLoc2
    assert (loc1.fileName == loc2.fileName)
        $ assert (loc1.startLine <= loc2.startLine || loc1.startLine == loc2.startLine && loc1.startColumn <= loc2.startColumn)
        $ Loc
            { fileName = loc1.fileName
            , startLine = loc1.startLine
            , startColumn = loc1.startColumn
            , endLine = loc2.endLine
            , endColumn = loc2.endColumn
            }

prettyErrorLoc :: Loc -> Doc Ann -> Doc Ann
prettyErrorLoc loc doc =
    pretty loc <> emphasis ":" <+> errorDoc "ERROR:" <> "\n" <> doc

instance Pretty Loc where
    pretty (Loc{fileName, startLine, startColumn}) =
        -- TODO: Add flag to display end line/column as well
        emphasis (fileName <> ":" <> show startLine <> ":" <> show startColumn)

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




instance (Generic a, HasLocGenUntagged (Rep a)) => HasLoc (Untagged a) where
    getLoc (MkUntagged x) = getLocGenUntagged (from x)

class HasLocGenUntagged f where
    getLocGenUntagged :: f x -> Loc

instance HasLocGenUntagged V1 where
    getLocGenUntagged = \case {}

instance (HasLocGenUntagged f, HasLocGenUntagged g) => HasLocGenUntagged (f :+: g) where
    getLocGenUntagged = \case
        L1 x -> getLocGenUntagged x
        R1 y -> getLocGenUntagged y

instance (HasLoc c) => HasLocGenUntagged (K1 i c) where
    getLocGenUntagged (K1 x) = getLoc x

instance (HasLocGenUntagged f) => HasLocGenUntagged (M1 i t f) where
    getLocGenUntagged (M1 x) = getLocGenUntagged x
