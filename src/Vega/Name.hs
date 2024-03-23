module Vega.Name (
    Name,
    internal,
    original,
    unique,
    freshNameIO,
    ident,
    constructor,
    skolem,
    PrettyIdent (..),
) where

import Vega.Prelude

import Data.Unique (newUnique)
import Vega.Debug
import Vega.Pretty

import GHC.Show qualified as S
import System.IO.Unsafe (unsafePerformIO)

data Name = MkName Text Unique

instance Eq Name where
    MkName _ u1 == MkName _ u2 = u1 == u2

instance Ord Name where
    compare (MkName _ u1) (MkName _ u2) = compare u1 u2

internalUnique :: Unique
internalUnique = unsafePerformIO newUnique
{-# NOINLINE internalUnique #-}

internal :: Text -> Name
internal original = MkName original internalUnique

original :: Name -> Text
original (MkName original _) = original

unique :: Name -> Unique
unique (MkName _ unique) = unique

freshNameIO :: Text -> IO Name
freshNameIO original = do
    unique <- newUnique
    pure (MkName original unique)

ident :: Name -> Doc Ann
ident name = withUnique (unique name) $ identTextWith (unique name) (original name)

newtype PrettyIdent = MkPrettyIdent Name
    deriving newtype (Eq, Ord)

instance Pretty PrettyIdent where
    pretty = coerce ident

constructor :: Name -> Doc Ann
constructor name = withUnique (unique name) $ constructorTextWith (unique name) (original name)

skolem :: Unique -> Name -> Doc Ann
skolem skolemUnique name = withUnique skolemUnique $ withUnique (unique name) $ skolemTextWith skolemUnique (original name)

instance S.Show Name where
    show = toString . original

instance HeadConstructorArg Name where
    headConstructorArg = ident
