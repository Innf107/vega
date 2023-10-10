module Vega.Debug (
    ShowHeadConstructor (..),
    HeadConstructorArg (..),
) where

import Vega.Prelude

import Vega.Pretty

import GHC.Generics
import GHC.TypeLits (KnownSymbol, symbolVal)

class ShowHeadConstructor a where
    showHeadConstructor :: a -> Doc Ann
    default showHeadConstructor :: (Generic a, ShowHeadConstructorGen (Rep a)) => a -> Doc Ann
    showHeadConstructor x = showHeadConstructorGen (from x)

class ShowHeadConstructorGen f where
    showHeadConstructorGen :: f x -> Doc Ann

instance ShowHeadConstructorGen V1 where
    showHeadConstructorGen = \case {}

instance (ShowHeadConstructorGen f, ShowHeadConstructorGen g) => ShowHeadConstructorGen (f :+: g) where
    showHeadConstructorGen (L1 left) = showHeadConstructorGen left
    showHeadConstructorGen (R1 right) = showHeadConstructorGen right

instance {-# OVERLAPPABLE #-} (ShowHeadConstructorGen f) => ShowHeadConstructorGen (M1 i t f) where
    showHeadConstructorGen (M1 x) = showHeadConstructorGen x

instance (KnownSymbol constructor, HeadConstructorArgs f) => ShowHeadConstructorGen (M1 i (MetaCons constructor _fixity _idkwhatthisdoes) f) where
    showHeadConstructorGen (M1 x) = lparen "(" <> sep (constructorText (toText (symbolVal (Proxy @constructor))) :<| headConstructorArgs x) <> rparen ")"

class HeadConstructorArgs f where
    headConstructorArgs :: f x -> Seq (Doc Ann)

instance HeadConstructorArgs V1 where
    headConstructorArgs = \case {}

instance (HeadConstructorArgs f) => HeadConstructorArgs (M1 i t f) where
    headConstructorArgs (M1 x) = headConstructorArgs x

instance (HeadConstructorArgs f, HeadConstructorArgs g) => HeadConstructorArgs (f :*: g) where
    headConstructorArgs (x :*: y) = headConstructorArgs x <> headConstructorArgs y

instance (HeadConstructorArg x) => HeadConstructorArgs (K1 _i x) where
    headConstructorArgs (K1 x) = [headConstructorArg x]

class HeadConstructorArg a where
    headConstructorArg :: a -> Doc Ann

instance {-# OVERLAPPABLE #-} HeadConstructorArg a where
    headConstructorArg _ = "_"
