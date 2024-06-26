{-# LANGUAGE AllowAmbiguousTypes #-}

module Vega.Debug (
    todo,
    showHeadConstructor,
    HeadConstructorArg (..),
    defaultHeadConstructorArg,
    getRecordFields,
) where

import Vega.Prelude

import Vega.Pretty

import GHC.Generics
import GHC.TypeLits (KnownSymbol, symbolVal)

{-# WARNING todo "todo remains in code" #-}
todo :: a -> a
todo x = x

-- | Pretty-print the first constructor of a data type that implements 'Generic' for debugging purposes.
-- This will include every argument that implements 'HeadConstructorArg' and display everything else as @_@.
showHeadConstructor :: (Generic a, ShowHeadConstructorGen (Rep a)) => a -> Doc Ann
showHeadConstructor x = showHeadConstructorGen (from x)

class ShowHeadConstructorGen f where
    showHeadConstructorGen :: f x -> Doc Ann

instance ShowHeadConstructorGen V1 where
    showHeadConstructorGen :: forall k (x :: k). V1 x -> Doc Ann
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

instance HeadConstructorArgs U1 where
    headConstructorArgs U1 = []

instance (HeadConstructorArgs f) => HeadConstructorArgs (M1 i t f) where
    headConstructorArgs (M1 x) = headConstructorArgs x

instance (HeadConstructorArgs f, HeadConstructorArgs g) => HeadConstructorArgs (f :*: g) where
    headConstructorArgs (x :*: y) = headConstructorArgs x <> headConstructorArgs y

instance (HeadConstructorArg x) => HeadConstructorArgs (K1 _i x) where
    headConstructorArgs (K1 x) = [headConstructorArg x]

{- | This class can be used to override the way an argument
    to a constructor is displayed by 'showHeadConstructor'.

    Since this uses overlapping instances, there is a chance of incoherence so make
    sure you define these instances early enough. Since 'showHeadConstructor'
    is only used for debugging, this shouldn't cause any major issues though.
-}
class HeadConstructorArg a where
    headConstructorArg :: a -> Doc Ann

instance {-# OVERLAPPABLE #-} HeadConstructorArg a where
    headConstructorArg _ = defaultHeadConstructorArg

instance HeadConstructorArg a => HeadConstructorArg (Maybe a) where
    headConstructorArg Nothing = keyword "Nothing"
    headConstructorArg (Just x) = headConstructorArg x

defaultHeadConstructorArg :: Doc Ann
defaultHeadConstructorArg = "_"

{- | Get the names of all fields in a record type that implements 'Generic'.
    This only works on record types with a single constructor.
-}
getRecordFields :: forall a. (RecordFieldsG (Rep a)) => Seq Text
getRecordFields = getRecordFieldsG @(Rep a)

class RecordFieldsG f where
    getRecordFieldsG :: Seq Text

instance (RecordFieldsG f, RecordFieldsG g) => RecordFieldsG (f :*: g) where
    getRecordFieldsG = getRecordFieldsG @f <> getRecordFieldsG @g

instance {-# OVERLAPPABLE #-} (RecordFieldsG f) => RecordFieldsG (M1 _i _c f) where
    getRecordFieldsG = getRecordFieldsG @f

instance (KnownSymbol name) => RecordFieldsG (M1 _i (MetaSel (Just name) _unpackedness _sourcestrictness _decidedstrictness) _f) where
    getRecordFieldsG = [toText (symbolVal (Proxy @name))]
