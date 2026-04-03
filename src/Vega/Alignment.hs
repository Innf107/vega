module Vega.Alignment (Alignment, fromExponent, fromValue, align, toInt) where

import Data.Bits (complement, shiftL, (.&.))
import Data.Bits qualified as Bits
import Relude
import Vega.Panic (panic)
import Vega.Pretty (Pretty, number, pretty)
import Vega.Pretty qualified as Pretty

newtype Alignment = MkAlignment {alignment :: Int}
    deriving (Eq, Ord, Show)

fromExponent :: Int -> Alignment
fromExponent exponent = MkAlignment (1 `shiftL` exponent)

fromValue :: Int -> Alignment
fromValue value
    | Bits.popCount value == 1 = MkAlignment value
    | otherwise = panic $ "Trying to create alignment value with non-power of 2 value" Pretty.<+> number value

align :: Alignment -> Int -> Int
align MkAlignment{alignment} value = do
    let mask = alignment - 1
    if value .&. mask == 0
        then value
        else (value .&. complement mask) + alignment

instance Pretty Alignment where
    pretty alignment = number (toInt alignment)

toInt :: Alignment -> Int
toInt MkAlignment{alignment} = alignment
