module Vega.Alignment (Alignment, fromExponent, align) where

import Data.Bits (complement, shiftL, (.&.))
import Relude
import Vega.Pretty (Pretty, number, pretty)

newtype Alignment = MkAlignment {exponent :: Int}
    deriving (Eq, Ord)

fromExponent :: Int -> Alignment
fromExponent exponent = MkAlignment{exponent}

align :: Alignment -> Int -> Int
align MkAlignment{exponent} value = do
    let alignment = 1 `shiftL` exponent
    let mask = alignment - 1
    if value .&. mask == 0
        then value
        else (value .&. complement mask) + alignment

instance Pretty Alignment where
    pretty MkAlignment{exponent} = number (1 `shiftL` exponent :: Int)
