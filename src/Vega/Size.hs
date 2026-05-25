module Vega.Size (
    Size,
    fromBits,
    fromBytes,
    inBits,
    inBytes,
) where

import GHC.Show (show)
import Relude hiding (show)

newtype Size = MkSize {sizeInBits :: Int}
instance Show Size where
    show (MkSize{sizeInBits}) = "fromBits " <> show sizeInBits

fromBits :: Int -> Size
fromBits sizeInBits = MkSize{sizeInBits}

inBits :: Size -> Int
inBits size = size.sizeInBits

fromBytes :: Int -> Size
fromBytes sizeInBytes = MkSize{sizeInBits = 8 * sizeInBytes}

inBytes :: Size -> Int
inBytes size
    | size.sizeInBits `mod` 8 == 0 = size.sizeInBits `div` 8
    | otherwise = size.sizeInBits `div` 8 + 1