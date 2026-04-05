{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Vega.Compilation.LLVM.Runtime.Serialize (
    serialize,
    Serialize (..),
    CStruct (..),
    CUnion (..),
    CEnum (..),
) where

import Relude

import Data.ByteString qualified as ByteString
import Data.ByteString.Builder (Builder)
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Unsafe qualified as ByteString.Unsafe
import Foreign (Ptr, Storable (pokeByteOff), malloc, mallocBytes, mallocForeignPtrBytes, withForeignPtr)
import Foreign.C (CSize)
import GHC.Generics (Generic (from), K1 (..), M1 (..), Rep, U1, V1, to, (:*:) (..), (:+:) (..))
import System.IO.Unsafe (unsafePerformIO)
import Vega.Alignment (Alignment)
import Vega.Alignment qualified as Alignment

serialize :: forall a. (Serialize a) => a -> ByteString
serialize x = unsafePerformIO do
    pointer <- mallocBytes (size @a)

    serializeUnsafe 0 x pointer

    ByteString.Unsafe.unsafePackMallocCStringLen (coerce pointer, size @a)

{- | Class for serializing runtime values that are known at compile time.
In particular this includes runtime objects like info tables.

This is similar to 'Storable' but does not support reading and can differ in some details.
in particular, it explicitly does not support platform-dependent types like 'CSize' since those might
differ between the platform of the compiler and the target.
-}
class Serialize a where
    {- | Serialize the value at the given index in the byte array.
    This assumes that the array has enough elements and that the
    index is properly aligned according to 'alignment'.
    Neither property is checked.
    -}
    serializeUnsafe :: Int -> a -> Ptr Word8 -> IO ()

    size :: Int
    alignment :: Alignment

instance Serialize Word64 where
    size = 8
    alignment = Alignment.fromValue 8

    serializeUnsafe pos word64 pointer = do
        pokeByteOff pointer pos word64

-- | Newtype for deriving 'Serialize' instances that follow the equivalent C struct layout if applicable
newtype CStruct a = MkCStruct a

-- | Newtype for deriving 'Serialize' instances of sums that are serialized to C unions
newtype CUnion a = MkCUnion a

-- | Newtype for deriving 'Serialize' instances of constructor-less enums that are serialized to C enums starting from 0
newtype CEnum a = MkCEnum a

instance (Generic a, SerializeCStruct (Rep a)) => Serialize (CStruct a) where
    size = sizeCStruct @(Rep a)
    alignment = alignmentCStruct @(Rep a)
    serializeUnsafe position (MkCStruct x) array = serializeUnsafeCStruct position (from x) array

class SerializeCStruct f where
    sizeCStruct :: Int
    alignmentCStruct :: Alignment
    serializeUnsafeCStruct :: Int -> f x -> Ptr Word8 -> IO ()

instance (Serialize a) => SerializeCStruct (K1 r a) where
    sizeCStruct = size @a
    alignmentCStruct = alignment @a
    serializeUnsafeCStruct pos (K1 x) pointer = serializeUnsafe pos x pointer

instance (SerializeCStruct f, SerializeCStruct g) => SerializeCStruct (f :*: g) where
    sizeCStruct = Alignment.align (alignmentCStruct @g) (sizeCStruct @f) + sizeCStruct @g
    alignmentCStruct = max (alignmentCStruct @f) (alignmentCStruct @g)
    serializeUnsafeCStruct pos (x :*: y) = do
        serializeUnsafeCStruct pos x
        let posForY = Alignment.align (alignmentCStruct @g) (pos + sizeCStruct @f)
        serializeUnsafeCStruct posForY y

instance (SerializeCStruct f) => SerializeCStruct (M1 _i _c f) where
    sizeCStruct = sizeCStruct @f
    alignmentCStruct = alignmentCStruct @f
    serializeUnsafeCStruct pos (M1 x) pointer = serializeUnsafeCStruct pos x pointer

instance (Generic a, SerializeCUnion (Rep a)) => Serialize (CUnion a) where
    size = sizeCUnion @(Rep a)
    alignment = alignmentCUnion @(Rep a)
    serializeUnsafe position (MkCUnion x) array = serializeUnsafeCUnion position (from x) array

class SerializeCUnion f where
    sizeCUnion :: Int
    alignmentCUnion :: Alignment
    serializeUnsafeCUnion :: Int -> f x -> Ptr Word8 -> IO ()

instance (Serialize a) => SerializeCUnion (K1 r a) where
    sizeCUnion = size @a
    alignmentCUnion = alignment @a
    serializeUnsafeCUnion pos (K1 x) pointer = serializeUnsafe pos x pointer

instance (SerializeCUnion f) => SerializeCUnion (M1 _i _c f) where
    sizeCUnion = sizeCUnion @f
    alignmentCUnion = alignmentCUnion @f
    serializeUnsafeCUnion pos (M1 x) pointer = serializeUnsafeCUnion pos x pointer

instance (SerializeCUnion f, SerializeCUnion g) => SerializeCUnion (f :+: g) where
    sizeCUnion = max (sizeCUnion @f) (sizeCUnion @g)
    alignmentCUnion = max (alignmentCUnion @f) (alignmentCUnion @g)
    serializeUnsafeCUnion pos (L1 x) pointer = serializeUnsafeCUnion pos x pointer
    serializeUnsafeCUnion pos (R1 x) pointer = serializeUnsafeCUnion pos x pointer

instance (SerializeCEnum (Rep a), Generic a) => Serialize (CEnum a) where
    size = 4
    alignment = Alignment.fromValue 4
    serializeUnsafe pos (MkCEnum x) pointer = pokeByteOff pointer pos (toCWord (from x))

class SerializeCEnum f where
    constructorCount :: Word32
    toCWord :: f x -> Word32

instance SerializeCEnum U1 where
    constructorCount = 1
    toCWord _ = 0

instance (SerializeCEnum f, SerializeCEnum g) => SerializeCEnum (f :+: g) where
    constructorCount = constructorCount @f + constructorCount @g
    toCWord (L1 x) = toCWord x
    toCWord (R1 y) = constructorCount @f + toCWord y

instance (SerializeCEnum f) => SerializeCEnum (M1 _i _c f) where
    constructorCount = constructorCount @f
    toCWord (M1 x) = toCWord x
