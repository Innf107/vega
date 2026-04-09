{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Vega.Compilation.LLVM.Runtime.ToLLVMConstant (ToLLVMConstant (..), CStruct (..), CUnion (..), CEnum (..)) where

import Data.Sequence (Seq (..))
import GHC.Generics (Generic (..), K1 (..), M1 (..), Rep, U1, (:*:) (..), (:+:) (..))
import LLVM.Core qualified as LLVM
import Relude
import Vega.Alignment (Alignment)
import Vega.Alignment qualified as Alignment
import Vega.Util (viaList)

class ToLLVMConstant a where
    size :: Int
    alignment :: Alignment
    toLLVMConstant :: (?context :: LLVM.Context, MonadIO io) => a -> io (LLVM.Type, LLVM.Value)

instance ToLLVMConstant Word64 where
    size = 8
    alignment = Alignment.fromValue 8
    toLLVMConstant x = pure $ (LLVM.int64Type, LLVM.constInt LLVM.int64Type x False)

-- TODO: LLVM.constNull should be pure in llvm-ng
paddingConstant :: (MonadIO io, ?context :: LLVM.Context) => Int -> io LLVM.Value
paddingConstant size = LLVM.constNull (LLVM.arrayType LLVM.int8Type size)

paddingType :: (?context :: LLVM.Context) => Int -> LLVM.Type
paddingType size = LLVM.arrayType LLVM.int8Type size

addPadding :: (?context :: LLVM.Context, MonadIO io) => Seq (Int, Alignment, LLVM.Value, LLVM.Type) -> io (Seq LLVM.Value, Seq LLVM.Type)
addPadding fields = go 0 [] [] fields
  where
    go position values types = \case
        Empty -> pure (values, types)
        (size, alignment, value, type_) :<| rest -> do
            let startingPosition = Alignment.align alignment position
            let padding = startingPosition - position

            let nextPos = startingPosition + size

            case padding of
                0 -> go nextPos (values :|> value) (types :|> type_) rest
                _ -> do
                    paddingValue <- paddingConstant padding
                    go
                        nextPos
                        (values :|> paddingValue :|> value)
                        (types :|> paddingType padding :|> type_)
                        rest

newtype CStruct a = MkCStruct a

class ToLLVMCStruct f where
    cstructSize :: Int
    cstructAlignment :: Alignment
    toLLVMCStructFields :: (?context :: LLVM.Context, MonadIO io) => f x -> io (Seq (Int, Alignment, LLVM.Value, LLVM.Type))

instance (ToLLVMCStruct (Rep a), Generic a) => ToLLVMConstant (CStruct a) where
    size = cstructSize @(Rep a)
    alignment = cstructAlignment @(Rep a)
    toLLVMConstant (MkCStruct x) = do
        fields <- toLLVMCStructFields (from x)

        (fieldsWithPadding, fieldTypesWithPadding) <- addPadding fields

        constant <- LLVM.constStructInContext (viaList fieldsWithPadding) False
        let type_ = LLVM.structType (viaList fieldTypesWithPadding) False
        pure (type_, constant)

instance (ToLLVMConstant a) => ToLLVMCStruct (K1 _r a) where
    cstructSize = size @a
    cstructAlignment = alignment @a

    toLLVMCStructFields (K1 x) = do
        (type_, value) <- toLLVMConstant x
        pure [(size @a, alignment @a, value, type_)]

instance (ToLLVMCStruct f, ToLLVMCStruct g) => ToLLVMCStruct (f :*: g) where
    cstructSize = Alignment.align (cstructAlignment @g) (cstructSize @f) + cstructSize @g
    cstructAlignment = max (cstructAlignment @f) (cstructAlignment @g)
    toLLVMCStructFields (x :*: y) = do
        leftValues <- toLLVMCStructFields x
        rightValues <- toLLVMCStructFields y
        pure (leftValues <> rightValues)

instance (ToLLVMCStruct f) => ToLLVMCStruct (M1 _a _b f) where
    cstructSize = cstructSize @f
    cstructAlignment = cstructAlignment @f
    toLLVMCStructFields (M1 x) = toLLVMCStructFields x

newtype CUnion a = MkCUnion a

class ToLLVMCUnion f where
    cunionSize :: Int
    cunionAlignment :: Alignment
    toLLVMCUnion :: (?context :: LLVM.Context, MonadIO io) => Int -> f x -> io (LLVM.Type, LLVM.Value)

instance (ToLLVMCUnion (Rep a), Generic a) => ToLLVMConstant (CUnion a) where
    size = cunionSize @(Rep a)
    alignment = cunionAlignment @(Rep a)
    toLLVMConstant (MkCUnion x) = do
        toLLVMCUnion (size @(CUnion a)) (from x)

instance (ToLLVMConstant a) => ToLLVMCUnion (K1 _r a) where
    cunionSize = size @a
    cunionAlignment = alignment @a

    toLLVMCUnion expectedSize (K1 x) = do
        (type_, value) <- toLLVMConstant x

        let paddingSize = expectedSize - size @a
        case paddingSize of
            0 -> pure (type_, value)
            _ -> do
                padding <- paddingConstant paddingSize
                let paddingArray = paddingType paddingSize
                constant <- LLVM.constStructInContext [value, padding] False
                type_ <- pure $ LLVM.structType [type_, paddingArray] False
                pure (type_, constant)

instance (ToLLVMCUnion f, ToLLVMCUnion g) => ToLLVMCUnion (f :+: g) where
    cunionSize = max (cunionSize @f) (cunionSize @g)
    cunionAlignment = max (cunionAlignment @f) (cunionAlignment @g)
    toLLVMCUnion expectedSize = \case
        L1 x -> toLLVMCUnion expectedSize x
        R1 x -> toLLVMCUnion expectedSize x

instance (ToLLVMCUnion f) => ToLLVMCUnion (M1 _a _b f) where
    cunionSize = cunionSize @f
    cunionAlignment = cunionAlignment @f
    toLLVMCUnion size (M1 x) = toLLVMCUnion size x

newtype CEnum a = MkCEnum a

class IsCEnum f where
    constructorCount :: Word32
    toCWord :: f x -> Word32

instance (Generic a, IsCEnum (Rep a)) => ToLLVMConstant (CEnum a) where
    size = 4
    alignment = Alignment.fromValue 4
    toLLVMConstant (MkCEnum x) = pure $ (LLVM.int32Type, LLVM.constInt LLVM.int32Type (fromIntegral (toCWord (from x))) False)

instance IsCEnum U1 where
    constructorCount = 1
    toCWord _ = 0

instance (IsCEnum f, IsCEnum g) => IsCEnum (f :+: g) where
    constructorCount = constructorCount @f + constructorCount @g
    toCWord (L1 x) = toCWord x
    toCWord (R1 y) = constructorCount @f + toCWord y

instance (IsCEnum f) => IsCEnum (M1 _i _c f) where
    constructorCount = constructorCount @f
    toCWord (M1 x) = toCWord x
