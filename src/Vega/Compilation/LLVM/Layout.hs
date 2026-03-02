module Vega.Compilation.LLVM.Layout (
    Layout,
    representationLayout,
    size,
    kind,
    LayoutKind (..),
    alignment,
    llvmParameterType,
    llvmType,
    productOffsetAndLayout,
    sumOffsetAndLayout,
) where

import Data.Bits qualified as Bits
import Data.Foldable1 (maximum)
import Data.Sequence (Seq (..))
import Data.Traversable (for)
import Effectful (Eff)
import LLVM.Core qualified as LLVM
import Relude (
    Applicative (pure),
    Bool (False),
    Constraint,
    Foldable (length, toList),
    Int,
    Integral (div),
    NonEmpty ((:|)),
    Num ((+), (-)),
    Ord (max),
    Semigroup ((<>)),
    Seq,
    map,
    undefined,
    ($),
 )
import Vega.Alignment (Alignment)
import Vega.Alignment qualified as Alignment
import Vega.Alignment qualified as Vega
import Vega.Compilation.Core.Syntax (Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Syntax qualified as Vega

data Layout = MkLayout
    { size :: Int
    , alignment :: Vega.Alignment
    , kind :: LayoutKind
    , details :: LayoutDetails
    }

data LayoutKind
    = LLVMScalar LLVM.Type
    | AggregatePointer

data LayoutDetails
    = ProductLayout {offsetsAndElementLayouts :: Seq (Int, Layout)}
    | SumLayout {tagSizeInBytes :: Int, constructorLayouts :: Seq Layout}
    | Primitive

size :: Layout -> Int
size layout = layout.size

alignment :: Layout -> Vega.Alignment
alignment layout = layout.alignment

llvmParameterType :: (?context :: LLVM.Context) => Layout -> LLVM.Type
llvmParameterType layout = case layout.kind of
    LLVMScalar type_ -> type_
    AggregatePointer -> LLVM.pointerType -- TODO: byval?? alignment??


llvmType :: (?context :: LLVM.Context) => Layout -> LLVM.Type
llvmType layout = case layout.kind of
    LLVMScalar type_ -> type_
    AggregatePointer -> LLVM.arrayType LLVM.int8Type layout.size

kind :: Layout -> LayoutKind
kind layout = layout.kind

productOffsetAndLayout :: Int -> Layout -> (Int, Layout)
productOffsetAndLayout fieldIndex layout = undefined

sumOffsetAndLayout :: Int -> Layout -> (Int, Layout)
sumOffsetAndLayout constructorIndex layout = undefined

type LayoutGen es = (?context :: LLVM.Context) :: Constraint

representationLayout :: (LayoutGen es) => Representation -> Eff es Layout
representationLayout = \case
    Core.PrimitiveRep primitive -> primitiveLayout primitive
    Core.ProductRep elements -> do
        elementLayouts <- for elements representationLayout
        pure (productLayout elementLayouts)
    Core.SumRep constructors -> do
        constructorLayouts <- for constructors representationLayout
        pure (sumLayout constructorLayouts)
    Core.ArrayRep elements -> do
        undefined
    rep@Core.ParameterRep{} -> panic $ "Non-monomorphized parameter representation in layout generation: " <> pretty rep

productLayout :: (?context :: LLVM.Context) => Seq Layout -> Layout
productLayout elementLayouts = do
    let go currentSize currentAlignment offsetsAndLayouts = \case
            Empty -> (currentSize, currentAlignment, offsetsAndLayouts)
            nextLayout :<| rest -> do
                let offset = Alignment.align nextLayout.alignment currentSize

                go (offset + nextLayout.size) (max currentAlignment nextLayout.alignment) (offsetsAndLayouts :|> (offset, nextLayout)) rest
    let (size, alignment, offsetsAndElementLayouts) = go 0 (Alignment.fromExponent 1) [] elementLayouts

    MkLayout{size, alignment, kind = AggregatePointer, details = ProductLayout{offsetsAndElementLayouts}}

sumLayout :: (?context :: LLVM.Context) => Seq Layout -> Layout
sumLayout payloads = do
    let tagSizeInBits = smallestPowerOfTwoFitting (length payloads)
    -- TODO: it would be nice to pack the bits into niches when possible but for now it's easier to
    -- pad it to full byte boundaries (I'm not sure if it even makes sense to support variants with > 256 fields tbh)
    let tagSizeInBytes = Alignment.align (Alignment.fromExponent 3) tagSizeInBits `div` 8
    let tagAlignment = Alignment.fromValue tagSizeInBytes

    let sumAlignment = maximum (tagAlignment :| (map alignment (toList payloads)))

    let size = maximum (tagSizeInBytes :| [Alignment.align payload.alignment tagSizeInBytes + payload.size | payload <- toList payloads])

    MkLayout
        { size
        , alignment = sumAlignment
        , kind = AggregatePointer
        , details =
            SumLayout
                { tagSizeInBytes
                , constructorLayouts = payloads
                }
        }

primitiveLayout :: (?context :: LLVM.Context) => Vega.PrimitiveRep -> Eff es Layout
primitiveLayout = \case
    Vega.UnitRep -> pure (MkLayout{size = 0, alignment = Alignment.fromExponent 1, kind = AggregatePointer, details = Primitive})
    Vega.EmptyRep -> pure (MkLayout{size = 0, alignment = Alignment.fromExponent 1, kind = LLVMScalar LLVM.voidType, details = Primitive})
    -- TODO: we might be able to give heap pointers a different address space from unmanaged pointers?
    Vega.BoxedRep -> pure $ (MkLayout{size = 0, alignment = Alignment.fromExponent 3, kind = LLVMScalar LLVM.pointerType, details = Primitive})
    Vega.IntRep -> pure $ MkLayout{size = 8, alignment = Alignment.fromExponent 3, kind = LLVMScalar LLVM.int64Type, details = Primitive}
    Vega.DoubleRep -> pure $ MkLayout{size = 8, alignment = Alignment.fromExponent 3, kind = LLVMScalar LLVM.doubleType, details = Primitive}

smallestPowerOfTwoFitting :: Int -> Int
smallestPowerOfTwoFitting n = Bits.finiteBitSize n - Bits.countLeadingZeros (n - 1)
