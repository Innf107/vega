module Vega.Compilation.LLVM.Layout (
    -- * Layout Generation
    Layout,
    representationLayout,

    -- * Specific Layouts
    boxedLayout,
    intLayout,
    sizedIntLayoutInBytes,
    functionPointerLayout,
    closureLayout,

    -- * Layout Properties
    size,
    alignment,
    llvmParameterType,
    llvmType,
    identifier,

    -- ** Products
    productLayout,
    productOffsetAndLayout,

    -- ** Sums
    sumOffsetAndLayout,
    sumTagOffset,
    sumTagSizeInBytes,

    -- ** Low level details
    kind,
    LayoutKind (..),
) where

import Data.Bits qualified as Bits
import Data.Foldable1 (maximum)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Effectful (Eff)
import LLVM.Core qualified as LLVM
import Relude
import Text.Show (Show (..))
import Vega.Alignment (Alignment)
import Vega.Alignment qualified as Alignment
import Vega.Alignment qualified as Vega
import Vega.Compilation.Core.Syntax (Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Debug (showHeadConstructor)
import Vega.Panic (panic)
import Vega.Pretty (number, pretty)
import Vega.Syntax qualified as Vega
import qualified LLVM.Core.Context as LLVM
import System.IO.Unsafe (unsafePerformIO)

data Layout = MkLayout
    { size :: Int
    , alignment :: Vega.Alignment
    , kind :: LayoutKind
    , details :: LayoutDetails
    }
    deriving (Show)

data LayoutKind
    = LLVMScalar LLVM.Type
    | AggregatePointer
    | ZeroSized

instance Show LayoutKind where
    show AggregatePointer = "AggregatePointer"
    show (LLVMScalar _) = "LLVMScalar _"
    show ZeroSized = "ZeroSized"

data LayoutDetails
    = ProductLayout {offsetsAndElementLayouts :: Seq (Int, Layout)}
    | SumLayout {tagSizeInBytes :: Int, constructorLayouts :: Seq Layout}
    | Primitive
    deriving (Generic, Show)

size :: Layout -> Int
size layout = layout.size

alignment :: Layout -> Vega.Alignment
alignment layout = layout.alignment

llvmParameterType :: (?context :: LLVM.Context, HasCallStack) => Layout -> (LLVM.Type, Seq LLVM.Attribute)
llvmParameterType layout = case layout.kind of
    LLVMScalar type_ -> (type_, [])
    AggregatePointer -> unsafePerformIO do
        byvalAttributeKind <- LLVM.getEnumAttributeKindForName "byval"
        byvalAttribute <- LLVM.createTypeAttribute byvalAttributeKind (llvmType layout)
        pure (LLVM.pointerType, [byvalAttribute]) -- TODO: alignment?
    ZeroSized -> panic "Trying to access LLVM type of zero-sized layout"

llvmType :: (?context :: LLVM.Context, HasCallStack) => Layout -> LLVM.Type
llvmType layout = case layout.kind of
    LLVMScalar type_ -> type_
    AggregatePointer -> LLVM.arrayType LLVM.int8Type layout.size
    ZeroSized -> panic "Trying to access LLVM type of zero-sized layout"

kind :: Layout -> LayoutKind
kind layout = layout.kind

productOffsetAndLayout :: Int -> Layout -> (Int, Layout)
productOffsetAndLayout fieldIndex layout = case layout.details of
    ProductLayout{offsetsAndElementLayouts} -> case Seq.lookup fieldIndex offsetsAndElementLayouts of
        Nothing -> panic $ "trying to access out-of-bounds index " <> number fieldIndex <> " on product layout with " <> pretty (length offsetsAndElementLayouts) <> " fields."
        Just value -> value
    _ -> panic $ "trying to access productOffsetAndLayout on non-product layout " <> showHeadConstructor layout.details

{- | Return the layout of the given constructor, as well as the offset from which it starts.
Because the sum tag is currently the last element of the product, this is always zero,
but that might change in the future. See NOTE: [Sum tags] for details
-}
sumOffsetAndLayout :: Int -> Layout -> (Int, Layout)
sumOffsetAndLayout constructorIndex layout = case layout.details of
    SumLayout{constructorLayouts} -> case Seq.lookup constructorIndex constructorLayouts of
        Nothing -> panic $ "trying to access out-of-bounds constructor " <> number constructorIndex <> " on sum layout with " <> pretty (length constructorLayouts) <> " constructors."
        Just value -> (0, value)
    _ -> panic $ "trying to access sumOffsetAndLayout on non-sum layout " <> showHeadConstructor layout.details

-- | The offset at which the sum tag is stored. See NOTE: [Sum tags]
sumTagOffset :: Layout -> Int
sumTagOffset layout = layout.size - sumTagSizeInBytes layout

sumTagSizeInBytes :: Layout -> Int
sumTagSizeInBytes layout = case layout.details of
    SumLayout{tagSizeInBytes} -> tagSizeInBytes
    _ -> panic $ "trying to access sum tag size on non-sum layout " <> showHeadConstructor layout.details

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
    Core.FunctionPointerRep ->
        pure (MkLayout{size = 8, alignment = Alignment.fromValue 8, kind = LLVMScalar LLVM.pointerType, details = Primitive})
    rep@Core.ParameterRep{} -> panic $ "Non-monomorphized parameter representation in layout generation: " <> pretty rep

productLayout :: (?context :: LLVM.Context) => Seq Layout -> Layout
productLayout elementLayouts = do
    case elementLayouts of
        Empty -> MkLayout{size = 0, alignment = Alignment.fromValue 1, kind = ZeroSized, details = Primitive}
        _ -> do
            let go currentSize currentAlignment offsetsAndLayouts = \case
                    Empty -> (currentSize, currentAlignment, offsetsAndLayouts)
                    nextLayout :<| rest -> do
                        let offset = Alignment.align nextLayout.alignment currentSize

                        go (offset + nextLayout.size) (max currentAlignment nextLayout.alignment) (offsetsAndLayouts :|> (offset, nextLayout)) rest
            let (size, alignment, offsetsAndElementLayouts) = go 0 (Alignment.fromValue 1) [] elementLayouts

            MkLayout{size, alignment, kind = AggregatePointer, details = ProductLayout{offsetsAndElementLayouts}}

-- TODO: make sure the tag is *last* element
sumLayout :: (?context :: LLVM.Context) => Seq Layout -> Layout
sumLayout payloads = do
    case payloads of
        Empty -> (MkLayout{size = 0, alignment = Alignment.fromValue 1, kind = ZeroSized, details = Primitive})
        _ -> do
            let tagSizeInBits = smallestPowerOfTwoFitting (length payloads)
            -- TODO: it would be nice to pack the bits into niches when possible but for now it's easier to
            -- pad it to full byte boundaries (I'm not sure if it even makes sense to support variants with > 256 fields tbh)
            let tagSizeInBytes = Alignment.align (Alignment.fromValue 8) tagSizeInBits `div` 8
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
    Vega.BoxedRep -> pure boxedLayout
    Vega.IntRep -> pure intLayout
    Vega.DoubleRep -> pure $ MkLayout{size = 8, alignment = Alignment.fromValue 8, kind = LLVMScalar LLVM.doubleType, details = Primitive}

intLayout :: (?context :: LLVM.Context) => Layout
intLayout = sizedIntLayoutInBytes 8

sizedIntLayoutInBytes :: (?context :: LLVM.Context) => Int -> Layout
sizedIntLayoutInBytes size = MkLayout{size, alignment = Alignment.fromValue size, kind = LLVMScalar (LLVM.intType (size * 8)), details = Primitive}

-- TODO: we might be able to give heap pointers a different address space from unmanaged pointers?
boxedLayout :: (?context :: LLVM.Context) => Layout
boxedLayout = MkLayout{size = 8, alignment = Alignment.fromValue 8, kind = LLVMScalar LLVM.pointerType, details = Primitive}

-- TODO: This pointer should not count as boxed since it doesn't need to be followed by the GC
functionPointerLayout :: (?context :: LLVM.Context) => Layout
functionPointerLayout = MkLayout{size = 8, alignment = Alignment.fromValue 8, kind = LLVMScalar LLVM.pointerType, details = Primitive}

closureLayout :: (?context :: LLVM.Context) => Layout -> Layout
closureLayout payloadLayout = productLayout [functionPointerLayout, payloadLayout]

smallestPowerOfTwoFitting :: Int -> Int
smallestPowerOfTwoFitting n = Bits.finiteBitSize n - Bits.countLeadingZeros (n - 1)

-- | Return a 'Text' identifier that uniquely identifies this layout for the purposes of info-table generation
identifier :: Layout -> Text
identifier layout = do
    -- TODO: include information about pointers
    "layout[" <> Relude.show layout.size <> "," <> Relude.show (Alignment.toInt layout.alignment) <> "]"

{- NOTE [Sum tags]:
For now, the tag of a sum is always the last element in the layout.

In the common case where the tag fits in a single byte, this means it is exactly the last byte
(exactly one after the size of the largest constructor), although if it needs two bytes,
it may be offset by one to satisfy its natural alignment.

Doing this is beneficial for two reasons:
1) Sum payloads are kept contiguous, meaning we can load and store them in one go.
2) We don't need to introduce unnecessary padding into the payload and since the tag is almost always
only a single byte (and even if not, only two bytes), we don't add any (or at most one byte of) additional padding.

However, we may want to lift this restriction in the future since if the payload contains unused bytes, we might be
able to squeeze the tag into it without using any space for it. In order to support this, we will first need
support for both non-contiguous payloads and padding/niche tracking, neither of which we have just yet.
-}
