module Vega.Compilation.LIR.Layout (Layout (..), LayoutContents (..), Path, PathSegment (..), generateLayout) where

import Data.Sequence qualified as Seq
import Data.Vector.Unboxed (Vector)
import GHC.Exts qualified
import Relude
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Panic (panic)
import Vega.Pretty (Pretty, pretty)
import Vega.Pretty qualified as Pretty
import Vega.Syntax qualified as Vega
import Vega.Util qualified as Util
import qualified Data.Vector.Unboxed as Vector
import Vega.Util (assert)
import qualified GHC.Base
import Vega.Alignment (Alignment)
import qualified Vega.Alignment as Alignment

data Layout = MkLayoutUnchecked
    { size :: Int
    , alignment :: Alignment
    , contents :: LayoutContents
    }

data LayoutContents
    = SumLayout {constructors :: Seq LayoutContents}
    | ProductLayout {offsets :: Vector Int}
    | NumberLayout
    | ManagedPointerLayout

-- TODO: factor this out to bits that can go in registers

instance Pretty Layout where
    pretty layout = Pretty.lparen "[" <> Pretty.number layout.size <> "@" <> pretty layout.alignment <> Pretty.rparen "]" <> pretty layout.contents

instance Pretty LayoutContents where
    pretty = \case
        SumLayout constructors -> Pretty.lparen "<" <> Pretty.intercalateDoc (Pretty.keyword " + ") (fmap pretty constructors) <> Pretty.rparen ">"
        ProductLayout offsets -> Pretty.lparen "(" <> Pretty.intercalateDoc (Pretty.keyword ", ") (fmap Pretty.number (GHC.Exts.toList offsets)) <> Pretty.rparen ")"
        NumberLayout -> Pretty.keyword "Int"
        ManagedPointerLayout -> Pretty.keyword "Pointer"

generateLayout :: Core.Representation -> Layout
generateLayout = \case
    Core.ProductRep elementRepresentations -> generateProductLayout elementRepresentations
    Core.SumRep constructorRepresentations -> do
        undefined
    Core.ArrayRep representation -> do
        undefined
    Core.PrimitiveRep primitiveRep -> case primitiveRep of
        Vega.IntRep -> MkLayoutUnchecked{size = 8, alignment = Alignment.fromExponent 3, contents = NumberLayout}
        Vega.BoxedRep -> MkLayoutUnchecked{size = 8, alignment = Alignment.fromExponent 3, contents = ManagedPointerLayout}
        _ -> undefined
    Core.ParameterRep index -> panic $ "Trying to generate a layout for unsubstituted parameter representation " <> pretty index

generateProductLayout :: Seq Core.Representation -> Layout
generateProductLayout elementRepresentations = do
    let elementLayoutsWithIndices = Seq.mapWithIndex (\index rep -> (index, generateLayout rep)) elementRepresentations
    let sortedLayouts = Seq.sortBy (compare `on` \(_, layout) -> Down layout.size) elementLayoutsWithIndices

    let ((size, alignment), offsetsPerIndex) = mapAccumL go (0, Alignment.fromExponent 0) (toList sortedLayouts)

    let offsets = (Vector.replicate (length elementRepresentations) -100) Vector.// (offsetsPerIndex)
    -- If we ever see -100 in an offset, that means something went horribly wrong here
    -- (it really shouldn't happen though since we just pass on the indices that mapWithIndex gave us)
    GHC.Base.assert (-100 `Vector.notElem` offsets) do
        MkLayoutUnchecked{size, alignment, contents = ProductLayout{offsets}}
  where
    go (currentOffset, currentMaxAlignment) (index, layout) = do
        let offset = Alignment.align layout.alignment currentOffset

        let nextMaxAlignment = max currentMaxAlignment layout.alignment
        let nextOffset = offset + layout.size
        ((nextOffset, nextMaxAlignment), (index, offset))

data PathSegment
    = SumConstructor Int
    | ProductField Int
    deriving (Generic)

type Path = Seq PathSegment
