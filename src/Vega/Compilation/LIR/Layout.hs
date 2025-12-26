module Vega.Compilation.LIR.Layout (Layout (..), LayoutContents (..), Path, PathSegment (..), generateLayout) where

import Data.Vector.Unboxed (Vector)
import Relude
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Pretty (Pretty, pretty)

data Layout = MkLayoutUnchecked
    { size :: Int
    , alignment :: Int
    , contents :: LayoutContents
    }

data LayoutContents
    = SumLayout {constructors :: Seq LayoutContents}
    | ProductLayout {offsets :: Vector Int}

instance Pretty Layout where
    pretty _ = undefined

generateLayout :: Core.Representation -> Layout
generateLayout = undefined

data PathSegment
    = SumConstructor Int
    | ProductField Int
    deriving (Generic)

type Path = Seq PathSegment
