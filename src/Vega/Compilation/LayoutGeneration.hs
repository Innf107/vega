module Vega.Compilation.LayoutGeneration where

import Effectful
import Relude hiding (NonEmpty, Type)

import Data.Bits (FiniteBits (countLeadingZeros), finiteBitSize)
import Data.Sequence (Seq (..))
import Vega.Compilation.LIR.Syntax (Layout (..))
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Seq.NonEmpty (pattern NonEmpty)
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Syntax (PrimitiveRep (..), Type (..))
import Vega.Util (These (..), forIndexed, zipWithLongest)



