module Vega.Compilation.Shape (Shape (..)) where

import Relude

data Shape = MkShape
    { sizeInBytes :: Int
    }
