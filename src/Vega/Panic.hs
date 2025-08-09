module Vega.Panic (panic, Panic (..)) where

import Control.Exception (throw)
import Relude
import Vega.Pretty

newtype Panic = Panic (Doc Ann)
    deriving stock (Show)
    deriving anyclass (Exception)

panic :: (HasCallStack) => Doc Ann -> a
panic doc = throw (Panic doc)
