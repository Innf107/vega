module Vega.Panic (panic, Panic (..), prettyCallStack) where

import Control.Exception (throw)
import Relude hiding (prettyCallStack)
import Relude qualified
import Vega.Pretty

data Panic = Panic CallStack (Doc Ann)
    deriving stock (Show)
    deriving anyclass (Exception)

panic :: (HasCallStack) => Doc Ann -> a
panic doc = throw (Panic callStack doc)

prettyCallStack :: CallStack -> Doc Ann
prettyCallStack callStack = align (note $ toText $ Relude.prettyCallStack callStack)
