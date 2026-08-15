module Vega.ShadowStackDependency.TH (addShadowStackDependency) where

import Relude (pure)

import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax qualified as TH

{- | Even though we statically link with our plugin, stack does not
re-link the project when the plugin archive changes.

In order to force it to do so anyway, we use this hack:
We declare a template haskell dependency from an otherwise empty module
(Vega.ShadowStackDependency).
This way, whenever the archive changes, stack will recompile only that
module, which doesn't actually do anything but still makes it
re-link with the new version of the plugin.
-}
addShadowStackDependency :: TH.DecsQ
addShadowStackDependency = do
    TH.addDependentFile "llvm-shadow-stack/libVegaShadowStackPlugin.a"
    pure []
