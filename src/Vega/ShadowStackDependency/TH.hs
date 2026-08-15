module Vega.ShadowStackDependency.TH (addShadowStackDependency) where

import Relude (pure)

import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax qualified as TH

{- | Even though we statically link with our plugin, stack does not
re-link the project when the plugin archive changes.

In order to force it to do so anyway, we use this hack:
We declare a template haskell dependency from an otherwise empty module (ShadowStackDependency).
This way, whenever the archive changes, stack will recompile only that
module, which doesn't actually do anything but still makes it
re-link with the new version of the plugin.

However, for this to work consistently, the module that uses 'addShadowStackDependency' needs to be defined
as part of the vega *executable* (app). If we do this in the library, stack still uses the old
archive for some reason (this might be a bug).
-}
addShadowStackDependency :: TH.DecsQ
addShadowStackDependency = do
    TH.addDependentFile "llvm-shadow-stack/libVegaShadowStackPlugin.a"
    pure []
