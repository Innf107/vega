module Vega.ShadowStackDependency.TH (addShadowStackDependency) where

import Relude (pure)

import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax qualified as TH

{- | Even though we compile the plugin using stack, stack does not
re-compile the project when its source file changes.

In order to force it to do so anyway, we use this hack:
We declare a template haskell dependency from an otherwise empty module (ShadowStackDependency).
This way, whenever the archive changes, stack will recompile only that
module, which doesn't actually do anything but still makes it
re-compile the new version of the plugin.

However, for this to work consistently, the module that uses 'addShadowStackDependency' needs to be defined
as part of the vega *executable* (app). If we do this in the library, stack still uses the old
version for some reason (this might be a bug).
-}
addShadowStackDependency :: TH.DecsQ
addShadowStackDependency = do
    TH.addDependentFile "llvm-shadow-stack/VegaShadowStackPlugin.cpp"
    pure []