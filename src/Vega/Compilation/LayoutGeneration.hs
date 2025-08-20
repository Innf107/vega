module Vega.Compilation.LayoutGeneration where

import Relude hiding (Type)
import Effectful

import Vega.Syntax(Type(..))
import Vega.Compilation.LIR.Syntax (Layout(..))
import Vega.Effect.GraphPersistence (GraphPersistence)
import Data.Traversable (for)

layoutForRep :: (IOE :> es, GraphPersistence :> es) => Type -> Eff es Layout
layoutForRep = \case
    ProductRep elements -> do
        elementLayouts <- for elements layoutForRep
        pure undefined
    _ -> undefined

