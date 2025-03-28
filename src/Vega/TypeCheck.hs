module Vega.TypeCheck where

import Vega.Syntax
import Vega.Effect.GlobalTypes 
import Vega.Effect.Dependency

import Relude hiding (Type)
import Effectful

type TypeCheck es = (GlobalTypes :> es)


checkDeclaration :: (GlobalTypes :> es) => Declaration Renamed -> Eff es (Declaration Typed)
checkDeclaration = undefined

