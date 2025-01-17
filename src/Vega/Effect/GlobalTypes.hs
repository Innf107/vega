module Vega.Effect.GlobalTypes (
    GlobalTypes (..),
    getGlobalType,
    setGlobalType,
) where

import Vega.Syntax

import Effectful
import Effectful.Dispatch.Dynamic (send)

data GlobalTypes :: Effect where
    GetGlobalType :: GlobalName -> GlobalTypes m Type
    SetGlobalType :: GlobalName -> Type -> GlobalTypes m ()

type instance DispatchOf GlobalTypes = Dynamic

{- | Get the type of a global variable.
-}
getGlobalType :: (GlobalTypes :> es) => GlobalName -> Eff es Type
getGlobalType name = send (GetGlobalType name)

-- | Set the type of a global variable
setGlobalType :: (GlobalTypes :> es) => GlobalName -> Type -> Eff es ()
setGlobalType name type_ = send (SetGlobalType name type_)
