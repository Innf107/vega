{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Vega.Effect.Unique.Static.Local (NewUnique, Unique, newUnique, runNewUnique) where

import Data.Unique (Unique)
import Data.Unique qualified as Unique
import Effectful (Dispatch (Static), DispatchOf, Eff, Effect, IOE, (:>))
import Effectful.Dispatch.Static (
    StaticRep,
    evalStaticRep,
    unsafeEff_,
    pattern WithSideEffects,
 )

data NewUnique :: Effect

type instance DispatchOf NewUnique = Static WithSideEffects
data instance StaticRep NewUnique = NewUniqueRep

newUnique :: (NewUnique :> es) => Eff es Unique
newUnique = unsafeEff_ (Unique.newUnique)

runNewUnique :: (IOE :> es) => Eff (NewUnique : es) a -> Eff es a
runNewUnique eff = evalStaticRep NewUniqueRep eff
