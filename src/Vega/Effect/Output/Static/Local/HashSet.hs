module Vega.Effect.Output.Static.Local.HashSet (Output (..), output, runOutputHashSet) where

import Relude hiding (toList)

import Data.HashSet qualified as HashSet
import Effectful (Dispatch (Static), DispatchOf, Eff, Effect, (:>))
import Effectful.Dispatch.Static (
    StaticRep,
    runStaticRep,
    stateStaticRep,
    pattern NoSideEffects,
 )

data Output (o :: Type) :: Effect

output :: forall o es. (Output o :> es, Hashable o) => o -> Eff es ()
output o = stateStaticRep (\(OutputRep set) -> ((), OutputRep (HashSet.insert o set)))

type instance DispatchOf (Output o) = Static NoSideEffects
newtype instance StaticRep (Output o) = OutputRep (HashSet o)

runOutputHashSet :: (Hashable o) => Eff (Output o ': es) a -> Eff es (a, HashSet o)
runOutputHashSet eff = do
    (result, OutputRep set) <- runStaticRep (OutputRep []) eff
    pure (result, set)
