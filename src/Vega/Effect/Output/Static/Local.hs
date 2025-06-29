module Vega.Effect.Output.Static.Local (
    Output,
    output,
    outputAll,
    runOutputList,
    runOutputSeq,
    execOutputList,
    execOutputSeq,
) where

import Relude hiding (toList)

import Effectful (Dispatch (Static), DispatchOf, Eff, Effect, (:>))
import Effectful.Dispatch.Static (
    StaticRep,
    execStaticRep,
    getStaticRep,
    runStaticRep,
    stateStaticRep,
    unsafeEff_,
    pattern NoSideEffects,
 )
import GHC.IsList (IsList (..))

data Output (o :: Type) :: Effect

output :: forall o es. (Output o :> es) => o -> Eff es ()
output o = stateStaticRep (\(OutputRep list) -> ((), OutputRep (o : list)))

outputAll :: forall o list es. (Output o :> es, IsList list, Item list ~ o) => list -> Eff es ()
outputAll outputs = stateStaticRep (\(OutputRep list) -> ((), OutputRep (toList outputs <> list)))

type instance DispatchOf (Output o) = Static NoSideEffects
newtype instance StaticRep (Output o) = OutputRep ([o])

runOutputList :: forall o a es. Eff (Output o ': es) a -> Eff es (a, [o])
runOutputList eff = coerce $ runStaticRep (OutputRep []) eff

runOutputSeq :: forall o a es. Eff (Output o ': es) a -> Eff es (a, Seq o)
runOutputSeq eff = do
    (result, list) <- runOutputList eff
    pure (result, fromList list)

execOutputList :: forall o a es. Eff (Output o ': es) a -> Eff es [o]
execOutputList eff = coerce $ execStaticRep (OutputRep []) eff

execOutputSeq :: forall o a es. Eff (Output o ': es) a -> Eff es (Seq o)
execOutputSeq eff = fromList <$> execOutputList eff