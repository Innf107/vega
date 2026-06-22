module Vega.OutArray (
    OutArray,
    new,
    fill,
    fillRemaining,
    initializedToVector,
) where

import Relude

import Control.Monad.ST.Strict (ST)
import Data.Vector.Generic qualified as Vector
import Data.Vector.Generic.Mutable qualified as Vector.Mutable
import Data.Vector.Strict (MVector, Vector)
import Effectful (Eff, (:>))
import Vega.Effect.ST (STE, liftST)
import Vega.Panic (panic)
import Vega.Pretty qualified as Pretty

newtype OutArray s a = MkOutArray
    { elements :: MVector s (Maybe a)
    }

new :: forall s es a. (STE s :> es) => Int -> Eff es (OutArray s a)
new size = liftST $ MkOutArray <$> Vector.Mutable.replicate size Nothing

fill :: (HasCallStack, STE s :> es) => OutArray s a -> Int -> a -> Eff es ()
fill (MkOutArray{elements}) index value = liftST do
    Vector.Mutable.read elements index >>= \case
        Nothing -> Vector.Mutable.write elements index (Just value)
        Just _ -> panic $ "OutArray.fill: Conflicting element values at index " <> Pretty.number index

fillRemaining :: (STE s :> es) => OutArray s a -> a -> Eff es ()
fillRemaining outArray fillValue = liftST $ for_ @[] [0 .. Vector.Mutable.length outArray.elements - 1] \index -> do
    Vector.Mutable.read outArray.elements index >>= \case
        Nothing -> Vector.Mutable.write outArray.elements index (Just fillValue)
        Just{} -> pure ()

initializedToVector :: (HasCallStack, STE s :> es) => OutArray s a -> Eff es (Vector a)
initializedToVector outArray = liftST do
    Vector.generateM (Vector.Mutable.length outArray.elements) \index ->
        Vector.Mutable.read outArray.elements index >>= \case
            Nothing -> panic $ "OutArray.initializedToVector: Uninitialized element at index " <> Pretty.number index
            Just value -> pure value
