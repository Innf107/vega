{-# LANGUAGE RequiredTypeArguments #-}

module Vega.Effect.ST (
    STE,
    STRef,
    runSTE,
    liftST,
    newSTRef,
    readSTRef,
    writeSTRef,
    (=:),
    modifySTRef,
) where

import Control.Monad.ST (ST)
import Control.Monad.ST.Unsafe (unsafeSTToIO)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))

import Data.STRef.Strict (STRef)
import Effectful
import Effectful.Dispatch.Static

import Data.STRef qualified as STRef
import Prelude (($!))

-- | An effect for embedding 'ST' computations
data STE (s :: Type) :: Effect

type role STE nominal phantom phantom

type instance DispatchOf (STE s) = Static NoSideEffects
data instance StaticRep (STE s) = STE

{- | Run the 'STE' effect.
Since effectful allows several 'STE' effects to be in scope at once,
it can be ambiguous which one a usage of 'liftST' refers to.
In these cases, the 's' parameter can be used to disambiguate.
In particular, instead of @liftST $ newSTRef x@, you will have to write
@liftST \@s $ newSTRef x@.
-}
runSTE :: (forall s -> Eff (STE s : es) a) -> Eff es a
runSTE eff = evalStaticRep STE (eff (type ()))

liftST :: forall s a es. (STE s :> es) => ST s a -> Eff es a
liftST st = unsafeEff_ (unsafeSTToIO st)

newSTRef :: (STE s :> es) => a -> Eff es (STRef s a)
newSTRef x = liftST (STRef.newSTRef x)

readSTRef :: (STE s :> es) => STRef s a -> Eff es a
readSTRef x = liftST (STRef.readSTRef x)

writeSTRef :: (STE s :> es) => STRef s a -> a -> Eff es ()
writeSTRef ref x = liftST (STRef.writeSTRef ref $! x)

(=:) :: (STE s :> es) => STRef s a -> a -> Eff es ()
(=:) = writeSTRef

modifySTRef :: (STE s :> es) => STRef s a -> (a -> a) -> Eff es ()
modifySTRef ref f = liftST (STRef.modifySTRef' ref f)