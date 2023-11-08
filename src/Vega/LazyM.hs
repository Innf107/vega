module Vega.LazyM (
    LazyM,
    lazyM,
    lazyValueM,
    forceM,
) where

import Vega.Prelude

import Vega.Monad.Ref

data LazyRef m a
    = Delayed (m a)
    | Cached a

{- | Lazily delayed computations inside a monad.
This is *NOT* thread safe
-}
newtype LazyM m a = MkLazyM (Ref m (LazyRef m a))

lazyM :: (MonadRef outerM, Ref outerM ~ Ref innerM) => innerM a -> outerM (LazyM innerM a)
lazyM inner = do
    ref <- newRef (Delayed inner)
    pure (MkLazyM ref)

lazyValueM :: (MonadRef outerM, Ref outerM ~ Ref innerM) => a -> outerM (LazyM innerM a)
lazyValueM x = do
    ref <- newRef (Cached x)
    pure (MkLazyM ref)

forceM :: (MonadRef m) => LazyM m a -> m a
forceM (MkLazyM ref) =
    readRef ref >>= \case
        Cached result -> pure result
        Delayed computation -> do
            result <- computation
            writeRef ref (Cached result)
            pure result
