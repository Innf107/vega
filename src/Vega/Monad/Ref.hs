module Vega.Monad.Ref (MonadRef (..)) where

import Vega.Prelude

{- | MonadRef represents a canonical way to create and manipulate mutable references.
These are in general **NOT** expected to be thread safe but should otherwise
satisfy some obvious properties (again ignoring any concurrent accesses):

> writeRef ref x >> readRef x = writeRef ref x >> pure x
> writeRef ref x >> writeRef ref y = writeRef ref y
> newRef x >>= readRef = pure x
-}
class (Monad m) => MonadRef m where
    type Ref m :: HSType -> HSType

    writeRef :: Ref m a -> a -> m ()
    readRef :: Ref m a -> m a
    newRef :: a -> m (Ref m a)

instance MonadRef IO where
    type Ref IO = IORef
    writeRef = writeIORef
    readRef = readIORef
    newRef = newIORef

instance MonadRef (ST s) where
    type Ref (ST s) = STRef s
    writeRef = writeSTRef
    readRef = readSTRef
    newRef = newSTRef

instance MonadRef STM where
    type Ref STM = TVar
    writeRef = writeTVar
    readRef = readTVar
    newRef = newTVar
