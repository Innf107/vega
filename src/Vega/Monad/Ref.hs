module Vega.Monad.Ref (MonadRef (..)) where

import Vega.Prelude

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