{-# LANGUAGE RecursiveDo #-}

module Vega.Constraint (
    ConstraintSet,
    newConstraintSet,
    addToSet,
    currentConstraints,
    ConstraintQueue,
    newConstraintQueue,
    enqueue,
    dequeueAll,
    mergeInto,
) where

import Control.Monad.Fix (MonadFix)
import Data.Traversable (for)
import Relude
import Vega.ListBuilder (ListBuilder)
import Vega.ListBuilder qualified as ListBuilder
import Vega.Panic (panic)

newtype ConstraintSet constraint = MkConstraintSet
    { start :: IORef (Maybe (ConstraintNode constraint))
    }
    deriving newtype (Eq)

data ConstraintNode constraint = MkConstraintNode
    { constraint :: constraint
    , previous :: IORef (ConstraintNode constraint)
    , next :: IORef (ConstraintNode constraint)
    }

instance Eq (ConstraintNode constraint) where
    -- We can rely on every node having unique previous/next IORefs
    -- to provide the identity for our mutable objects
    node1 == node2 = node1.previous == node2.previous

newConstraintSet :: (MonadIO io) => io (ConstraintSet constraint)
newConstraintSet = do
    start <- newIORef Nothing
    pure (MkConstraintSet{start})

-- | O(1)
addToSetWithReference :: (MonadIO io, MonadFix io) => ConstraintSet constraint -> constraint -> io (ConstraintNode constraint)
addToSetWithReference set constraint = do
    readIORef set.start >>= \case
        Nothing -> do
            rec previous <- newIORef node
                next <- newIORef node
                let node =
                        MkConstraintNode
                            { constraint
                            , previous
                            , next
                            }
            writeIORef set.start (Just node)
            pure node
        Just start -> do
            nextNode <- readIORef start.next

            previous <- newIORef start
            next <- newIORef nextNode

            let node =
                    MkConstraintNode
                        { constraint
                        , previous
                        , next
                        }
            writeIORef start.next node
            pure node

-- | O(1)
addToSet :: (MonadIO io, MonadFix io) => ConstraintSet constraint -> constraint -> io ()
addToSet constraintSet constraint = do
    _ <- addToSetWithReference constraintSet constraint
    pure ()

removeNode :: (MonadIO io) => ConstraintSet constraint -> ConstraintNode constraint -> io ()
removeNode constraintSet node = do
    previous <- readIORef node.previous
    next <- readIORef node.next
    if node == next
        then do
            -- This is the only node in the set so we only need to update it
            -- and can leave the pointers of the node alone (to be garbage collected)
            writeIORef constraintSet.start Nothing
        else do
            start <- readIORef constraintSet.start
            when (start == Just node) do
                writeIORef constraintSet.start (Just next)

            writeIORef previous.next next
            writeIORef next.previous previous

-- | O(n)
currentConstraints :: (MonadIO io) => ConstraintSet constraint -> io [constraint]
currentConstraints set =
    readIORef set.start >>= \case
        Nothing -> pure []
        Just start -> do
            let go constraints node = do
                    next <- readIORef node.next
                    if next == start
                        then
                            pure [node.constraint]
                        else
                            go (node.constraint : constraints) next
            go [] start

data ConstraintQueue constraint = MkConstraintQueue
    { set :: ConstraintSet constraint
    , blockedConstraints :: IORef (ListBuilder (ConstraintNode constraint))
    }

-- | O(1)
newConstraintQueue :: (MonadIO io) => ConstraintSet constraint -> io (ConstraintQueue constraint)
newConstraintQueue set = do
    blockedConstraints <- newIORef mempty
    pure (MkConstraintQueue{set, blockedConstraints})

-- | O(1)
enqueue :: (MonadIO io, MonadFix io) => ConstraintQueue constraint -> constraint -> io ()
enqueue queue constraint = do
    node <- addToSetWithReference queue.set constraint
    modifyIORef' queue.blockedConstraints (<> ListBuilder.singleton node)

{- | Clear this queue and return all its constraints.

The queue remains operational afterwards so new constraints can be added again.

O(1) amortized
-}
dequeueAll :: (MonadIO io) => ConstraintQueue constraint -> io [constraint]
dequeueAll queue = do
    constraintNodes <- readIORef queue.blockedConstraints
    writeIORef queue.blockedConstraints mempty
    for (ListBuilder.toList constraintNodes) \node -> do
        removeNode queue.set node
        pure node.constraint

{- | Move all the constraints from the first queue into the second, clearing the first.
Both queues need to be part of the same 'ConstraintSet'

This is equivalent to calling 'dequeueAll' on the first queue and manually re-'enqueue'ing all the
elements into the second one (but significantly more efficient)

O(1)
-}
mergeInto :: (HasCallStack, MonadIO io) => ConstraintQueue constraint -> ConstraintQueue constraint -> io ()
mergeInto queue1 queue2 = do
    when (queue1.set /= queue2.set) do
        panic "Trying to merge constraint queues from different constraint sets"

    firstConstraints <- readIORef queue1.blockedConstraints
    writeIORef queue1.blockedConstraints mempty

    modifyIORef' queue2.blockedConstraints (<> firstConstraints)
