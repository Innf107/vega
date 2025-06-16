{-# LANGUAGE RecursiveDo #-}

module Vega.WorkQueue (WorkQueue, WorkQueueNode, new, append, popFirst, delete) where

import Relude

import Control.Monad.Fix (MonadFix)

data WorkQueueNode a = MkWorkQueueNode
    { element :: a
    , previous :: IORef (WorkQueueNode a)
    , next :: IORef (WorkQueueNode a)
    }

instance Eq (WorkQueueNode a) where
    -- We use equality of the 'previous' ref as a proxy for node equality.
    -- This relies on the assumption that we never share references
    -- (which we never do if nodes are created with newNode)
    (==) :: WorkQueueNode a -> WorkQueueNode a -> Bool
    node1 == node2 = node1.previous == node2.previous

newtype WorkQueue a = MkWorkQueue
    { firstAndLast :: IORef (Maybe (WorkQueueNode a, WorkQueueNode a))
    }

new :: (MonadIO io) => io (WorkQueue a)
new = do
    firstAndLast <- newIORef Nothing
    pure (MkWorkQueue{firstAndLast})

newNode :: (MonadIO io) => a -> WorkQueueNode a -> WorkQueueNode a -> io (WorkQueueNode a)
newNode element previous next = do
    previous <- newIORef previous
    next <- newIORef next
    pure (MkWorkQueueNode{element, previous, next})

append :: (MonadIO io, MonadFix io) => WorkQueue a -> a -> io (WorkQueueNode a)
append queue element =
    readIORef queue.firstAndLast >>= \case
        Nothing -> do
            rec node <- newNode element node node
            writeIORef queue.firstAndLast (Just (node, node))
            pure node
        Just (first, last) -> do
            previous <- newIORef last
            next <- newIORef first
            let node = MkWorkQueueNode{element, previous, next}
            writeIORef last.next node
            writeIORef first.previous node

            writeIORef queue.firstAndLast (Just (first, node))
            pure node

popFirst :: (MonadIO io) => WorkQueue a -> io (Maybe a)
popFirst queue =
    readIORef queue.firstAndLast >>= \case
        Nothing -> pure Nothing
        Just (first, _) -> do
            delete queue first
            pure (Just first.element)

{- | Delete a node from a work queue. This does *not* reliably check if the node is contained in the queue.
After calling this, the passed node should not be used anymore
-}
delete :: (HasCallStack, MonadIO io) => WorkQueue a -> WorkQueueNode a -> io ()
delete queue node = do
    readIORef queue.firstAndLast >>= \case
        Nothing -> error "Vega.WorkQueue.delete: trying to delete node from an empty queue"
        Just (first, last)
            | first == last && first /= node -> error "Vega.WorkQueue.delete: trying to delete node from a 1 element queue that doesn't contain it"
            | first == last -> do
                writeIORef queue.firstAndLast Nothing
            | first == node -> do
                previous <- readIORef node.previous
                next <- readIORef node.next

                writeIORef previous.next next
                writeIORef next.previous previous

                writeIORef queue.firstAndLast (Just (next, last))
            | last == node -> do
                previous <- readIORef node.previous
                next <- readIORef node.next

                writeIORef previous.next next
                writeIORef next.previous previous

                writeIORef queue.firstAndLast (Just (first, previous))
            | otherwise -> do
                previous <- readIORef node.previous
                next <- readIORef node.next

                writeIORef previous.next next
                writeIORef next.previous previous
