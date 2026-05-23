{-# LANGUAGE RecursiveDo #-}

module Vega.Constraint (
    ManageConstraints,
    runManageConstraints,
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
import Effectful (DispatchOf, Eff, Effect, IOE, (:>), pattern Static)
import Effectful.Dispatch.Static (StaticRep, evalStaticRep, unsafeEff_, pattern WithSideEffects)
import Relude
import Vega.ListBuilder (ListBuilder)
import Vega.ListBuilder qualified as ListBuilder
import Vega.Panic (panic)

data ManageConstraints :: Effect
type instance DispatchOf ManageConstraints = Static WithSideEffects
data instance StaticRep ManageConstraints = ManageConstraintsRep

runManageConstraints :: (IOE :> es) => Eff (ManageConstraints : es) a -> Eff es a
runManageConstraints eff = evalStaticRep ManageConstraintsRep eff

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
    (==) :: ConstraintNode constraint -> ConstraintNode constraint -> Bool
    node1 == node2 = node1.previous == node2.previous

newConstraintSet :: (ManageConstraints :> es) => Eff es (ConstraintSet constraint)
newConstraintSet = unsafeEff_ do
    start <- newIORef Nothing
    pure (MkConstraintSet{start})

-- | O(1)
addToSetWithReference :: (ManageConstraints :> es) => ConstraintSet constraint -> constraint -> Eff es (ConstraintNode constraint)
addToSetWithReference set constraint = unsafeEff_ do
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
            when (start == nextNode) do
                writeIORef start.previous node
            pure node

-- | O(1)
addToSet :: (ManageConstraints :> es) => ConstraintSet constraint -> constraint -> Eff es ()
addToSet constraintSet constraint = do
    _ <- addToSetWithReference constraintSet constraint
    pure ()

removeNode :: (ManageConstraints :> es) => ConstraintSet constraint -> ConstraintNode constraint -> Eff es ()
removeNode constraintSet node = unsafeEff_ do
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
currentConstraints :: (ManageConstraints :> es) => ConstraintSet constraint -> Eff es [constraint]
currentConstraints set = unsafeEff_ do
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
newConstraintQueue :: (ManageConstraints :> es) => ConstraintSet constraint -> Eff es (ConstraintQueue constraint)
newConstraintQueue set = unsafeEff_ do
    blockedConstraints <- newIORef mempty
    pure (MkConstraintQueue{set, blockedConstraints})

-- | O(1)
enqueue :: (ManageConstraints :> es) => ConstraintQueue constraint -> constraint -> Eff es ()
enqueue queue constraint = do
    node <- addToSetWithReference queue.set constraint
    unsafeEff_ $ modifyIORef' queue.blockedConstraints (<> ListBuilder.singleton node)

{- | Clear this queue and return all its constraints.

The queue remains operational afterwards so new constraints can be added again.

O(1) amortized
-}
dequeueAll :: (ManageConstraints :> es) => ConstraintQueue constraint -> Eff es [constraint]
dequeueAll queue = do
    constraintNodes <- unsafeEff_ $ readIORef queue.blockedConstraints
    unsafeEff_ $ writeIORef queue.blockedConstraints mempty
    for (ListBuilder.toList constraintNodes) \node -> do
        removeNode queue.set node
        pure node.constraint

{- | Move all the constraints from the first queue into the second, clearing the first.
Both queues need to be part of the same 'ConstraintSet'

This is equivalent to calling 'dequeueAll' on the first queue and manually re-'enqueue'ing all the
elements into the second one (but significantly more efficient)

O(1)
-}
mergeInto :: (HasCallStack, ManageConstraints :> es) => ConstraintQueue constraint -> ConstraintQueue constraint -> Eff es ()
mergeInto queue1 queue2 = unsafeEff_ do
    when (queue1.set /= queue2.set) do
        panic "Trying to merge constraint queues from different constraint sets"

    firstConstraints <- readIORef queue1.blockedConstraints
    writeIORef queue1.blockedConstraints mempty

    modifyIORef' queue2.blockedConstraints (<> firstConstraints)
