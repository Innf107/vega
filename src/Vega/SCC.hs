module Vega.SCC (SCCId, computeSCC) where

import Relude hiding (State, evalState, get, modify, put)
import Relude.Extra

import Effectful

import Data.HashSet qualified as HashSet
import Data.UUID (UUID)
import Data.UUID.V4 (nextRandom)

-- TODO: try to use something more efficient (maybe twitter-style snowflakes?)
newtype SCCId = MkSCCId UUID
    deriving (Show, Eq)

newSCCId :: (IOE :> es) => Eff es SCCId
newSCCId = MkSCCId <$> liftIO nextRandom

-- Technically IOE isn't necessary here but manually using State effects gets messy
-- and effectful doesn't really have a great alternative to ST (yet).
-- (and also every place we use this in is in IOE anyway so it doesn't really matter).
computeSCC ::
    forall node es.
    (Show node, Hashable node, IOE :> es) =>
    -- | Return a list of nodes only if the node has not been assigned an SCC already
    (node -> Eff es (Maybe [node])) ->
    node ->
    Eff es (HashMap node SCCId)
computeSCC outEdgesOrPrecomputedSCC node = do
    visited :: IORef (HashSet node) <- newIORef mempty
    currentDFSNum :: IORef Int <- newIORef 0
    dfsNums :: IORef (HashMap node Int) <- newIORef mempty

    openSCCs :: IORef [node] <- newIORef [node]
    openNodes :: IORef [node] <- newIORef [node]

    sccs :: IORef (HashMap node SCCId) <- newIORef mempty

    let go node = do
            dfsNum <- readIORef currentDFSNum
            writeIORef currentDFSNum (dfsNum + 1)
            modifyIORef' dfsNums (insert node dfsNum)
            outEdgesOrPrecomputedSCC node >>= \case
                Nothing -> pure ()
                Just neighbors -> do
                    for_ neighbors \neighbor -> do
                        visitedUntilNow <- readIORef visited
                        case HashSet.member neighbor visitedUntilNow of
                            False -> do
                                modifyIORef' visited (HashSet.insert neighbor)
                                modifyIORef' openSCCs (neighbor :)
                                modifyIORef' openNodes (neighbor :)

                                go neighbor
                            True -> do
                                dfsNumsUntilNow <- readIORef dfsNums
                                let dfsNumOf otherNode = case lookup otherNode dfsNumsUntilNow of
                                        Nothing -> error $ "DFS number of '" <> show node <> "' not found"
                                        Just dfsNum -> dfsNum

                                modifyIORef' openSCCs (dropWhile (\representative -> dfsNumOf representative >= dfsNum))
                    -- backtrack
                    readIORef openSCCs >>= \case
                        (topRepresentative : rest)
                            | topRepresentative == node -> do
                                writeIORef openSCCs rest

                                sccId <- newSCCId

                                let assignSCC = \case
                                        [] -> pure []
                                        (openNode : rest) -> do
                                            modifyIORef' sccs (insert openNode sccId)
                                            if openNode == node
                                                then pure rest
                                                else assignSCC rest
                                currentOpenNodes <- readIORef openNodes
                                remainingOpenNodes <- assignSCC currentOpenNodes
                                writeIORef openNodes remainingOpenNodes
                        _ -> pure ()

    go node
    readIORef sccs
