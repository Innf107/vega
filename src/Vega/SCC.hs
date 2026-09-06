module Vega.SCC (SCCId, computeSCC) where

import Relude hiding (State, evalState, get, modify, put, trace)
import Relude.Extra

import Effectful

import Data.HashSet qualified as HashSet
import Data.UUID.V4 (nextRandom)

import Vega.Effect.ST (STE, STRef, liftST, modifySTRef, newSTRef, readSTRef, runSTE, (=:))
import Vega.Effect.Trace (Category (..), Trace, trace)
import Vega.Panic (assertM, panic)
import Vega.Pretty (Pretty, number, pretty)
import Vega.Pretty qualified as Pretty
import Vega.Syntax (DeclarationName)

-- We use the "root" declaration (the first one that was found by the DFS) as the representative of an SCC.
-- This is valid, even across different invocations of the algorithm, since SCCs are unique, we compute the representative
-- for every element of an SCC in one go (so they cannot disagree on their representative) and changes that extend or shrink an
-- SCC will invalidate the entire SCC anyway.
--
-- Which declaration *exactly* is chosen as the SCC may vary depending on the order the DFS takes and which declaration is checked first.
newtype SCCId = MkSCCId {representative :: DeclarationName}
    deriving stock (Eq)

instance Pretty SCCId where
    -- This is a bit hacky but we only use it for debugging anyway so it's fine
    pretty id = Pretty.keyword (Pretty.prettyPlain (pretty id.representative))

{- | Compute the set of all not previously computed SCCs that are reachable from this node.

The algorithm is based on Cheriyan-Mehlhorn-Gabow (https://arxiv.org/pdf/1703.10023)

If the entry point has already been assigned an SCC, this will return an empty map
-}
computeSCC ::
    forall es.
    (Trace :> es) =>
    -- | Return a list of nodes only if the node has not been assigned an SCC already
    (DeclarationName -> Eff es (Maybe [DeclarationName])) ->
    DeclarationName ->
    Eff es (HashMap DeclarationName SCCId)
computeSCC outEdgesOrPrecomputedSCC entryPoint = runSTE \(type s) -> do
    currentDFSNum :: STRef s Int <- newSTRef 0
    -- This is -1 if the node is already part of a closed component
    openDFSNums :: STRef s (HashMap DeclarationName Int) <- newSTRef mempty
    sccs :: STRef s (HashMap DeclarationName SCCId) <- newSTRef mempty

    roots :: STRef s [DeclarationName] <- newSTRef []
    open :: STRef s [DeclarationName] <- newSTRef []

    let dfs node =
            raise (outEdgesOrPrecomputedSCC node) >>= \case
                -- We can pretend that nodes with precomputed SCCs aren't there since they can never
                -- be part of any component we care about anyway
                Nothing -> pure ()
                Just neighbors -> do
                    dfsNum <- readSTRef currentDFSNum
                    currentDFSNum =: (dfsNum + 1)
                    modifySTRef openDFSNums (insert node dfsNum)
                    modifySTRef roots (node :)
                    modifySTRef open (node :)

                    for_ neighbors \neighbor -> do
                        currentOpenDFSNums <- readSTRef openDFSNums
                        case lookup neighbor currentOpenDFSNums of
                            Nothing -> dfs neighbor
                            Just neighborDFSNum
                                | neighborDFSNum == -1 -> pure ()
                                | otherwise -> do
                                    let dfsNumOf representative = case lookup representative currentOpenDFSNums of
                                            Nothing -> panic $ "DFS number for potential root " <> pretty representative <> " not found"
                                            Just dfsNum -> dfsNum
                                    modifySTRef roots (dropWhile (\representative -> dfsNumOf representative > neighborDFSNum))
                    readSTRef roots >>= \case
                        [] -> panic $ "No roots left after processing neighbors of " <> pretty node
                        (top : rest)
                            | top == node -> do
                                roots =: rest
                                currentOpen <- readSTRef open
                                let (inComponent, remainingOpen) = spanIncluding (/= node) currentOpen
                                for_ inComponent \nodeToClose -> do
                                    modifySTRef openDFSNums (insert nodeToClose -1)
                                    modifySTRef sccs (insert nodeToClose (MkSCCId{representative = node}))
                                open =: remainingOpen
                            | otherwise -> pure ()
    assertM (null <$> readSTRef roots)
    assertM (null <$> readSTRef open)
    dfs entryPoint
    readSTRef sccs

-- | Variant of 'span' that includes the first element that does not match the predicate in the left result
spanIncluding :: (a -> Bool) -> [a] -> ([a], [a])
spanIncluding predicate = \case
    [] -> ([], [])
    (x : xs)
        | predicate x -> do
            let (prefix, rest) = spanIncluding predicate xs
            (x : prefix, rest)
        | otherwise -> ([x], xs)
