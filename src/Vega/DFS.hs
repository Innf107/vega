module Vega.DFS (dfs) where

import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Sequence (Seq)
import Effectful (Eff, IOE, raise, (:>))
import Effectful.State.Static.Local (execState, get, modify, put)
import Relude hiding (execState, get, modify, put)

dfs ::
    forall vertex es.
    (Hashable vertex) =>
    vertex ->
    (vertex -> Eff es (Seq vertex)) ->
    Eff es (HashSet vertex)
dfs initial onVertex = execState HashSet.empty do
    let go next = do
            modify (HashSet.insert next)
            neighbors <- raise $ onVertex next
            for_ neighbors \neighbor -> do
                visited <- get
                case neighbor `HashSet.member` visited of
                    True -> pure ()
                    False -> do
                        go neighbor
    go initial
