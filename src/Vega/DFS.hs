module Vega.DFS (dfs) where

import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Sequence (Seq)
import Effectful (Eff, IOE, raise, (:>))
import Relude
import Streaming (Of, Stream)

{-# SPECIALIZE dfs ::
    forall vertex es.
    (Hashable vertex) =>
    Seq vertex ->
    (vertex -> Eff es (Seq vertex)) ->
    Eff es (HashSet vertex)
    #-}
{-# SPECIALIZE dfs ::
    forall vertex es a.
    (Hashable vertex) =>
    Seq vertex ->
    (vertex -> Stream (Of a) (Eff es) (Seq vertex)) ->
    Stream (Of a) (Eff es) (HashSet vertex)
    #-}
dfs ::
    forall m vertex.
    (Hashable vertex, Monad m) =>
    Seq vertex ->
    (vertex -> m (Seq vertex)) ->
    m (HashSet vertex)
dfs roots onVertex = flip execStateT (HashSet.empty @vertex) do
    let go next = do
            modify (HashSet.insert next)
            neighbors <- lift $ onVertex next
            for_ neighbors \neighbor -> do
                visited <- get
                case neighbor `HashSet.member` visited of
                    True -> pure ()
                    False -> do
                        go neighbor
    for_ roots go
