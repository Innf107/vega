module Vega.Effect.Dependency (
    DependencyManagement (..),
    dependencyBetween,
    Dependency (..),
    declareDependency,
) where

import Vega.Syntax

import Effectful
import Effectful.Dispatch.Dynamic (send)

data DependencyManagement :: Effect where
    DependencyBetween :: GlobalName -> GlobalName -> DependencyManagement m ()

type instance DispatchOf DependencyManagement = Dynamic

dependencyBetween :: (DependencyManagement :> es) => GlobalName -> GlobalName -> Eff es ()
dependencyBetween name1 name2 = send (DependencyBetween name1 name2)

data Dependency :: Effect where
    DeclareDependency :: GlobalName -> Dependency m ()

type instance DispatchOf Dependency = Dynamic

{- | Declare that the current declaration depends on the given declaration and will need
    to be recompiled if it changes
-}
declareDependency :: (Dependency :> es) => GlobalName -> Eff es ()
declareDependency name = send (DeclareDependency name)
