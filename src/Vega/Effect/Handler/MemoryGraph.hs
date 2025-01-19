module Vega.Effect.Handler.MemoryGraph () where

import Relude hiding (Type)

import Vega.Syntax
import Vega.Effect.GlobalTypes
import Vega.Effect.Dependency (DependencyManagement)

import Effectful

data Dependency = DeclarationDependency GlobalName

data MemoryGraph = MkMemoryGraph
    { typeInfo :: IORef (Map GlobalName Type)
    , declarationDependencies :: IORef (Map GlobalName Dependency)

    , moduleContents :: IORef ()
    }

runMemoryGraph :: (IOE :> es) => MemoryGraph -> Eff (GlobalTypes : DependencyManagement : es) a -> Eff es a
runMemoryGraph = undefined
