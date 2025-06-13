{-# LANGUAGE TemplateHaskell #-}

module Vega.Effect.GraphPersistence where

import Relude hiding (Type)

import Vega.Syntax hiding (Effect)

import Effectful
import Effectful.Dispatch.Dynamic (send)
import Effectful.TH (makeEffect)

import Vega.Error (Error, RenameError, TypeError)

data GraphData error a
    = Ok a
    | Missing
    | Failed error

data GraphPersistence :: Effect where
    -- File Data
    LastKnownDeclarations :: FilePath -> GraphPersistence m (Maybe (HashMap GlobalName (Declaration Parsed)))
    SetKnownDeclarations :: FilePath -> HashMap GlobalName (Declaration Parsed) -> GraphPersistence m ()
    -- New Declarations
    AddDeclaration :: Declaration Parsed -> GraphPersistence m ()
    -- Declaration Retrieval
    GetParsed :: GlobalName -> GraphPersistence m (Declaration Parsed)
    GetRenamed :: GlobalName -> GraphPersistence m (GraphData RenameError (Declaration Renamed))
    GetTyped :: GlobalName -> GraphPersistence m (GraphData TypeError (Declaration Typed))
    -- Invalidation
    RemoveDeclaration :: GlobalName -> GraphPersistence m ()
    Invalidate :: GlobalName -> GraphPersistence m ()
    InvalidateRenamed :: Maybe RenameError -> GlobalName -> GraphPersistence m ()
    InvalidateTyped :: Maybe TypeError -> GlobalName -> GraphPersistence m ()
    -- Dependencies
    GetDependencies :: GlobalName -> GraphPersistence m (HashSet GlobalName)
    GetDependents :: GlobalName -> GraphPersistence m (HashSet GlobalName)
    AddDependency :: GlobalName -> GlobalName -> GraphPersistence m ()
    ---------------- ^ dependent   ^
    ------------------------------ | dependency
    -- Specific accesses
    GetGlobalType :: GlobalName -> GraphPersistence m (Maybe Type)
    GetCurrentErrors :: GraphPersistence m (Seq Error)

makeEffect ''GraphPersistence
