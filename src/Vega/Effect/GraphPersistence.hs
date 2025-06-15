{-# LANGUAGE TemplateHaskell #-}

module Vega.Effect.GraphPersistence where

import Relude hiding (Type)

import Vega.Syntax hiding (Effect)

import Effectful
import Effectful.TH (makeEffect)

import Vega.Error (Error, RenameError, TypeError)

data GraphData error a
    = Ok a
    | Missing {previous :: Maybe a}
    | Failed {previous :: Maybe a, error :: error}

data WorkItem
    = Rename GlobalName
    | TypeCheck GlobalName

data GraphPersistence :: Effect where
    -- Module Data
    LastKnownDeclarations :: FilePath -> GraphPersistence m (Maybe (HashMap GlobalName (Declaration Parsed)))
    SetKnownDeclarations :: FilePath -> HashMap GlobalName (Declaration Parsed) -> GraphPersistence m ()
    GetModuleImportScope :: ModuleName -> GraphPersistence m ImportScope
    SetModuleImportScope :: ModuleName -> ImportScope -> GraphPersistence m ()
    -- Declarations
    AddDeclaration :: Declaration Parsed -> GraphPersistence m ()
    GetParsed :: GlobalName -> GraphPersistence m (Declaration Parsed)
    SetParsed :: Declaration Parsed -> GraphPersistence m ()
    GetRenamed :: GlobalName -> GraphPersistence m (GraphData RenameError (Declaration Renamed))
    SetRenamed :: Declaration Renamed -> GraphPersistence m ()
    GetTyped :: GlobalName -> GraphPersistence m (GraphData TypeError (Declaration Typed))
    SetTyped :: Declaration Typed -> GraphPersistence m ()
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
    GetGlobalType :: GlobalName -> GraphPersistence m (Either Type (TypeSyntax Renamed))
    CacheGlobalType :: GlobalName -> Type -> GraphPersistence m ()
    FindMatchingNames :: Text -> GraphPersistence m (HashSet GlobalName)
    GetErrors :: GlobalName -> GraphPersistence m (Seq Error)
    -- Compilation
    GetCurrentErrors :: GraphPersistence m (Seq Error)
    GetRemainingWork :: GraphPersistence m (Maybe WorkItem)

makeEffect ''GraphPersistence
