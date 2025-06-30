{-# LANGUAGE TemplateHaskell #-}

module Vega.Effect.GraphPersistence where

import Relude hiding (Type)

import Vega.Syntax hiding (Effect)

import Effectful
import Effectful.TH (makeEffect)

import Vega.BuildConfig (Backend)
import Vega.Error (CompilationError, RenameError, RenameErrorSet, TypeError, TypeErrorSet)

data GraphData error a
    = Ok a
    | Missing {previous :: Maybe a}
    | Failed {previous :: Maybe a, error :: error}

data WorkItem
    = Rename GlobalName
    | TypeCheck GlobalName
    | CompileToJS GlobalName
    deriving (Show)

data GraphPersistence :: Effect where
    -- Module Data
    LastKnownDeclarations :: FilePath -> GraphPersistence m (Maybe (HashMap GlobalName (Declaration Parsed)))
    SetKnownDeclarations :: FilePath -> HashMap GlobalName (Declaration Parsed) -> GraphPersistence m ()
    GetModuleImportScope :: ModuleName -> GraphPersistence m ImportScope
    SetModuleImportScope :: ModuleName -> ImportScope -> GraphPersistence m ()
    -- Declarations
    DoesDeclarationExist :: GlobalName -> GraphPersistence m Bool
    AddDeclaration :: Declaration Parsed -> GraphPersistence m ()
    GetParsed :: GlobalName -> GraphPersistence m (Declaration Parsed)
    SetParsed :: Declaration Parsed -> GraphPersistence m ()
    GetRenamed :: GlobalName -> GraphPersistence m (GraphData RenameErrorSet (Declaration Renamed))
    SetRenamed :: Declaration Renamed -> GraphPersistence m ()
    GetTyped :: GlobalName -> GraphPersistence m (GraphData TypeErrorSet (Declaration Typed))
    SetTyped :: Declaration Typed -> GraphPersistence m ()
    GetCompiledJS :: GlobalName -> GraphPersistence m (GraphData Void LText)
    SetCompiledJS :: GlobalName -> LText -> GraphPersistence m ()
    -- Invalidation
    RemoveDeclaration :: GlobalName -> GraphPersistence m ()
    Invalidate :: GlobalName -> GraphPersistence m ()
    InvalidateRenamed :: Maybe RenameErrorSet -> GlobalName -> GraphPersistence m ()
    InvalidateTyped :: Maybe TypeErrorSet -> GlobalName -> GraphPersistence m ()
    -- Dependencies
    GetDependencies :: GlobalName -> GraphPersistence m (HashSet GlobalName)
    GetDependents :: GlobalName -> GraphPersistence m (HashSet GlobalName)
    AddDependency :: GlobalName -> GlobalName -> GraphPersistence m ()
    ---------------- ^ dependent   ^
    ------------------------------ | dependency
    -- Specific accesses
    GetGlobalType :: GlobalName -> GraphPersistence m (Either Type (TypeSyntax Renamed))
    CacheGlobalType :: GlobalName -> Type -> GraphPersistence m ()
    FindMatchingNames :: Text -> GraphPersistence m (HashMap GlobalName NameKind)
    GetErrors :: GlobalName -> GraphPersistence m (Seq CompilationError)
    -- Compilation
    GetCurrentErrors :: GraphPersistence m (Seq CompilationError)
    GetRemainingWork :: Backend -> GraphPersistence m (Seq WorkItem)

makeEffect ''GraphPersistence
