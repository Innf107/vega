{-# LANGUAGE TemplateHaskell #-}

module Vega.Effect.GraphPersistence where

import Relude hiding (Type)

import Vega.Syntax hiding (Effect)

import Effectful
import Effectful.TH (makeEffect)

import Vega.BuildConfig (Backend)
import Vega.Error (CompilationError, RenameErrorSet, TypeErrorSet)
import Vega.SCC (SCCId)

data GraphData error a
    = Ok a
    | Missing {previous :: Maybe a}
    | Failed {previous :: Maybe a, error :: error}

data WorkItem
    = Rename DeclarationName
    | TypeCheck DeclarationName
    | CompileToJS DeclarationName
    deriving (Show)

data GraphPersistence :: Effect where
    -- Module Data
    LastKnownDeclarations :: FilePath -> GraphPersistence m (Maybe (HashMap DeclarationName (Declaration Parsed)))
    SetKnownDeclarations :: FilePath -> HashMap DeclarationName (Declaration Parsed) -> GraphPersistence m ()
    GetModuleImportScope :: ModuleName -> GraphPersistence m ImportScope
    SetModuleImportScope :: ModuleName -> ImportScope -> GraphPersistence m ()
    -- Declarations
    DoesDeclarationExist :: DeclarationName -> GraphPersistence m Bool
    AddDeclaration :: Declaration Parsed -> GraphPersistence m ()
    GetParsed :: DeclarationName -> GraphPersistence m (Declaration Parsed)
    SetParsed :: Declaration Parsed -> GraphPersistence m ()
    GetRenamed :: DeclarationName -> GraphPersistence m (GraphData RenameErrorSet (Declaration Renamed))
    SetRenamed :: Declaration Renamed -> GraphPersistence m ()
    GetTyped :: DeclarationName -> GraphPersistence m (GraphData TypeErrorSet (Declaration Typed))
    SetTyped :: Declaration Typed -> GraphPersistence m ()
    GetCompiledJS :: DeclarationName -> GraphPersistence m (GraphData Void LText)
    SetCompiledJS :: DeclarationName -> LText -> GraphPersistence m ()
    -- Invalidation
    RemoveDeclaration :: DeclarationName -> GraphPersistence m ()
    Invalidate :: DeclarationName -> GraphPersistence m ()
    InvalidateRenamed :: Maybe RenameErrorSet -> DeclarationName -> GraphPersistence m ()
    InvalidateTyped :: Maybe TypeErrorSet -> DeclarationName -> GraphPersistence m ()
    -- Dependencies
    GetDependencies :: DeclarationName -> GraphPersistence m (HashSet DeclarationName)
    GetDependents :: DeclarationName -> GraphPersistence m (HashSet DeclarationName)
    AddDependency :: DeclarationName -> DeclarationName -> GraphPersistence m ()
    ---------------- ^ dependent   ^
    ------------------------------ | dependency
    GetSCC :: DeclarationName -> GraphPersistence m SCCId
    -- Specific accesses
    GetGlobalType :: GlobalName -> GraphPersistence m (Either Type (TypeSyntax Renamed))
    CacheGlobalType :: GlobalName -> Type -> GraphPersistence m ()
    GetCachedGlobalKind :: GlobalName -> GraphPersistence m (GraphData TypeErrorSet Kind)
    CacheGlobalKind :: GlobalName -> Kind -> GraphPersistence m ()
    FindMatchingNames :: Text -> GraphPersistence m (HashMap GlobalName NameKind)
    GetErrors :: DeclarationName -> GraphPersistence m (Seq CompilationError)
    -- Compilation
    GetCurrentErrors :: GraphPersistence m (Seq CompilationError)
    GetRemainingWork :: Backend -> GraphPersistence m (Seq WorkItem)
    --
    GetDefiningDeclaration :: GlobalName -> GraphPersistence m (Maybe DeclarationName)

makeEffect ''GraphPersistence
