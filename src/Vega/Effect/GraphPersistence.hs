{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Vega.Effect.GraphPersistence where

import Relude hiding (State, Type, evalState, get, modify, put)

import Vega.Syntax hiding (Effect)

import Effectful
import Effectful.State.Static.Local (State, evalState, get, modify)
import Effectful.TH (makeEffect)

import Data.HashSet qualified as HashSet
import Streaming (Stream, hoist)
import Streaming.Prelude (Of, yield)
import Vega.BuildConfig (Backend)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Error (CompilationError, RenameErrorSet, TypeErrorSet)
import Vega.Pretty (Pretty, keyword, pretty, (<+>))
import Vega.SCC (SCCId)
import Vega.Syntax qualified as Vega

data GraphData error a
    = Ok a
    | Missing {previous :: Maybe a}
    | Failed {previous :: Maybe a, error :: error}

data WorkItem
    = Rename DeclarationName
    | TypeCheck DeclarationName
    | CompileToJS DeclarationName
    | CompileToCore DeclarationName
    deriving (Show)
instance Pretty WorkItem where
    pretty (Rename name) = keyword "rename" <+> pretty name
    pretty (TypeCheck name) = keyword "type-check" <+> pretty name
    pretty (CompileToJS name) = keyword "compile-to-js" <+> pretty name
    pretty (CompileToCore name) = keyword "compile-to-core" <+> pretty name

data CachedType
    = RenamingFailed
    | CachedTypeSyntax (TypeSyntax Renamed)
    | CachedType Type

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
    GetCompiledJS :: DeclarationName -> GraphPersistence m (GraphData Void Text)
    SetCompiledJS :: DeclarationName -> Text -> GraphPersistence m ()
    GetCompiledCore :: DeclarationName -> GraphPersistence m (GraphData Void (Seq Core.Declaration))
    SetCompiledCore :: DeclarationName -> Seq Core.Declaration -> GraphPersistence m ()
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
    GetGlobalType :: GlobalName -> GraphPersistence m CachedType
    CacheGlobalType :: GlobalName -> Type -> GraphPersistence m ()
    GetCachedGlobalKind :: GlobalName -> GraphPersistence m (GraphData TypeErrorSet Kind)
    CacheGlobalKind :: GlobalName -> Kind -> GraphPersistence m ()
    FindMatchingNames :: Text -> NameKind -> GraphPersistence m (HashSet GlobalName)
    GetErrors :: DeclarationName -> GraphPersistence m (Seq CompilationError)
    -- Compilation
    GetCurrentErrors :: GraphPersistence m (Seq CompilationError)
    GetRemainingWork :: Backend -> GraphPersistence m (Seq WorkItem)
    --
    GetDefiningDeclaration :: GlobalName -> GraphPersistence m (Maybe DeclarationName)

makeEffect ''GraphPersistence

reachableFrom :: (GraphPersistence :> es) => DeclarationName -> Stream (Of DeclarationName) (Eff es) ()
reachableFrom name = hoist (evalState (mempty :: HashSet DeclarationName)) $ go name
  where
    go :: (GraphPersistence :> es, State (HashSet DeclarationName) :> es) => DeclarationName -> Stream (Of DeclarationName) (Eff es) ()
    go name = do
        yield name
        dependencies <- lift $ getDependencies name
        for_ dependencies \dependency -> do
            seenSoFar <- lift get
            when (not (HashSet.member dependency seenSoFar)) do
                lift $ modify (HashSet.insert dependency)
                go dependency
