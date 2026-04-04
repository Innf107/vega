{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Vega.Effect.GraphPersistence where

import Relude hiding (State, execState, Type, evalState, get, modify, put)

import Vega.Syntax hiding (Effect)

import Effectful
import Effectful.State.Static.Local (State, evalState, execState, get, modify, put)
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
import Vega.Panic (panic)
import Vega.Debug (showHeadConstructor)
import Data.Traversable (for)

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

data DataConstructorIndex
    = OnlyConstructor
    | MultiConstructor Int

data GlobalRepresentation
    = GlobalVar Core.Representation
    | GlobalClosure

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
    -- TODO: not super happy about having this separate from declarations
    GetGlobalRepresentation :: GlobalName -> GraphPersistence m GlobalRepresentation
    SetGlobalRepresentation :: GlobalName -> GlobalRepresentation -> GraphPersistence m ()
    --
    GetDefiningDeclaration :: GlobalName -> GraphPersistence m (Maybe DeclarationName)
    GetDataConstructorIndex :: Name -> GraphPersistence m DataConstructorIndex
    SetDataConstructorIndex :: Name -> DataConstructorIndex -> GraphPersistence m ()

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

getAutoBoxing :: GraphPersistence :> es => GlobalName -> Eff es (Seq Bool)
getAutoBoxing dataConstructorName = getDefiningDeclaration dataConstructorName >>= \case
    Nothing -> panic $ "Trying to access auto-boxing of data constructor with missing declaration: " <> prettyGlobal DataConstructorKind dataConstructorName
    Just declaration -> getRenamed declaration >>= \case
        Missing{} -> undefined
        Failed{} -> undefined
        Ok (MkDeclaration{syntax = DefineVariantType _ _ constructors}) -> do
            -- TODO: cache the results for all constructors
            result <- execState Nothing $ for_ constructors \(_, name, parameters) -> do
                autoBoxingFlags <- for parameters \type_ -> do
                    ownSCC <- getSCC declaration
                    flip anyM (typeConstructorsS type_) \(_loc, name) -> case name of
                        Global globalName -> getDefiningDeclaration globalName >>= \case
                            -- If the type is primitive, it is obviously not in the same SCC as us
                            Nothing -> pure False
                            Just typeDeclaration -> do
                                otherSCC <- getSCC typeDeclaration
                                pure (ownSCC == otherSCC)
                        Local{} -> undefined
                -- TODO: cache autoBoxingFlags
                when (name == dataConstructorName) do
                    put (Just autoBoxingFlags)
            case result of
                Just autoBoxingFlags -> pure autoBoxingFlags
                Nothing -> panic $ "Definition of data constructor " <> prettyGlobal DataConstructorKind dataConstructorName <> " doesn't define it"
        Ok declaration -> panic $ "Data constructor " <> prettyGlobal DataConstructorKind dataConstructorName <> " refers to non-DefineVariantType declaration: " <> showHeadConstructor declaration.syntax


