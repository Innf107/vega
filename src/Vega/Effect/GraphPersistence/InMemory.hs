{-# LANGUAGE PartialTypeSignatures #-}

module Vega.Effect.GraphPersistence.InMemory (runInMemory) where

import Relude hiding (Reader, Type, ask, runReader)
import Relude.Extra

import Data.HashSet qualified as HashSet

import Vega.Effect.GraphPersistence hiding (addDeclaration, addDependency, getCurrentErrors, getDependencies, getDependents, getGlobalType, getParsed, getRenamed, getTyped, invalidate, invalidateRenamed, invalidateTyped, lastKnownDeclarations, removeDeclaration, setKnownDeclarations)

import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.Reader.Static
import Vega.Error (Error, RenameError, TypeError)
import Vega.Syntax

import Data.HashTable.IO (CuckooHashTable)
import Data.HashTable.IO qualified as HashTable

-- TODO: this currently isn't thread safe

data DeclarationData = MkDeclarationData
    { parsed :: IORef (Declaration Parsed)
    , renamed :: IORef (GraphData RenameError (Declaration Renamed))
    , typed :: IORef (GraphData TypeError (Declaration Typed))
    , --
      dependencies :: IORef (HashSet GlobalName)
    , dependents :: IORef (HashSet GlobalName)
    }

type InMemory es =
    ( IOE :> es
    , Reader (CuckooHashTable GlobalName DeclarationData) :> es
    , Reader (IORef (HashMap FilePath (HashMap GlobalName (Declaration Parsed)))) :> es
    )

declarationData :: (HasCallStack, InMemory es) => GlobalName -> Eff es DeclarationData
declarationData name = do
    declarations <- ask @(CuckooHashTable _ _)
    liftIO (HashTable.lookup declarations name) >>= \case
        Just data_ -> pure data_
        Nothing -> error $ "Unknown declaration '" <> show name <> "'"

resetDependencies :: (InMemory es) => DeclarationData -> Eff es ()
resetDependencies data_ = do
    dependencies <- readIORef data_.dependencies
    dependents <- readIORef data_.dependents
    for_ dependencies \dependency -> do
        undefined

lastKnownDeclarations :: (InMemory es) => FilePath -> Eff es (Maybe (HashMap GlobalName (Declaration Parsed)))
lastKnownDeclarations filePath = do
    declarationsPerFile <- readIORef =<< ask @(IORef (HashMap _ _))
    pure $ lookup filePath declarationsPerFile

setKnownDeclarations :: (InMemory es) => FilePath -> HashMap GlobalName (Declaration Parsed) -> Eff es ()
setKnownDeclarations filePath declarations = do
    lastKnownDeclarationsPerFile <- ask @(IORef (HashMap _ _))
    modifyIORef' lastKnownDeclarationsPerFile (insert filePath declarations)

addDeclaration :: (InMemory es) => Declaration Parsed -> Eff es ()
addDeclaration declaration = do
    declarations <- ask @(CuckooHashTable _ _)

    parsed <- newIORef declaration
    renamed <- newIORef Missing
    typed <- newIORef Missing
    dependencies <- newIORef mempty
    dependents <- newIORef mempty
    let data_ = MkDeclarationData{parsed, renamed, typed, dependencies, dependents}
    liftIO $ HashTable.insert declarations declaration.name data_

getParsed :: (InMemory es) => GlobalName -> Eff es (Declaration Parsed)
getParsed name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.parsed

getRenamed :: (InMemory es) => GlobalName -> Eff es (GraphData RenameError (Declaration Renamed))
getRenamed name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.renamed

getTyped :: (InMemory es) => GlobalName -> Eff es (GraphData TypeError (Declaration Typed))
getTyped name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.typed

removeDeclaration :: (InMemory es) => GlobalName -> Eff es ()
removeDeclaration = undefined

invalidate :: (InMemory es) => GlobalName -> Eff es ()
invalidate = undefined

invalidateRenamed :: (InMemory es) => Maybe RenameError -> GlobalName -> Eff es ()
invalidateRenamed = undefined

invalidateTyped :: (InMemory es) => Maybe TypeError -> GlobalName -> Eff es ()
invalidateTyped = undefined

getDependencies :: (InMemory es) => GlobalName -> Eff es (HashSet GlobalName)
getDependencies name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.dependencies

getDependents :: (InMemory es) => GlobalName -> Eff es (HashSet GlobalName)
getDependents name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.dependents

addDependency :: (InMemory es) => GlobalName -> GlobalName -> Eff es ()
addDependency dependent dependency = do
    dependentData <- declarationData dependent
    dependencyData <- declarationData dependency
    modifyIORef' dependentData.dependencies (HashSet.insert dependent)
    modifyIORef' dependencyData.dependents (HashSet.insert dependency)

getGlobalType :: (InMemory es) => GlobalName -> Eff es (Maybe Type)
getGlobalType = undefined

getCurrentErrors :: (InMemory es) => Eff es (Seq Error)
getCurrentErrors = undefined

runInMemory :: forall a es. (IOE :> es) => Eff (GraphPersistence : es) a -> Eff es a
runInMemory action = do
    lastKnownDeclarationsPerFile :: IORef (HashMap FilePath (HashMap GlobalName (Declaration Parsed))) <- liftIO $ newIORef mempty

    declarations :: CuckooHashTable GlobalName DeclarationData <- liftIO HashTable.new

    action & interpret \_ ->
        runReader lastKnownDeclarationsPerFile . runReader declarations . \case
            LastKnownDeclarations filePath -> lastKnownDeclarations filePath
            SetKnownDeclarations filePath declarations -> setKnownDeclarations filePath declarations
            AddDeclaration declaration -> addDeclaration declaration
            GetParsed name -> getParsed name
            GetRenamed name -> getRenamed name
            GetTyped name -> getTyped name
            -- Invalidation
            RemoveDeclaration name -> removeDeclaration name
            Invalidate name -> invalidate name
            InvalidateRenamed maybeError name -> invalidateRenamed maybeError name
            InvalidateTyped maybeError name -> invalidateTyped maybeError name
            -- Dependencies
            GetDependencies name -> getDependencies name
            GetDependents name -> getDependents name
            AddDependency dependent dependency -> addDependency dependent dependency
            -- Specific accesses
            GetGlobalType name -> getGlobalType name
            GetCurrentErrors -> getCurrentErrors
