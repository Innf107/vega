{-# LANGUAGE PartialTypeSignatures #-}

module Vega.Effect.GraphPersistence.InMemory (runInMemory) where

import Relude hiding (Reader, Type, ask, runReader)
import Relude.Extra

import Data.HashSet qualified as HashSet

import Vega.Effect.GraphPersistence hiding (addDeclaration, addDependency, findMatchingNames, getCurrentErrors, getDependencies, getDependents, getErrors, getGlobalType, getModuleImportScope, getParsed, getRemainingWork, getRenamed, getTyped, invalidate, invalidateRenamed, invalidateTyped, lastKnownDeclarations, removeDeclaration, setKnownDeclarations, setModuleImportScope, setParsed, setRenamed, setTyped)

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

type DeclarationStore = CuckooHashTable GlobalName DeclarationData

type LastKnownDeclarations = IORef (HashMap FilePath (HashMap GlobalName (Declaration Parsed)))

type NameResolution = CuckooHashTable Text GlobalName

type ImportScopes = CuckooHashTable ModuleName ImportScope

type InMemory es =
    ( IOE :> es
    , Reader DeclarationStore :> es
    , Reader LastKnownDeclarations :> es
    , Reader NameResolution :> es
    , Reader ImportScopes :> es
    )

declarationData :: (HasCallStack, InMemory es) => GlobalName -> Eff es DeclarationData
declarationData name = do
    declarations <- ask @DeclarationStore
    liftIO (HashTable.lookup declarations name) >>= \case
        Just data_ -> pure data_
        Nothing -> error $ "Unknown declaration '" <> show name <> "'"

resetDependencies :: (InMemory es) => GlobalName -> Eff es ()
resetDependencies name = do
    data_ <- declarationData name
    dependencies <- readIORef data_.dependencies
    for_ dependencies \dependency -> do
        dependencyData <- declarationData dependency
        modifyIORef' dependencyData.dependents (HashSet.delete name)

invalidateDependents :: (InMemory es) => GlobalName -> Eff es ()
invalidateDependents name = do
    data_ <- declarationData name
    dependents <- readIORef data_.dependents
    for_ dependents \dependent -> do
        invalidate dependent

lastKnownDeclarations :: (InMemory es) => FilePath -> Eff es (Maybe (HashMap GlobalName (Declaration Parsed)))
lastKnownDeclarations filePath = do
    declarationsPerFile <- readIORef =<< ask @LastKnownDeclarations
    pure $ lookup filePath declarationsPerFile

setKnownDeclarations :: (InMemory es) => FilePath -> HashMap GlobalName (Declaration Parsed) -> Eff es ()
setKnownDeclarations filePath declarations = do
    lastKnownDeclarationsPerFile <- ask @LastKnownDeclarations
    modifyIORef' lastKnownDeclarationsPerFile (insert filePath declarations)

getModuleImportScope :: (InMemory es, HasCallStack) => ModuleName -> Eff es ImportScope
getModuleImportScope moduleName = do
    importScopes <- ask @ImportScopes
    liftIO (HashTable.lookup importScopes moduleName) >>= \case
        Nothing -> error $ "No import scope for module: " <> show moduleName
        Just importScope -> pure importScope

setModuleImportScope :: (InMemory es) => ModuleName -> ImportScope -> Eff es ()
setModuleImportScope moduleName scope = do
    importScopes <- ask @ImportScopes
    liftIO $ HashTable.insert importScopes moduleName scope

addDeclaration :: (InMemory es) => Declaration Parsed -> Eff es ()
addDeclaration declaration = do
    declarations <- ask @DeclarationStore

    parsed <- newIORef declaration
    renamed <- newIORef Missing
    typed <- newIORef Missing
    dependencies <- newIORef mempty
    dependents <- newIORef mempty
    let data_ = MkDeclarationData{parsed, renamed, typed, dependencies, dependents}
    liftIO $ HashTable.mutate declarations declaration.name \case
        Nothing -> (Just data_, ())
        Just _ -> error $ "Trying to add declaration as new that already exists: '" <> show declaration.name <> "'"

getParsed :: (InMemory es) => GlobalName -> Eff es (Declaration Parsed)
getParsed name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.parsed

setParsed :: (InMemory es) => Declaration Parsed -> Eff es ()
setParsed declaration = do
    invalidate declaration.name
    data_ <- declarationData declaration.name
    writeIORef data_.parsed declaration

getRenamed :: (InMemory es) => GlobalName -> Eff es (GraphData RenameError (Declaration Renamed))
getRenamed name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.renamed

setRenamed :: (InMemory es) => Declaration Renamed -> Eff es ()
setRenamed declaration = do
    invalidate declaration.name
    data_ <- declarationData declaration.name
    writeIORef data_.renamed (Ok declaration)

getTyped :: (InMemory es) => GlobalName -> Eff es (GraphData TypeError (Declaration Typed))
getTyped name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.typed

setTyped :: (InMemory es) => Declaration Typed -> Eff es ()
setTyped declaration = do
    invalidate declaration.name
    data_ <- declarationData declaration.name
    writeIORef data_.typed (Ok declaration)

removeDeclaration :: (InMemory es) => GlobalName -> Eff es ()
removeDeclaration name = do
    dependencies <- ask @DeclarationStore
    resetDependencies name
    invalidateDependents name
    liftIO $ HashTable.delete dependencies name

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
getGlobalType name = do
    undefined

findMatchingNames :: (InMemory es) => Text -> Eff es (Seq GlobalName)
findMatchingNames = do
    undefined

getErrors :: (InMemory es) => GlobalName -> Eff es (Seq Error)
getErrors name = undefined

getCurrentErrors :: (InMemory es) => Eff es (Seq Error)
getCurrentErrors = undefined

remainingWorkItems :: (InMemory es) => GlobalName -> DeclarationData -> Eff es (Seq WorkItem)
remainingWorkItems name data_ = do
    readIORef data_.renamed >>= \case
        Missing -> pure [Rename name]
        -- If compilation failed here, we can't do anything until something changes in the input (which will invalidate the renamed field)
        Failed _ -> pure []
        Ok _ -> do
            readIORef data_.typed >>= \case
                Missing -> pure [TypeCheck name]
                Failed _ -> pure []
                Ok _ -> pure []

getRemainingWork :: (InMemory es) => Eff es (Seq WorkItem)
getRemainingWork = do
    declarations <- liftIO . HashTable.toList =<< ask @DeclarationStore
    mconcat <$> traverse (\(name, data_) -> remainingWorkItems name data_) declarations

runInMemory :: forall a es. (IOE :> es) => Eff (GraphPersistence : es) a -> Eff es a
runInMemory action = do
    lastKnownDeclarationsPerFile :: LastKnownDeclarations <- liftIO $ newIORef mempty

    declarations :: DeclarationStore <- liftIO HashTable.new

    nameResolution :: NameResolution <- liftIO HashTable.new

    importScopes :: ImportScopes <- liftIO HashTable.new

    action & interpret \_ ->
        runReader lastKnownDeclarationsPerFile
            . runReader declarations
            . runReader nameResolution
            . runReader importScopes
            . \case
                LastKnownDeclarations filePath -> lastKnownDeclarations filePath
                SetKnownDeclarations filePath declarations -> setKnownDeclarations filePath declarations
                GetModuleImportScope moduleName -> getModuleImportScope moduleName
                SetModuleImportScope moduleName scope -> setModuleImportScope moduleName scope
                AddDeclaration declaration -> addDeclaration declaration
                GetParsed name -> getParsed name
                SetParsed name -> setParsed name
                GetRenamed name -> getRenamed name
                SetRenamed name -> setRenamed name
                GetTyped name -> getTyped name
                SetTyped name -> setTyped name
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
                FindMatchingNames name -> findMatchingNames name
                GetErrors name -> getErrors name
                -- Compilation
                GetCurrentErrors -> getCurrentErrors
                GetRemainingWork -> getRemainingWork
