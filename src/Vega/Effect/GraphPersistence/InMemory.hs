{-# LANGUAGE PartialTypeSignatures #-}

module Vega.Effect.GraphPersistence.InMemory (runInMemory) where

import Relude hiding (Reader, Type, ask, runReader)
import Relude.Extra

import Data.HashSet qualified as HashSet

import Vega.Effect.GraphPersistence hiding (
    addDeclaration,
    addDependency,
    cacheGlobalType,
    doesDeclarationExist,
    findMatchingNames,
    getCompiledJS,
    getCurrentErrors,
    getDependencies,
    getDependents,
    getErrors,
    getGlobalType,
    getModuleImportScope,
    getParsed,
    getRemainingWork,
    getRenamed,
    getTyped,
    invalidate,
    invalidateRenamed,
    invalidateTyped,
    lastKnownDeclarations,
    removeDeclaration,
    setCompiledJS,
    setKnownDeclarations,
    setModuleImportScope,
    setParsed,
    setRenamed,
    setTyped,
 )

import Effectful
import Effectful.Dispatch.Dynamic
import Effectful.Reader.Static
import Vega.Error (CompilationError, RenameError, TypeError, TypeErrorSet)
import Vega.Syntax

import Data.HashMap.Strict qualified as HashMap
import Data.HashTable.IO (CuckooHashTable)
import Data.HashTable.IO qualified as HashTable
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Vega.BuildConfig (Backend (JavaScript))

-- TODO: this currently isn't thread safe

data DeclarationData = MkDeclarationData
    { parsed :: IORef (Declaration Parsed)
    , renamed :: IORef (GraphData RenameError (Declaration Renamed))
    , typed :: IORef (GraphData TypeErrorSet (Declaration Typed))
    , compiledJS :: IORef (GraphData Void LText)
    , --
      dependencies :: IORef (HashSet GlobalName)
    , dependents :: IORef (HashSet GlobalName)
    , --
      cachedType :: IORef (Maybe Type)
    }

type DeclarationStore = CuckooHashTable GlobalName DeclarationData

type LastKnownDeclarations = IORef (HashMap FilePath (HashMap GlobalName (Declaration Parsed)))

type NameResolution = CuckooHashTable Text (HashMap GlobalName NameKind)

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

doesDeclarationExist :: (InMemory es) => GlobalName -> Eff es Bool
doesDeclarationExist name = do
    declarations <- ask @DeclarationStore
    liftIO (HashTable.lookup declarations name) >>= \case
        Just _ -> pure True
        Nothing -> pure False

addDeclaration :: (InMemory es) => Declaration Parsed -> Eff es ()
addDeclaration declaration = do
    declarations <- ask @DeclarationStore
    nameResolution <- ask @NameResolution

    parsed <- newIORef declaration
    renamed <- newIORef Missing{previous = Nothing}
    typed <- newIORef Missing{previous = Nothing}
    compiledJS <- newIORef Missing{previous = Nothing}
    dependencies <- newIORef mempty
    dependents <- newIORef mempty
    cachedType <- newIORef Nothing
    let data_ = MkDeclarationData{parsed, renamed, typed, compiledJS, dependencies, dependents, cachedType}
    liftIO $ HashTable.mutate declarations declaration.name \case
        Nothing -> (Just data_, ())
        Just _ -> error $ "Trying to add declaration as new that already exists: '" <> show declaration.name <> "'"

    -- TODO: yeah no this totally doesn't work for anything other than variables oops

    liftIO $ HashTable.mutate nameResolution declaration.name.name \case
        Nothing -> (Just [(declaration.name, definedDeclarationKind declaration.syntax)], ())
        Just entries -> (Just (insert declaration.name (definedDeclarationKind declaration.syntax) entries), ())

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

getTyped :: (InMemory es) => GlobalName -> Eff es (GraphData TypeErrorSet (Declaration Typed))
getTyped name = do
    data_ <- declarationData name
    readIORef data_.typed

setTyped :: (InMemory es) => Declaration Typed -> Eff es ()
setTyped declaration = do
    invalidateTyped Nothing declaration.name
    data_ <- declarationData declaration.name
    writeIORef data_.typed (Ok declaration)

getCompiledJS :: (InMemory es) => GlobalName -> Eff es (GraphData Void LText)
getCompiledJS name = do
    data_ <- declarationData name
    readIORef data_.compiledJS

setCompiledJS :: (InMemory es) => GlobalName -> LText -> Eff es ()
setCompiledJS name js = do
    data_ <- declarationData name
    writeIORef data_.compiledJS (Ok js)

removeDeclaration :: (InMemory es) => GlobalName -> Eff es ()
removeDeclaration name = do
    dependencies <- ask @DeclarationStore
    nameResolution <- ask @NameResolution
    resetDependencies name
    invalidateDependents name
    liftIO $ HashTable.delete dependencies name
    liftIO $ HashTable.mutate nameResolution name.name \case
        Nothing -> error $ "removing declaration with a name that was never tracked: " <> show name
        Just entries -> do
            let remaining = HashMap.delete name entries
            if null remaining
                then
                    (Nothing, ())
                else (Just remaining, ())

invalidateGraphData :: GraphData error a -> GraphData error a
invalidateGraphData = \case
    Ok a -> Missing{previous = Just a}
    Missing{previous} -> Missing{previous}
    Failed{previous, error = _} -> Missing{previous}

failGraphData :: error -> GraphData error a -> GraphData error a
failGraphData error = \case
    Ok a -> Failed{error, previous = Just a}
    Missing{previous} -> Failed{error, previous}
    Failed{previous, error = _} -> Failed{error, previous}

invalidate :: (InMemory es) => GlobalName -> Eff es ()
invalidate name = do
    data_ <- declarationData name
    resetDependencies name

    modifyIORef' data_.renamed invalidateGraphData
    invalidateTyped Nothing name

invalidateRenamed :: (InMemory es) => Maybe RenameError -> GlobalName -> Eff es ()
invalidateRenamed = undefined

invalidateTyped :: (InMemory es) => Maybe TypeErrorSet -> GlobalName -> Eff es ()
invalidateTyped maybeError name = do
    let invalidate = case maybeError of
            Nothing -> invalidateGraphData
            Just error -> failGraphData error

    data_ <- declarationData name
    modifyIORef' data_.typed invalidate
    writeIORef data_.cachedType Nothing

    modifyIORef' data_.compiledJS invalidateGraphData

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
    modifyIORef' dependentData.dependencies (HashSet.insert dependency)
    modifyIORef' dependencyData.dependents (HashSet.insert dependent)

getGlobalType :: (HasCallStack, InMemory es) => GlobalName -> Eff es (Either Type (TypeSyntax Renamed))
getGlobalType name = do
    data_ <- declarationData name
    readIORef data_.cachedType >>= \case
        Just type_ -> pure (Left type_)
        Nothing ->
            readIORef data_.renamed >>= \case
                Ok renamed -> case renamed.syntax of
                    DefineFunction{typeSignature} -> pure (Right typeSignature)
                    _ -> error $ "trying to access type of non-function declaration: " <> show name
                _ -> error $ "trying to access type of non-renamed declaration: " <> show name

cacheGlobalType :: (InMemory es) => GlobalName -> Type -> Eff es ()
cacheGlobalType name type_ = do
    data_ <- declarationData name
    writeIORef (data_.cachedType) (Just type_)

findMatchingNames :: (InMemory es) => Text -> Eff es (HashMap GlobalName NameKind)
findMatchingNames text = do
    nameResolution <- ask @NameResolution

    liftIO (HashTable.lookup nameResolution text) >>= \case
        Just candidates -> pure candidates
        Nothing -> mempty

getErrors :: (InMemory es) => GlobalName -> Eff es (Seq CompilationError)
getErrors name = undefined

getCurrentErrors :: (InMemory es) => Eff es (Seq CompilationError)
getCurrentErrors = undefined

remainingWorkItems :: (InMemory es) => Backend -> GlobalName -> DeclarationData -> Eff es (Seq WorkItem)
remainingWorkItems backend name data_ = do
    -- TODO: ughhhh i hope this gets better once we switch to the work queue API
    let remainingCompilation = case backend of
            JavaScript -> [CompileToJS name]
            _ -> []
    readIORef data_.renamed >>= \case
        Missing{} -> pure $ [Rename name, TypeCheck name] <> remainingCompilation
        -- If compilation failed here, we can't do anything until something changes in the input (which will invalidate the renamed field)
        Failed{} -> pure []
        Ok _ -> do
            readIORef data_.typed >>= \case
                Missing{} -> pure $ [TypeCheck name] <> remainingCompilation
                Failed{} -> pure []
                Ok _ -> do
                    case backend of
                        JavaScript -> do
                            readIORef data_.compiledJS >>= \case
                                Missing{} -> pure [CompileToJS name]
                                Ok{} -> pure []
                        _ -> undefined

getRemainingWork :: (InMemory es) => Backend -> Eff es (Seq WorkItem)
getRemainingWork backend = do
    declarations <- liftIO . HashTable.toList =<< ask @DeclarationStore
    remainingWork <-
        mconcat <$> for declarations \(name, data_) -> do
            remainingWorkItems backend name data_
    pure (Seq.sortOn rankWorkItem remainingWork)
  where
    rankWorkItem :: WorkItem -> Int
    rankWorkItem = \case
        Rename{} -> 0
        TypeCheck{} -> 1
        CompileToJS{} -> 2

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
                DoesDeclarationExist name -> doesDeclarationExist name
                AddDeclaration declaration -> addDeclaration declaration
                GetParsed name -> getParsed name
                SetParsed name -> setParsed name
                GetRenamed name -> getRenamed name
                SetRenamed name -> setRenamed name
                GetTyped name -> getTyped name
                SetTyped name -> setTyped name
                GetCompiledJS name -> getCompiledJS name
                SetCompiledJS name js -> setCompiledJS name js
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
                CacheGlobalType name type_ -> cacheGlobalType name type_
                FindMatchingNames name -> findMatchingNames name
                GetErrors name -> getErrors name
                -- Compilation
                GetCurrentErrors -> getCurrentErrors
                GetRemainingWork backend -> getRemainingWork backend
