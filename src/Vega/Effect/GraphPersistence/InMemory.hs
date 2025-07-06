{-# LANGUAGE PartialTypeSignatures #-}

module Vega.Effect.GraphPersistence.InMemory (runInMemory) where

import Relude hiding (Reader, Type, ask, runReader)
import Relude.Extra

import Data.HashSet qualified as HashSet

import Vega.Effect.GraphPersistence hiding (
    addDeclaration,
    addDependency,
    cacheGlobalKind,
    cacheGlobalType,
    doesDeclarationExist,
    findMatchingNames,
    getCompiledJS,
    getCurrentErrors,
    getDefiningDeclaration,
    getDependencies,
    getDependents,
    getErrors,
    getGlobalKind,
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
import Vega.Error (CompilationError (..), RenameError, RenameErrorSet (..), TypeError, TypeErrorSet (..))
import Vega.Syntax

import Data.HashMap.Strict qualified as HashMap
import Data.HashTable.IO (CuckooHashTable)
import Data.HashTable.IO qualified as HashTable
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Effectful.Concurrent.Async (forConcurrently, runConcurrent)
import Vega.BuildConfig (Backend (JavaScript))

-- TODO: this currently isn't thread safe

data DeclarationData = MkDeclarationData
    { parsed :: IORef (Declaration Parsed)
    , renamed :: IORef (GraphData RenameErrorSet (Declaration Renamed))
    , typed :: IORef (GraphData TypeErrorSet (Declaration Typed))
    , compiledJS :: IORef (GraphData Void LText)
    , --
      dependencies :: IORef (HashSet DeclarationName)
    , dependents :: IORef (HashSet DeclarationName)
    }

type CachedTypes = CuckooHashTable GlobalName Type
type CachedKinds = CuckooHashTable GlobalName Kind

type DeclarationStore = CuckooHashTable DeclarationName DeclarationData

type LastKnownDeclarations = IORef (HashMap FilePath (HashMap DeclarationName (Declaration Parsed)))

type NameResolution = CuckooHashTable Text (HashMap GlobalName NameKind)

type ImportScopes = CuckooHashTable ModuleName ImportScope

type DefiningDeclarations = CuckooHashTable GlobalName DeclarationName

type InMemory es =
    ( IOE :> es
    , Reader DeclarationStore :> es
    , Reader LastKnownDeclarations :> es
    , Reader NameResolution :> es
    , Reader ImportScopes :> es
    , Reader CachedTypes :> es
    , Reader CachedKinds :> es
    , Reader DefiningDeclarations :> es
    )

declarationData :: (HasCallStack, InMemory es) => DeclarationName -> Eff es DeclarationData
declarationData name = do
    declarations <- ask @DeclarationStore
    liftIO (HashTable.lookup declarations name) >>= \case
        Just data_ -> pure data_
        Nothing -> error $ "Unknown declaration '" <> show name <> "'"

resetDependencies :: (InMemory es) => DeclarationName -> Eff es ()
resetDependencies name = do
    data_ <- declarationData name
    dependencies <- readIORef data_.dependencies
    for_ dependencies \dependency -> do
        dependencyData <- declarationData dependency
        modifyIORef' dependencyData.dependents (HashSet.delete name)

invalidateDependents :: (InMemory es) => DeclarationName -> Eff es ()
invalidateDependents name = do
    data_ <- declarationData name
    dependents <- readIORef data_.dependents
    for_ dependents \dependent -> do
        invalidate dependent

lastKnownDeclarations :: (InMemory es) => FilePath -> Eff es (Maybe (HashMap DeclarationName (Declaration Parsed)))
lastKnownDeclarations filePath = do
    declarationsPerFile <- readIORef =<< ask @LastKnownDeclarations
    pure $ lookup filePath declarationsPerFile

setKnownDeclarations :: (InMemory es) => FilePath -> HashMap DeclarationName (Declaration Parsed) -> Eff es ()
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

doesDeclarationExist :: (InMemory es) => DeclarationName -> Eff es Bool
doesDeclarationExist name = do
    declarations <- ask @DeclarationStore
    liftIO (HashTable.lookup declarations name) >>= \case
        Just _ -> pure True
        Nothing -> pure False

addDeclaration :: (InMemory es) => Declaration Parsed -> Eff es ()
addDeclaration declaration = do
    declarations <- ask @DeclarationStore

    parsed <- newIORef declaration
    renamed <- newIORef Missing{previous = Nothing}
    typed <- newIORef Missing{previous = Nothing}
    compiledJS <- newIORef Missing{previous = Nothing}
    dependencies <- newIORef mempty
    dependents <- newIORef mempty
    let data_ = MkDeclarationData{parsed, renamed, typed, compiledJS, dependencies, dependents}
    liftIO $ HashTable.mutate declarations declaration.name \case
        Nothing -> (Just data_, ())
        Just _ -> error $ "Trying to add declaration as new that already exists: '" <> show declaration.name <> "'"

    let globals = definedGlobals declaration.syntax

    for_ globals \(name, kind) -> do
        addNameResolutionAssociation name kind
        setDefiningDeclaration name declaration.name

getParsed :: (InMemory es) => DeclarationName -> Eff es (Declaration Parsed)
getParsed name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.parsed

setParsed :: (InMemory es) => Declaration Parsed -> Eff es ()
setParsed declaration = do
    invalidate declaration.name
    data_ <- declarationData declaration.name
    writeIORef data_.parsed declaration

    for_ (definedGlobals declaration.syntax) \(global, kind) -> do
        addNameResolutionAssociation global kind
        setDefiningDeclaration global declaration.name

getRenamed :: (InMemory es) => DeclarationName -> Eff es (GraphData RenameErrorSet (Declaration Renamed))
getRenamed name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.renamed

setRenamed :: (InMemory es) => Declaration Renamed -> Eff es ()
setRenamed declaration = do
    invalidate declaration.name
    data_ <- declarationData declaration.name
    writeIORef data_.renamed (Ok declaration)

getTyped :: (InMemory es) => DeclarationName -> Eff es (GraphData TypeErrorSet (Declaration Typed))
getTyped name = do
    data_ <- declarationData name
    readIORef data_.typed

setTyped :: (InMemory es) => Declaration Typed -> Eff es ()
setTyped declaration = do
    invalidateTyped Nothing declaration.name
    data_ <- declarationData declaration.name
    writeIORef data_.typed (Ok declaration)

getCompiledJS :: (InMemory es) => DeclarationName -> Eff es (GraphData Void LText)
getCompiledJS name = do
    data_ <- declarationData name
    readIORef data_.compiledJS

setCompiledJS :: (InMemory es) => DeclarationName -> LText -> Eff es ()
setCompiledJS name js = do
    data_ <- declarationData name
    writeIORef data_.compiledJS (Ok js)

removeDeclaration :: (InMemory es) => DeclarationName -> Eff es ()
removeDeclaration name = do
    dependencies <- ask @DeclarationStore
    resetDependencies name
    invalidateDependents name
    liftIO $ HashTable.delete dependencies name

    globals <- getDefinedGlobals name
    for_ globals \(name, _) -> removeNameResolutionAssociation name

getDefinedGlobals :: (InMemory es) => DeclarationName -> Eff es (Seq (GlobalName, NameKind))
getDefinedGlobals name = do
    data_ <- declarationData name

    -- Since all global names are known after parsing, we can just look at the parsed declaration here
    declaration <- readIORef data_.parsed
    pure (definedGlobals declaration.syntax)

addNameResolutionAssociation :: (HasCallStack, InMemory es) => GlobalName -> NameKind -> Eff es ()
addNameResolutionAssociation name kind = do
    nameResolution <- ask @NameResolution

    liftIO $ HashTable.mutate nameResolution name.name \case
        Nothing -> (Just [(name, kind)], ())
        Just entries -> (Just (insert name kind entries), ())

removeNameResolutionAssociation :: (HasCallStack, InMemory es) => GlobalName -> Eff es ()
removeNameResolutionAssociation name = do
    nameResolution <- ask @NameResolution
    liftIO $ HashTable.mutate nameResolution name.name \case
        Nothing -> error $ "removing name association that was never tracked: " <> show name
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

invalidate :: (InMemory es) => DeclarationName -> Eff es ()
invalidate name = do
    data_ <- declarationData name
    resetDependencies name

    modifyIORef' data_.renamed invalidateGraphData
    invalidateTyped Nothing name

invalidateRenamed :: (InMemory es, HasCallStack) => Maybe RenameErrorSet -> DeclarationName -> Eff es ()
invalidateRenamed maybeError name = do
    let invalidate = case maybeError of
            Nothing -> invalidateGraphData
            Just error -> failGraphData error

    data_ <- declarationData name
    modifyIORef' data_.renamed invalidate
    resetDependencies name
    invalidateTyped Nothing name

invalidateTyped :: (InMemory es) => Maybe TypeErrorSet -> DeclarationName -> Eff es ()
invalidateTyped maybeError name = do
    let invalidate = case maybeError of
            Nothing -> invalidateGraphData
            Just error -> failGraphData error

    data_ <- declarationData name
    modifyIORef' data_.typed invalidate
    modifyIORef' data_.compiledJS invalidateGraphData

    cachedTypes <- ask @CachedTypes
    globals <- getDefinedGlobals name
    for_ globals \(name, _) ->
        liftIO (HashTable.delete cachedTypes name)

getDependencies :: (InMemory es) => DeclarationName -> Eff es (HashSet DeclarationName)
getDependencies name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.dependencies

getDependents :: (InMemory es) => DeclarationName -> Eff es (HashSet DeclarationName)
getDependents name = do
    data_ <- declarationData name
    liftIO $ readIORef data_.dependents

addDependency :: (InMemory es) => DeclarationName -> DeclarationName -> Eff es ()
addDependency dependent dependency = do
    dependentData <- declarationData dependent
    dependencyData <- declarationData dependency
    modifyIORef' dependentData.dependencies (HashSet.insert dependency)
    modifyIORef' dependencyData.dependents (HashSet.insert dependent)

getGlobalType :: (HasCallStack, InMemory es) => GlobalName -> Eff es (Either Type (TypeSyntax Renamed))
getGlobalType name = do
    cachedTypes <- ask @CachedTypes

    liftIO (HashTable.lookup cachedTypes name) >>= \case
        Just type_ -> pure (Left type_)
        Nothing -> do
            declarationName <-
                getDefiningDeclaration name >>= \case
                    Just declarationName -> pure declarationName
                    Nothing -> error $ "trying to access undefined declaration of global " <> show name
            data_ <- declarationData declarationName
            renamed <-
                readIORef data_.renamed >>= \case
                    Missing{} -> error $ "trying to access type of a global that has not been renamed: " <> show name
                    -- TODO: this might not actually be impossible?
                    Failed{} -> error $ "trying to access type of a global where renaming failed"
                    Ok renamed -> pure renamed

            pure (Right (typeOfGlobal name renamed.syntax))

cacheGlobalType :: (InMemory es) => GlobalName -> Type -> Eff es ()
cacheGlobalType name type_ = do
    cachedTypes <- ask @CachedTypes
    liftIO $ HashTable.insert cachedTypes name type_

getGlobalKind :: (HasCallStack, InMemory es) => GlobalName -> Eff es (Either Kind (KindSyntax Renamed))
getGlobalKind name = do
    cachedKinds <- ask @CachedKinds
    liftIO (HashTable.lookup cachedKinds name) >>= \case
        Just kind -> pure (Left kind)
        Nothing -> do
            declarationName <-
                getDefiningDeclaration name >>= \case
                    Just declarationName -> pure declarationName
                    Nothing -> error $ "trying to access undefined declaration of global " <> show name
            data_ <- declarationData declarationName
            renamed <-
                readIORef data_.renamed >>= \case
                    Missing{} -> error $ "trying to access kind of a global that has not been renamed: " <> show name
                    -- TODO: this might not actually be impossible?
                    Failed{} -> error $ "trying to access kind of a global where renaming failed"
                    Ok renamed -> pure renamed

            pure (Right (kindOfGlobal renamed))

cacheGlobalKind :: (InMemory es) => GlobalName -> Kind -> Eff es ()
cacheGlobalKind name kind = do
    cachedKinds <- ask @CachedKinds
    liftIO $ HashTable.insert cachedKinds name kind

findMatchingNames :: (InMemory es) => Text -> Eff es (HashMap GlobalName NameKind)
findMatchingNames text = do
    nameResolution <- ask @NameResolution

    liftIO (HashTable.lookup nameResolution text) >>= \case
        Just candidates -> pure candidates
        Nothing -> mempty

getErrors :: (InMemory es) => DeclarationName -> Eff es (Seq CompilationError)
getErrors name = do
    data_ <- declarationData name
    getErrorsFromData data_

getErrorsFromData :: forall es. (InMemory es) => DeclarationData -> Eff es (Seq CompilationError)
getErrorsFromData data_ = do
    let getError :: (err -> Seq CompilationError) -> IORef (GraphData err a) -> Eff es (Seq CompilationError)
        getError toCompilationErrors ioRef =
            readIORef ioRef >>= \case
                Ok _ -> pure []
                Missing{} -> pure []
                Failed{error} -> pure (toCompilationErrors error)

    fold @Seq
        <$> sequence
            [ getError (fmap RenameError . coerce) data_.renamed
            , getError (fmap TypeError . coerce) data_.typed
            , -- This is technically unreachable, but if that ever changes, this makes sure we update the error code here
              getError absurd data_.compiledJS
            ]

getCurrentErrors :: (InMemory es) => Eff es (Seq CompilationError)
getCurrentErrors = runConcurrent do
    declarations <- liftIO . HashTable.toList =<< ask @DeclarationStore
    -- This should be safe to do concurrently since even though declaration data isn't synchronized (yet),
    -- we never alias any references between declaration data entries.
    -- Let's hope I won't regret this (again)
    fold <$> forConcurrently declarations \(_, data_) -> do
        getErrorsFromData data_

remainingWorkItems :: (InMemory es) => Backend -> DeclarationName -> DeclarationData -> Eff es (Seq WorkItem)
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

getDefiningDeclaration :: (InMemory es) => GlobalName -> Eff es (Maybe DeclarationName)
getDefiningDeclaration name = do
    definingDeclarations <- ask @DefiningDeclarations
    liftIO $ HashTable.lookup definingDeclarations name

setDefiningDeclaration :: (InMemory es) => GlobalName -> DeclarationName -> Eff es ()
setDefiningDeclaration global declaration = do
    definingDeclarations <- ask @DefiningDeclarations
    liftIO $ HashTable.insert definingDeclarations global declaration

runInMemory :: forall a es. (IOE :> es) => Eff (GraphPersistence : es) a -> Eff es a
runInMemory action = do
    lastKnownDeclarationsPerFile :: LastKnownDeclarations <- liftIO $ newIORef mempty

    declarations :: DeclarationStore <- liftIO HashTable.new

    nameResolution :: NameResolution <- liftIO HashTable.new

    importScopes :: ImportScopes <- liftIO HashTable.new

    cachedTypes :: CachedTypes <- liftIO HashTable.new

    cachedKinds :: CachedKinds <- liftIO HashTable.new

    definingDeclarations :: DefiningDeclarations <- liftIO HashTable.new

    action & interpret \_ ->
        runReader lastKnownDeclarationsPerFile
            . runReader declarations
            . runReader nameResolution
            . runReader importScopes
            . runReader cachedTypes
            . runReader cachedKinds
            . runReader definingDeclarations
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
                GetGlobalKind name -> getGlobalKind name
                CacheGlobalKind name kind -> cacheGlobalKind name kind
                FindMatchingNames name -> findMatchingNames name
                GetErrors name -> getErrors name
                -- Compilation
                GetCurrentErrors -> getCurrentErrors
                GetRemainingWork backend -> getRemainingWork backend
                --
                GetDefiningDeclaration name -> getDefiningDeclaration name
