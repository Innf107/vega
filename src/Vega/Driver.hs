module Vega.Driver (
    rebuild,
    execute,
) where

-- TODO: check that imports make sense somewhere
-- TODO: diff imports and invalidate all declarations if they did
-- TODO: check file modifications to avoid having to diff every module every time
-- TODO: remove modules if their files are deleted

import Relude hiding (Reader, ask, trace)

import Effectful
import Effectful.FileSystem (FileSystem, doesDirectoryExist, doesFileExist, listDirectory, withCurrentDirectory)
import Effectful.Reader.Static
import System.FilePath (takeExtension, (</>))

import Data.HashMap.Strict qualified as HashMap
import Data.Map qualified as Map
import Data.Text qualified as Text
import Data.Text.Lazy.Builder qualified as TextBuilder
import Data.Time (getCurrentTime)
import Data.Traversable (for)
import Effectful.Concurrent (Concurrent)
import Effectful.Concurrent.Async (forConcurrently)
import Effectful.Writer.Static.Local (runWriter)
import Vega.BuildConfig (BuildConfig (..))
import Vega.BuildConfig qualified as BuildConfig
import Vega.Compilation.JavaScript qualified as JavaScript
import Vega.Diff (DiffChange (..))
import Vega.Diff qualified as Diff
import Vega.Effect.GraphPersistence (GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Error qualified as Error
import Vega.Lexer qualified as Lexer
import Vega.Parser qualified as Parser
import Vega.Rename qualified as Rename
import Vega.Syntax
import Vega.Trace (Category (..), trace, traceEnabled)
import Vega.TypeCheck qualified as TypeCheck
import Vega.Util (viaList)
import Witherable (wither)

type Driver es = (Reader BuildConfig :> es, GraphPersistence :> es, IOE :> es, FileSystem :> es, Concurrent :> es)

findSourceFiles :: (Driver es) => Eff es (Seq FilePath)
findSourceFiles = do
    config <- ask @BuildConfig
    go (BuildConfig.sourceDirectory config)
  where
    go path = do
        files <- listDirectory path
        fold <$> for files \file -> do
            let filePath = path </> file
            doesDirectoryExist filePath >>= \case
                True -> go filePath
                False
                    | takeExtension file == ".vega" -> pure [filePath]
                    | otherwise -> pure []

computeImportScope :: Seq Import -> ImportScope
computeImportScope imports = foldMap importScope imports
  where
    importScope = \case
        ImportUnqualified{moduleName, importedDeclarations} -> do
            ImportScope
                { imports =
                    fromList
                        [
                            ( moduleName
                            , MkImportedItems
                                { qualifiedAliases = mempty
                                , unqualifiedItems = viaList importedDeclarations
                                }
                            )
                        ]
                }
        ImportQualified{moduleName, importedAs} -> do
            ImportScope
                { imports =
                    fromList
                        [
                            ( moduleName
                            , MkImportedItems
                                { qualifiedAliases = [importedAs]
                                , unqualifiedItems = mempty
                                }
                            )
                        ]
                }

parseAndDiff :: (Driver es) => FilePath -> Eff es (Seq DiffChange)
parseAndDiff filePath = do
    let moduleName = moduleNameForPath filePath

    contents <- decodeUtf8 <$> readFileBS filePath
    tokens <- case Lexer.run (toText filePath) contents of
        Left errors -> undefined
        Right tokens -> pure tokens
    parsedModule <- case Parser.parse moduleName filePath tokens of
        Left errors -> do
            undefined
        Right parsedModule -> pure parsedModule

    let importScope = computeImportScope parsedModule.imports
    previousDeclarations <- GraphPersistence.lastKnownDeclarations filePath
    GraphPersistence.setKnownDeclarations filePath (viaList (fmap (\decl -> (decl.name, decl)) parsedModule.declarations))
    case previousDeclarations of
        Nothing -> do
            GraphPersistence.setModuleImportScope moduleName importScope
            pure $ Diff.reportNewModule parsedModule
        Just previous -> do
            previousImportScope <- GraphPersistence.getModuleImportScope moduleName
            if importScope /= previousImportScope
                then do
                    GraphPersistence.setModuleImportScope moduleName importScope
                    -- If imports changed, we simply invalidate every declaration in the module
                    pure $ fmap (\decl -> Changed decl) parsedModule.declarations
                else
                    Diff.diffDeclarations parsedModule.declarations previous

-- TODO: figure out something more reasonable here
moduleNameForPath :: FilePath -> ModuleName
moduleNameForPath path = MkModuleName (toText path)

applyDiffChange :: (Driver es) => DiffChange -> Eff es ()
applyDiffChange = \case
    Added decl -> GraphPersistence.addDeclaration decl
    Changed decl ->
        GraphPersistence.setParsed decl
    Removed decl -> GraphPersistence.removeDeclaration decl

trackSourceChanges :: (Driver es) => Eff es ()
trackSourceChanges = do
    sourceFiles <- findSourceFiles
    diffChanges <- fold <$> for sourceFiles parseAndDiff

    when (traceEnabled Driver) do
        for_ diffChanges \case
            Diff.Added decl -> trace Driver ("Declaration added: " <> show decl.name)
            Diff.Removed decl -> trace Driver ("Declaration removed: " <> show decl.name)
            Diff.Changed decl -> trace Driver ("Declaration changed: " <> show decl.name)

    for_ diffChanges applyDiffChange

performAllRemainingWork :: (Driver es) => Eff es ()
performAllRemainingWork = do
    config <- ask @BuildConfig

    remainingWorkItems <- GraphPersistence.getRemainingWork (BuildConfig.backend config)
    for_ remainingWorkItems \workItem -> do
        trace WorkItems ("Processing work item: " <> show workItem)
        case workItem of 
            GraphPersistence.Rename name -> do
                rename name
            GraphPersistence.TypeCheck name -> do
                typecheck name
            GraphPersistence.CompileToJS name -> do
                compileToJS name

rebuild :: (Driver es) => Eff es ()
rebuild = do
    trackSourceChanges
    performAllRemainingWork
    compileBackend

compileBackend :: (Driver es) => Eff es ()
compileBackend = do
    -- TODO: select the backend, etc.
    config <- ask @BuildConfig

    -- TODO: check that the entry point has the correct type (`Unit -{IO}> Unit` probably?)
    GraphPersistence.doesDeclarationExist (BuildConfig.entryPoint config) >>= \case
        True -> pure ()
        False -> undefined -- TODO: error message

    case BuildConfig.backend config of
        BuildConfig.JavaScript -> do
            jsCode <- JavaScript.assembleFromEntryPoint (BuildConfig.entryPoint config)

            -- TODO: make this configurable and make the path absolute
            writeFileLBS (toString $ config.contents.name <> ".js") (encodeUtf8 (TextBuilder.toLazyText jsCode))
        _ -> undefined

execute :: FilePath -> Text -> Eff es ()
execute = undefined

getLastKnownRenamed :: (Driver es) => GlobalName -> Eff es (Maybe (Declaration Renamed))
getLastKnownRenamed name = do
    GraphPersistence.getRenamed name >>= \case
        Ok renamed -> pure $ Just renamed
        Missing{previous} -> pure previous
        Failed{previous} -> pure previous

typeChanged :: Declaration Renamed -> Declaration Renamed -> Bool
typeChanged old new = case old.syntax of
    DefineFunction{typeSignature = oldTypeSignature} -> case new.syntax of
        DefineFunction{typeSignature = newTypeSignature} -> Diff.diff oldTypeSignature newTypeSignature
        DefineVariantType{} -> undefined
    DefineVariantType{} -> undefined

rename :: (Driver es) => GlobalName -> Eff es ()
rename name = do
    previous <- getLastKnownRenamed name

    parsed <- GraphPersistence.getParsed name
    (renamed, dependencies) <- Rename.rename parsed
    trace Dependencies (show name <> " --> " <> show dependencies)

    GraphPersistence.setRenamed renamed
    for_ dependencies \dependency -> do
        GraphPersistence.addDependency name dependency

    case previous of
        Just previous
            | typeChanged previous renamed -> do
                dependents <- GraphPersistence.getDependents name
                for_ dependents (GraphPersistence.invalidateTyped Nothing)
        _ -> pure ()

typecheck :: (Driver es) => GlobalName -> Eff es ()
typecheck name = do
    renamed <-
        GraphPersistence.getRenamed name >>= \case
            Ok renamed -> pure renamed
            Missing{} -> error $ "missing renamed in typecheck (TODO: should this rename it then?)"
            Failed{} -> error $ "trying to typecheck previously errored declaration"

    typedOrErrors <- TypeCheck.checkDeclaration renamed
    case typedOrErrors of
        Left errors -> undefined
        Right typed -> do
            GraphPersistence.setTyped typed

compileToJS :: (Driver es) => GlobalName -> Eff es ()
compileToJS name = do
    typedDeclaration <-
        GraphPersistence.getTyped name >>= \case
            Ok typed -> pure typed
            Missing{} -> error $ "missing typed in compilation to JS"
            Failed{} -> error $ "trying to compile errored declaration"
    compiled <- JavaScript.compileDeclaration typedDeclaration
    GraphPersistence.setCompiledJS name compiled
