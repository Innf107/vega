module Vega.Driver (
    rebuild,
    execute,
) where

-- TODO: check that imports make sense somewhere
-- TODO: diff imports and invalidate all declarations if they did
-- TODO: check file modifications to avoid having to diff every module every time

import Relude hiding (Driver, Reader, ask, trace)

import Effectful
import Effectful.FileSystem (FileSystem, doesDirectoryExist, doesFileExist, listDirectory, withCurrentDirectory)
import Effectful.Reader.Static
import System.FilePath (takeExtension, (</>))

import Data.HashMap.Strict qualified as HashMap
import Data.Map qualified as Map
import Data.Text qualified as Text
import Data.Time (getCurrentTime)
import Data.Traversable (for)
import Effectful.Concurrent (Concurrent)
import Effectful.Concurrent.Async (forConcurrently)
import Vega.BuildConfig (BuildConfig (..))
import Vega.BuildConfig qualified as BuildConfig
import Vega.Diff (DiffChange (..))
import Vega.Diff qualified as Diff
import Vega.Effect.GraphPersistence (GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Error qualified as Error
import Vega.Lexer qualified as Lexer
import Vega.Parser qualified as Parser
import Vega.Rename qualified as Rename
import Vega.Syntax
import Vega.Trace (Category (Driver), trace, traceEnabled)
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

compileAllRemainingWork :: (Driver es) => Eff es ()
compileAllRemainingWork = do
    remainingWorkItems <- GraphPersistence.getRemainingWork
    for_ remainingWorkItems \case
        GraphPersistence.Rename name -> do
            rename name
            typecheck name
        GraphPersistence.TypeCheck name ->
            typecheck name

rebuild :: (Driver es) => Eff es ()
rebuild = do
    trackSourceChanges
    compileAllRemainingWork

execute :: FilePath -> Text -> Eff es ()
execute = undefined

rename :: (Driver es) => GlobalName -> Eff es ()
rename name = do
    parsed <- GraphPersistence.getParsed name
    (renamed, dependencies) <- Rename.rename parsed

    GraphPersistence.setRenamed renamed
    for_ dependencies \dependency -> do
        GraphPersistence.addDependency name dependency

typecheck :: (Driver es) => GlobalName -> Eff es ()
typecheck name = do
    renamed <-
        GraphPersistence.getRenamed name >>= \case
            Ok renamed -> pure renamed
            Missing -> error $ "missing renamed in typecheck (TODO: should this rename it then?)"
            Failed _ -> error $ "trying to typecheck previously errored declaration"

    typed <- TypeCheck.checkDeclaration renamed
    undefined
