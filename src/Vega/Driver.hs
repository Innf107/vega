module Vega.Driver (
    trackNewModules,
    rebuildTrackedModules,
    rebuildOnlyFiles,
    execute,
) where

import Relude hiding (Driver, trace)

import Effectful
import Effectful.FileSystem (FileSystem, doesDirectoryExist, doesFileExist, listDirectory, withCurrentDirectory)
import System.FilePath (takeExtension, (</>))

import Data.HashMap.Strict qualified as HashMap
import Data.Map qualified as Map
import Data.Text qualified as Text
import Data.Time (getCurrentTime)
import Vega.Diff qualified as Diff
import Vega.Effect.GraphPersistence (GraphPersistence, addTrackedModule, getTrackedModules)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Error qualified as Error
import Vega.Lexer qualified as Lexer
import Vega.Parser qualified as Parser
import Vega.Syntax
import Vega.Trace (Category (Driver), trace)

registerModule :: (GraphPersistence :> es, FileSystem :> es, IOE :> es) => FilePath -> Eff es ()
registerModule module_ = do
    timestamp <- liftIO $ getCurrentTime
    addTrackedModule module_ timestamp

registerAllModulesInDirectory :: (GraphPersistence :> es, FileSystem :> es, IOE :> es) => FilePath -> Eff es ()
registerAllModulesInDirectory directory = do
    files <- listDirectory directory
    for_ files \file -> do
        let fullPath = directory </> file
        doesDirectoryExist fullPath >>= \case
            True -> registerAllModulesInDirectory fullPath
            False
                | takeExtension fullPath == ".vega" ->
                    registerModule fullPath
                | otherwise -> pure ()

-- | Find new modules that aren't yet tracked by the build system
trackNewModules :: (GraphPersistence :> es, FileSystem :> es, IOE :> es) => Eff es ()
trackNewModules = do
    registerAllModulesInDirectory "."

{- | Try to rebuild all files currently known to the build system.
This still only rebuilds files that actually changed since the last access.
-}
rebuildTrackedModules :: (GraphPersistence :> es, IOE :> es, FileSystem :> es) => Eff es ()
rebuildTrackedModules = do
    modules <- getTrackedModules
    rebuildOnlyFiles (fromList (Map.keys modules))

{- | Only try to rebuild some files.
This is useful for things like watch mode or LSP servers that already know
which files have changed.
-}
rebuildOnlyFiles :: (IOE :> es, FileSystem :> es, GraphPersistence :> es) => Seq FilePath -> Eff es ()
rebuildOnlyFiles files = do
    for_ files \filePath -> do
        doesFileExist filePath >>= \case
            False -> do
                trace Driver $ "File removed: " <> toText filePath
                undefined
            True -> do
                contents :: Text <- decodeUtf8 <$> readFileBS filePath

                trace Driver $ "Lexing '" <> toText filePath <> "'"
                tokens <- case Lexer.run (Text.pack filePath) contents of
                    Left lexError -> undefined
                    Right tokens -> pure tokens

                let moduleName = moduleNameForPath filePath

                trace Driver $ "Parsing '" <> toText filePath <> "'"
                parsedModule <- case Parser.parse moduleName filePath tokens of
                    Left parseErrors -> do
                        Error.printParseErrors parseErrors
                        undefined
                    Right parsedModule -> pure parsedModule

                GraphPersistence.lastKnownDeclarations filePath >>= \case
                    Nothing -> do
                        trace Driver $ "File added: " <> toText filePath
                        GraphPersistence.setKnownDeclarations filePath (fromList (map (\declaration -> (declaration.name, declaration)) (toList $ parsedModule.declarations)))
                        undefined
                    Just previous -> do
                        trace Driver $ "File modified: " <> toText filePath
                        diff <- Diff.diffDeclarations parsedModule.declarations previous
                        undefined

-- TODO
moduleNameForPath :: FilePath -> Text
moduleNameForPath = Text.pack

execute :: (IOE :> es, FileSystem :> es, GraphPersistence :> es) => FilePath -> Text -> Eff es ()
execute file mainFunction = undefined
