module Vega.Driver (
    rebuild,
    execute,
) where

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
import Vega.BuildConfig (BuildConfig (..))
import Vega.Diff qualified as Diff
import Vega.Effect.GraphPersistence (GraphPersistence, addTrackedModule, getTrackedModules)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Error qualified as Error
import Vega.Lexer qualified as Lexer
import Vega.Parser qualified as Parser
import Vega.Syntax
import Vega.Trace (Category (Driver), trace)
import Witherable (wither)

type Driver es = (Reader BuildConfig :> es, GraphPersistence :> es, IOE :> es, FileSystem :> es)

findSourceFiles :: (Driver es) => Eff es (Seq FilePath)
findSourceFiles = do
    config <- ask @BuildConfig
    go config.sourceDirectory
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

rebuild :: (Driver es) => Eff es ()
rebuild = do
    sourceFiles <- findSourceFiles
    undefined

execute :: FilePath -> Text -> Eff es ()
execute = undefined
