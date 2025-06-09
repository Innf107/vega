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
import Effectful.Concurrent (Concurrent)
import Effectful.Concurrent.Async (forConcurrently)
import Vega.BuildConfig (BuildConfig (..))
import Vega.BuildConfig qualified as BuildConfig
import Vega.Diff (DiffChange)
import Vega.Diff qualified as Diff
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Error qualified as Error
import Vega.Lexer qualified as Lexer
import Vega.Parser qualified as Parser
import Vega.Syntax
import Vega.Trace (Category (Driver), trace)
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

parseAndDiff :: (Driver es) => FilePath -> Eff es (Seq DiffChange)
parseAndDiff filePath = do
    contents <- decodeUtf8 <$> readFileBS filePath
    let tokens = case Lexer.run (toText filePath) contents of
            Left errors -> undefined
            Right tokens -> tokens
    let parsedModule = case Parser.parse (moduleNameForPath filePath) filePath tokens of
            Left errors -> undefined
            Right parsedModule -> parsedModule

    previousDeclarations <- GraphPersistence.lastKnownDeclarations filePath
    case previousDeclarations of
        Nothing -> pure $ Diff.reportNewModule parsedModule
        Just previous -> Diff.diffDeclarations parsedModule.declarations previous

-- TODO: figure out something more reasonable here
moduleNameForPath :: FilePath -> Text
moduleNameForPath path = toText path

rebuild :: (Driver es) => Eff es ()
rebuild = do
    sourceFiles <- findSourceFiles
    diffChanges <- fold <$> forConcurrently sourceFiles parseAndDiff
    undefined

execute :: FilePath -> Text -> Eff es ()
execute = undefined
