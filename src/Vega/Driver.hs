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
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Error qualified as Error
import Vega.Lexer qualified as Lexer
import Vega.Parser qualified as Parser
import Vega.Rename qualified as Rename
import Vega.Syntax
import Vega.Trace (Category (Driver), trace, traceEnabled)
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
    tokens <- case Lexer.run (toText filePath) contents of
            Left errors -> undefined
            Right tokens -> pure tokens
    parsedModule <- case Parser.parse (moduleNameForPath filePath) filePath tokens of
            Left errors -> do
                undefined
            Right parsedModule -> pure parsedModule

    previousDeclarations <- GraphPersistence.lastKnownDeclarations filePath
    case previousDeclarations of
        Nothing -> pure $ Diff.reportNewModule parsedModule
        Just previous -> Diff.diffDeclarations parsedModule.declarations previous

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
    diffChanges <- fold <$> forConcurrently sourceFiles parseAndDiff

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
    undefined

typecheck :: (Driver es) => GlobalName -> Eff es ()
typecheck name = undefined
