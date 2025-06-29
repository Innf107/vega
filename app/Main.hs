module Main (main) where

import Relude hiding (Reader, runReader)

import Options.Applicative
import Vega.Driver qualified as Driver

import Control.Exception (throw)
import Data.Text qualified as Text
import Effectful (Eff, IOE, runEff)
import Effectful.Concurrent (Concurrent, runConcurrent)
import Effectful.FileSystem (FileSystem, runFileSystem)
import Effectful.Reader.Static (Reader, runReader)
import Text.Read qualified as Read
import Vega.BuildConfig (BuildConfig, BuildConfigPresence (..), findBuildConfig)
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence.InMemory (runInMemory)
import Vega.Util (constructorNames)

data PersistenceBackend
    = InMemory
    deriving (Generic, Show, Read)

data Options
    = Build
        { persistence :: PersistenceBackend
        }
    | Exec
        { file :: FilePath
        , mainFunction :: Text
        }
    deriving (Generic, Show)

buildOptions :: Parser Options
buildOptions = do
    persistence <-
        option
            auto
            ( long "persistence"
                <> metavar "MODE"
                <> value InMemory
                <> showDefault
                <> help
                    ( "Select the persistence backend to use. Can be one of: "
                        <> toString (Text.intercalate ", " (toList $ constructorNames @PersistenceBackend))
                    )
            )
    pure Build{persistence}

execOptions :: Parser Options
execOptions = do
    file <- argument str (metavar "FILE")
    mainFunction <- option str (long "main-function" <> value "main" <> showDefault <> help ("The function to run when executing the given file"))
    pure (Exec{file, mainFunction})

parser :: Parser Options
parser =
    asum @[]
        [ hsubparser $
            command "build" (info buildOptions fullDesc)
        , hsubparser $
            command "exec" (info execOptions fullDesc)
        ]

run :: PersistenceBackend -> Eff '[Concurrent, GraphPersistence, FileSystem, IOE] a -> IO a
run persistence action = case persistence of
    InMemory -> runEff $ runFileSystem $ runInMemory $ runConcurrent $ action

main :: IO ()
main = do
    options <- execParser (info (parser <**> helper) fullDesc)
    case options of
        Build{persistence} -> run persistence do
            findBuildConfig "." >>= \case
                Missing -> undefined
                Invalid err -> throw err -- TODO
                Found config -> runReader config do
                    result <- Driver.rebuild
                    undefined
        Exec{file, mainFunction} -> run InMemory do
            Driver.execute file mainFunction
