module Main (main) where

import Relude

import Options.Applicative
import Vega.Driver qualified as Driver

import Data.Text qualified as Text
import Effectful (Eff, IOE, runEff)
import Effectful.FileSystem (FileSystem, runFileSystem)
import Text.Read qualified as Read
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
        [ hsubparser
            $ command "build" (info buildOptions fullDesc)
        , hsubparser
            $ command "exec" (info execOptions fullDesc)
        ]

run :: PersistenceBackend -> Eff '[GraphPersistence, FileSystem, IOE] a -> IO a
run persistence action = case persistence of
    InMemory -> runEff $ runFileSystem $ runInMemory action

main :: IO ()
main = do
    options <- execParser (info (parser <**> helper) fullDesc)
    case options of
        Build{persistence} -> run persistence do
            Driver.trackNewModules
            Driver.rebuildTrackedModules
        Exec{file, mainFunction} -> run InMemory do
            Driver.execute file mainFunction
