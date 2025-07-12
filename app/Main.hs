{-# LANGUAGE PartialTypeSignatures #-}

module Main (main) where

import Relude hiding (Reader, runReader)

import Options.Applicative
import Vega.Driver qualified as Driver

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Yaml (prettyPrintParseException)
import Effectful (Eff, IOE, runEff)
import Effectful.Concurrent (Concurrent, runConcurrent)
import Effectful.FileSystem (FileSystem, runFileSystem)
import Effectful.Reader.Static (runReader)
import System.IO (hIsTerminalDevice)
import Vega.BuildConfig (BuildConfigPresence (..), findBuildConfig)
import Vega.Driver (CompilationResult (..))
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence.InMemory (runInMemory)
import Vega.Effect.Trace (Trace, runTrace)
import Vega.Error (ErrorMessage (..), PlainErrorMessage (..), prettyErrorWithLoc, renderCompilationError)
import Vega.Pretty (Ann, Doc, PrettyANSIIConfig (MkPrettyANSIIConfig, includeUnique), align, emphasis, eprintANSII, keyword, pretty, prettyPlain, (<+>))
import Vega.Util (constructorNames)

data PersistenceBackend
    = InMemory
    deriving (Generic, Show, Read)

data Options
    = Build
        { persistence :: PersistenceBackend
        , includeUnique :: Bool
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
    includeUnique <-
        option
            auto
            ( long "include-uniques"
                <> value False
                <> showDefault
                <> help
                    ("Show unique identifiers in diagnostics where applicable")
            )
    pure Build{persistence, includeUnique}

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

run :: PersistenceBackend -> Eff '[Concurrent, GraphPersistence, FileSystem, Trace, IOE] a -> IO a
run persistence action = case persistence of
    InMemory -> runEff $ runTrace $ runFileSystem $ runInMemory $ runConcurrent $ action

main :: IO ()
main = do
    options <- execParser (info (parser <**> helper) fullDesc)
    case options of
        Build{persistence} -> run persistence do
            let eprint :: forall io. (MonadIO io) => Doc Ann -> io ()
                eprint doc =
                    liftIO (hIsTerminalDevice stderr) >>= \case
                        True -> do
                            let ?config =
                                    MkPrettyANSIIConfig
                                        { includeUnique = options.includeUnique
                                        }
                            eprintANSII doc
                        False -> liftIO (Text.hPutStrLn stderr (prettyPlain doc))

            findBuildConfig "." >>= \case
                Missing -> do
                    eprint $ pretty $ MkPlainErrorMessage $ emphasis "Missing" <+> keyword "vega.yaml" <+> emphasis "file"
                    exitFailure
                Invalid parseException -> do
                    -- TODO: format these yourself so they're actually human readable
                    eprint $
                        pretty $
                            MkPlainErrorMessage $
                                emphasis "Malformed" <+> keyword "vega.yaml" <+> emphasis "file:"
                                    <> "\n    "
                                    <> align (fromString (prettyPrintParseException parseException))
                    exitFailure
                Found config -> runReader config do
                    result <- Driver.rebuild
                    case result of
                        CompilationSuccessful -> pure ()
                        CompilationFailed errors -> do
                            for_ errors \error -> do
                                doc <- case renderCompilationError error of
                                    ErrorWithLoc errorWithLoc -> prettyErrorWithLoc errorWithLoc
                                    PlainError plainError -> pure $ pretty plainError
                                eprint doc
                                exitFailure
        Exec{file, mainFunction} -> run InMemory do
            Driver.execute file mainFunction
