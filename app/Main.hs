{-# LANGUAGE PartialTypeSignatures #-}

module Main (main) where

import Relude hiding (Reader, runReader)

import Options.Applicative
import Vega.Driver qualified as Driver

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Yaml (prettyPrintParseException)
import Effectful (Eff, IOE, runEff, (:>))
import Effectful.Concurrent (Concurrent, runConcurrent)
import Effectful.FileSystem (FileSystem, runFileSystem)
import Effectful.Reader.Static (runReader)
import GHC.Read (readsPrec)
import System.IO (hIsTerminalDevice)
import Vega.BuildConfig (BuildConfigPresence (..), findBuildConfig)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.LIR.Syntax qualified as LIR
import Vega.Driver (CompilationResult (..))
import Vega.Effect.DebugEmit
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence.InMemory (runInMemory)
import Vega.Effect.Trace (Trace, runTrace)
import Vega.Error (ErrorMessage (..), PlainErrorMessage (..), prettyErrorWithLoc, renderCompilationError)
import Vega.Pretty (Ann, Doc, PrettyANSIIConfig (MkPrettyANSIIConfig, includeUnique), align, emphasis, eprintANSII, intercalateDoc, keyword, pretty, prettyPlain, (<+>))
import Vega.Syntax (GlobalName)
import Vega.Util (constructorNames)

data PersistenceBackend
    = InMemory
    deriving (Generic, Show, Read)

data Options
    = Build
        { persistence :: PersistenceBackend
        , includeUnique :: Bool
        , debugEmitConfig :: DebugEmitConfig
        }
    | Exec
        { file :: FilePath
        , mainFunction :: Text
        }
    deriving (Generic)

data DebugEmitOption
    = ToFile
    | ToStderr
    | None
    deriving (Generic, Show)
instance Read DebugEmitOption where
    readsPrec _ = \case
        "file" -> [(ToFile, "")]
        "stderr" -> [(ToStderr, "")]
        "none" -> [(None, "")]
        _ -> []
data DebugEmitConfig = MkDebugEmitConfig {
    debugCore :: DebugEmitOption,
    debugLIR :: DebugEmitOption
}

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
        flag
            False
            True
            ( long "include-uniques"
                <> help
                    ("Show unique identifiers in diagnostics where applicable")
            )
    debugCore <-
        option
            auto
            ( long "debug-core"
                <> value None
                <> help ("Core output for debugging. Can be one of: file, stderr, none")
            )
    debugLIR <-
        option
            auto
            ( long "debug-lir"
                <> value None
                <> help ("LIR output for debugging. Can be one of: file, stderr, none")
            )
    pure Build{persistence, includeUnique, debugEmitConfig=MkDebugEmitConfig{ debugCore, debugLIR}}

runCoreEmit :: (IOE :> es, ?config :: PrettyANSIIConfig) => DebugEmitConfig -> Eff (DebugEmit (Seq Core.Declaration) : es) a -> Eff es a
runCoreEmit config cont = case config.debugCore of
    None -> ignoreEmit cont
    ToFile -> do
        let render declarations = encodeUtf8 do
                prettyPlain (intercalateDoc "\n\n" (fmap pretty declarations))
        emitAllToFile render "core.vegacore" cont
    ToStderr -> emitToStderr (\declarations -> intercalateDoc "\n\n" (fmap pretty declarations)) cont

runLIREmit :: (IOE :> es, ?config :: PrettyANSIIConfig) => DebugEmitConfig -> Eff (DebugEmit (Seq LIR.Declaration) : es) a -> Eff es a
runLIREmit config cont = case config.debugCore of
    None -> ignoreEmit cont
    ToFile -> do
        let render declarations = encodeUtf8 do
                prettyPlain (intercalateDoc "\n\n" (fmap pretty declarations))
        emitAllToFile render "lir.vegalir" cont
    ToStderr -> emitToStderr (\declarations -> intercalateDoc "\n\n" (fmap pretty declarations)) cont


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

run ::
    (?config :: PrettyANSIIConfig) =>
    DebugEmitConfig ->
    PersistenceBackend ->
    Eff
        '[ DebugEmit (Seq Core.Declaration)
         , DebugEmit (Seq LIR.Declaration)
         , Concurrent
         , GraphPersistence
         , FileSystem
         , Trace
         , IOE
         ]
        a ->
    IO a
run debugConfig persistence action = case persistence of
    InMemory -> runEff $ runTrace $ runFileSystem $ runInMemory $ runConcurrent $ runLIREmit debugConfig $ runCoreEmit debugConfig action

main :: IO ()
main = do
    options <- execParser (info (parser <**> helper) fullDesc)
    let ?config =
            MkPrettyANSIIConfig
                { includeUnique = options.includeUnique
                }
    case options of
        Build{persistence, debugEmitConfig} -> run debugEmitConfig persistence do
            let eprint :: forall io. (MonadIO io) => Doc Ann -> io ()
                eprint doc = do
                    liftIO (hIsTerminalDevice stderr) >>= \case
                        True -> do
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
                                let errorMessages = renderCompilationError error
                                for_ errorMessages \errorMessage -> do
                                    doc <- case errorMessage of
                                        ErrorWithLoc errorWithLoc -> prettyErrorWithLoc errorWithLoc
                                        PlainError plainError -> pure $ pretty plainError
                                    eprint doc
                            exitFailure
        Exec{file, mainFunction} -> run MkDebugEmitConfig{debugCore=None, debugLIR=None} InMemory do
            Driver.execute file mainFunction
