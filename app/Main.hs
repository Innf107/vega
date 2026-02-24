{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuasiQuotes #-}

module Main (main) where

import Relude hiding (Reader, runReader)

import Options.Applicative
import Vega.Driver qualified as Driver

import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Yaml (prettyPrintParseException)
import Effectful (Eff, IOE, runEff, (:>))
import Effectful.Concurrent (Concurrent, runConcurrent)
import Effectful.Dispatch.Dynamic (interpret_)
import Effectful.FileSystem (FileSystem, runFileSystem)
import Effectful.Process (Process, runProcess)
import Effectful.Reader.Static (Reader, runReader)
import GHC.Read (readsPrec)
import LLVM.Core qualified as LLVM
import System.IO (hIsTerminalDevice)
import System.OsPath (osp)
import Vega.BuildConfig (BuildConfigPresence (..), findBuildConfig)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Driver (CompilationResult (..))
import Vega.Effect.DebugEmit
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence.InMemory (runInMemory)
import Vega.Effect.Trace (Trace, runTrace)
import Vega.Error (ErrorMessage (..), PlainErrorMessage (..), prettyErrorWithLoc, renderCompilationError)
import Vega.Pretty (Ann, Doc, PrettyANSIIConfig (MkPrettyANSIIConfig, includeUnique), align, emphasis, eprintANSII, intercalateDoc, keyword, pretty, prettyPlain, (<+>))
import Vega.Util (constructorNames)

data PersistenceBackend
    = InMemory
    deriving (Generic, Show, Read)

data Options
    = Build
        { persistence :: PersistenceBackend
        , includeUnique :: Bool
        , debugEmitConfig :: DebugEmitConfig
        , verifyMIR :: Bool
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
data DebugEmitConfig = MkDebugEmitConfig
    { debugCore :: DebugEmitOption
    , debugMIR :: DebugEmitOption
    , debugLLVM :: DebugEmitOption
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
    debugMIR <-
        option
            auto
            ( long "debug-mir"
                <> value None
                <> help ("MIR output for debugging. Can be one of: file, stderr, none")
            )
    debugLLVM <-
        option
            auto
            (long "debug-llvm" <> value None <> help ("LLVM output for debugging. Can be one of: file, stderr, none"))
    verifyMIR <-
        flag
            False
            True
            (long "verify-mir" <> help ("Verify that the correctness intermediate MIR language is well-formed. This has a small performance cost and shouldn't be necessary unless the compiler has a bug."))

    pure Build{persistence, includeUnique, debugEmitConfig = MkDebugEmitConfig{debugCore, debugMIR, debugLLVM}, verifyMIR}

runCoreEmit :: (IOE :> es, ?config :: PrettyANSIIConfig) => DebugEmitConfig -> Eff (DebugEmit (Seq Core.Declaration) : es) a -> Eff es a
runCoreEmit config cont = case config.debugCore of
    None -> ignoreEmit cont
    ToFile -> do
        let render declarations = encodeUtf8 do
                prettyPlain (intercalateDoc "\n\n" (fmap pretty declarations))
        emitAllToFile render "core.vegacore" cont
    ToStderr -> emitToStderr (\declarations -> intercalateDoc "\n\n" (fmap pretty declarations)) cont

runMIREmit :: (IOE :> es, ?config :: PrettyANSIIConfig) => DebugEmitConfig -> Eff (DebugEmit (Seq MIR.Declaration) : es) a -> Eff es a
runMIREmit config cont = case config.debugMIR of
    None -> ignoreEmit cont
    ToFile -> do
        let render declarations = encodeUtf8 do
                prettyPlain (intercalateDoc "\n\n" (fmap pretty declarations))
        emitAllToFile render "mir.vegamir" cont
    ToStderr -> emitToStderr (\declarations -> intercalateDoc "\n\n" (fmap pretty declarations)) cont

runLLVMEmit :: (IOE :> es) => DebugEmitConfig -> Eff (DebugEmit LLVM.Module : es) a -> Eff es a
runLLVMEmit config cont = case config.debugLLVM of
    None -> ignoreEmit cont
    ToFile ->
        cont & interpret_ \case
            DebugEmit module_ -> do
                liftIO $ LLVM.printModuleToFile module_ [osp|llvm.ll|]
    ToStderr ->
        cont & interpret_ \case
            DebugEmit module_ ->
                liftIO $ LLVM.dumpModule module_

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
    Driver.DriverConfig ->
    DebugEmitConfig ->
    PersistenceBackend ->
    Eff
        '[ Reader Driver.DriverConfig
         , DebugEmit (Seq Core.Declaration)
         , DebugEmit (Seq MIR.Declaration)
         , DebugEmit LLVM.Module
         , Concurrent
         , Process
         , GraphPersistence
         , FileSystem
         , Trace
         , IOE
         ]
        a ->
    IO a
run driverConfig debugConfig persistence action = case persistence of
    InMemory ->
        action
            & runReader driverConfig
            & runCoreEmit debugConfig
            & runMIREmit debugConfig
            & runLLVMEmit debugConfig
            & runConcurrent
            & runProcess
            & runInMemory
            & runFileSystem
            & runTrace
            & runEff

main :: IO ()
main = do
    options <- execParser (info (parser <**> helper) fullDesc)
    let ?config =
            MkPrettyANSIIConfig
                { includeUnique = options.includeUnique
                }
    let driverConfig =
            Driver.MkDriverConfig
                { verifyMIR = options.verifyMIR
                }
    case options of
        Build{persistence, debugEmitConfig} -> run driverConfig debugEmitConfig persistence do
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
        Exec{file, mainFunction} -> run driverConfig MkDebugEmitConfig{debugCore = None, debugMIR = None, debugLLVM = None} InMemory do
            Driver.execute file mainFunction
