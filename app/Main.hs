{-# LANGUAGE ApplicativeDo #-}
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
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.LLVM.MIRToLLVM qualified as MIRToLLVM
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Driver (CompilationResult (..), Monomorphized (..))
import Vega.Effect.DebugEmit (DebugEmit)
import Vega.Effect.DebugEmit qualified as DebugEmit
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence.InMemory (runInMemory)
import Vega.Effect.Trace (Trace, runTrace)
import Vega.Error (ErrorMessage (..), PlainErrorMessage (..), prettyErrorWithLoc, renderCompilationError)
import Vega.Package (PackageConfigPresence (..))
import Vega.Package qualified as Package
import Vega.Pretty (Ann, Doc, PrettyANSIIConfig (MkPrettyANSIIConfig, includeUnique), align, emphasis, eprintANSII, intercalateDoc, keyword, pretty, prettyPlain, (<+>))
import Vega.Util (constructorNames)

data PersistenceBackend
    = InMemory
    deriving (Generic, Show, Read)

data Options
    = Build
        { optimizationLevel :: Driver.OptimizationLevel
        , persistence :: PersistenceBackend
        , linker :: Text
        , includeUnique :: Bool
        , debugEmitConfig :: DebugEmit.EmitConfig
        , verifyMIR :: Bool
        , useCCallingConvention :: Bool
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

showOptimizationLevel :: Driver.OptimizationLevel -> String
showOptimizationLevel = \case
    Driver.O0 -> "0"
    Driver.O1 -> "1"
    Driver.O2 -> "2"
    Driver.O3 -> "3"

parseOptimizationLevel :: ReadM Driver.OptimizationLevel
parseOptimizationLevel = maybeReader \case
    "0" -> Just Driver.O0
    "1" -> Just Driver.O1
    "2" -> Just Driver.O2
    "3" -> Just Driver.O3
    _ -> Nothing

buildOptions :: Parser Options
buildOptions = do
    optimizationLevel <- option parseOptimizationLevel (long "optimization-level" <> short 'O' <> metavar "LEVEL" <> value Driver.O0 
        <> showDefaultWith showOptimizationLevel <> help ("The overall optimization level used by Vega and LLVM. Can be one of 0, 1, 2, 3"))
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
    linker <- option auto (long "linker" <> metavar "PATH" <> value "auto" <> showDefault <> help "The executable to use for linking. This should be a C compiler or similar that already links in system libraries. Setting it to 'auto' will automatically use clang or gcc from the PATH if available.")
    includeUnique <-
        flag
            False
            True
            ( long "include-uniques"
                <> help
                    ("Show unique identifiers in diagnostics where applicable")
            )
    debugEmitConfig <- parseDebugEmitConfig
    verifyMIR <-
        flag
            False
            True
            (long "verify-mir" <> help ("Verify that the correctness intermediate MIR language is well-formed. This has a small performance cost and shouldn't be necessary unless the compiler has a bug."))
    useCCallingConvention <-
        flag
            False
            True
            ( long "use-c-calling-convention"
                <> help ("For debugging the compiler only: Make the generated LLVM code use the ccc calling convention instead of tailcc. This will break all tail calls, lead to stack overflows and possibly performance losses, but it might make it easier to debug miscompilations.")
            )

    pure Build{optimizationLevel, persistence, linker, includeUnique, debugEmitConfig, verifyMIR, useCCallingConvention}

parseDebugEmitConfig :: Parser DebugEmit.EmitConfig
parseDebugEmitConfig = do
    core <- flag False True (long "debug-core" <> help "Emit core output for debugging")
    mir <- flag False True (long "debug-mir" <> help "Emit MIR output for debugging.")
    monomorphizedMIR <- flag False True (long "debug-monomorphized-mir" <> help "Emit monomorphized MIR output for debugging.")
    llvm <- flag False True (long "debug-llvm" <> help "Emit the generated LLVM output for debugging.")
    optimizedLLVM <- flag False True (long "debug-optimized-llvm" <> help "Emit the fully optimized LLVM output for debugging. This does not include the custom shadow stack pass. Use --debug-shadow-stack to debug that.")
    llvmWithShadowStack <- flag False True (long "debug-shadow-stack" <> help "Emit the final LLVM including the custom shadow stack lowering.")
    assembly <- flag False True (long "debug-asm" <> help "Emit the generated assembly for debugging.")
    pure (DebugEmit.MkEmitConfig{core, mir, monomorphizedMIR, llvm, optimizedLLVM, llvmWithShadowStack, assembly})

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
    DebugEmit.EmitConfig ->
    PersistenceBackend ->
    Eff
        '[ Reader Driver.DriverConfig
         , DebugEmit
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
            & DebugEmit.runDebugEmit debugConfig
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
                { optimizationLevel = options.optimizationLevel
                , verifyMIR = options.verifyMIR
                , linker = options.linker
                }
    case options of
        Build{persistence, debugEmitConfig, useCCallingConvention} -> run driverConfig debugEmitConfig persistence do
            liftIO $ MIRToLLVM.useCCallingConvention useCCallingConvention
            let eprint :: forall io. (MonadIO io) => Doc Ann -> io ()
                eprint doc = do
                    liftIO (hIsTerminalDevice stderr) >>= \case
                        True -> do
                            eprintANSII doc
                        False -> liftIO (Text.hPutStrLn stderr (prettyPlain doc))

            Package.findConfig [osp|.|] >>= \case
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
                Found packageConfig -> do
                    let ?mainPackage = packageConfig
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
        Exec{file, mainFunction} -> run
            driverConfig
            DebugEmit.MkEmitConfig
                { core = False
                , mir = False
                , monomorphizedMIR = False
                , llvm = False
                , optimizedLLVM = False
                , llvmWithShadowStack = False
                , assembly = False
                }
            InMemory
            do
                Driver.execute file mainFunction
