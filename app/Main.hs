module Main (main) where

import Vega.Debug
import Vega.Driver qualified as Driver
import Vega.Error (extractRange)
import Vega.Loc (Loc, getLoc)
import Vega.Prelude
import Vega.Pretty
import Vega.Trace (TraceConfig (..), traceStderrAction)

import Vega.Compile.Lua qualified as Lua

import Options.Generic

import System.IO (hIsTerminalDevice)

import qualified Data.Text.IO as Text

data Flags = Flags {trace :: [Text], includeUnique :: Bool, coreLint :: Bool}
    deriving (Show, Generic)

instance ParseRecord Flags

data Arguments
    = Compile FilePath
    deriving (Show, Generic)

instance ParseRecord Arguments

data ArgumentsAndFlags = MkArgumentsAndFlags {flags :: Flags, arguments :: Arguments}
    deriving (Show, Generic)

instance ParseRecord ArgumentsAndFlags where
    parseRecord = MkArgumentsAndFlags <$> parseRecord <*> parseRecord

parseTraceConfig :: IO () -> [Text] -> IO TraceConfig
parseTraceConfig help = go (MkTraceConfig{types = False, unify = False, subst = False, patterns = False})
  where
    go config = \case
        [] -> pure config
        "types" : rest -> go (config{types = True}) rest
        "unify" : rest -> go (config{unify = True}) rest
        "subst" : rest -> go (config{subst = True}) rest
        "patterns" : rest -> go (config{patterns = True}) rest
        category : _ -> do
            putTextLn ("Invalid trace category: '" <> category <> "'. Valid categories include: " <> intercalate ", " (getRecordFields @TraceConfig) <> "\n")
            help
            exitFailure

main :: IO ()
main = do
    (MkArgumentsAndFlags{flags, arguments}, help) <- getWithHelp "Compiler for the Vega programming language"

    case arguments of
        Compile file -> do
            traceConfig <- parseTraceConfig help flags.trace

            let ?config = defaultPrettyANSIIConfig{Vega.Pretty.includeUnique = flags.includeUnique}
            renderStderr <-
                hIsTerminalDevice stderr <&> \case
                    False -> prettyPlain
                    True -> prettyANSII
            renderStdout <-
                hIsTerminalDevice stdout <&> \case
                    False -> prettyPlain
                    True -> prettyANSII

            let ?driverConfig =
                    Driver.MkDriverConfig
                        { enableCoreLint = flags.coreLint
                        }

            let ?traceAction =
                    traceStderrAction
                        renderStderr
                        traceConfig
            contents <- decodeUtf8 <$> readFileBS file

            (coreOrErrors, warnings) <- Driver.parseRenameTypeCheck file contents

            for_ warnings \warning -> do
                Text.hPutStrLn stderr (renderStderr (pretty warning))

            case coreOrErrors of
                Left errors -> do
                    for_ errors \error -> do
                        doc <- prettyErrorLoc (getLoc error) (pretty error)
                        putTextLn (renderStdout doc)
                    exitFailure
                Right core -> do
                    luaCode <- Lua.compile core
                    putTextLn luaCode

prettyErrorLoc :: (MonadIO io) => Loc -> Doc Ann -> io (Doc Ann)
prettyErrorLoc loc doc = do
    code <- extractRange loc
    pure
        $ pretty loc
        <> emphasis ":"
        <+> errorDoc "ERROR:"
        <> "\n"
        <> doc
        <> "\n"
        <> code