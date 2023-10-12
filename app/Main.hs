module Main (main) where

import Vega.Driver qualified as Driver
import Vega.Loc (getLoc, prettyErrorLoc)
import Vega.Prelude
import Vega.Pretty
import Vega.Debug
import Vega.Trace (TraceConfig (..), traceStderrAction)

import Options.Generic 

import System.IO (hIsTerminalDevice)

data Flags = Flags { trace :: [Text] }
    deriving (Show, Generic)

instance ParseRecord Flags

data Arguments 
    = Compile FilePath
    deriving (Show, Generic)

instance ParseRecord Arguments

data ArgumentsAndFlags = MkArgumentsAndFlags { flags :: Flags, arguments :: Arguments }
    deriving (Show, Generic)

instance ParseRecord ArgumentsAndFlags where
    parseRecord = MkArgumentsAndFlags <$> parseRecord <*> parseRecord

parseTraceConfig :: IO () -> [Text] -> IO TraceConfig
parseTraceConfig help = go (MkTraceConfig { types = False, unify = False, subst = False })
    where
        go config = \case
            [] -> pure config
            "types" : rest -> go (config { types = True }) rest
            "unify" : rest -> go (config { unify = True }) rest
            "subst" : rest -> go (config { subst = True }) rest
            category : _ -> do
                putTextLn ("Invalid trace category: '" <> category <> "'. Valid categories include: " <> intercalate ", " (getRecordFields @TraceConfig) <> "\n")
                help
                exitFailure

main :: IO ()
main = do
    (MkArgumentsAndFlags { flags, arguments }, help) <- getWithHelp "Compiler for the Vega programming language"

    case arguments of
        Compile file -> do
            traceConfig <- parseTraceConfig help flags.trace

            renderStderr <- hIsTerminalDevice stderr <&> \case
                False -> prettyPlain
                True -> prettyANSII
            renderStdout <- hIsTerminalDevice stdout <&> \case
                False -> prettyPlain
                True -> prettyANSII

            let ?traceAction =
                            traceStderrAction
                                renderStderr
                                traceConfig
            contents <- decodeUtf8 <$> readFileBS file

            coreOrErrors <- Driver.parseRenameTypeCheck file contents

                    -- TODO: Only use prettyANSII if the output is a tty
            case coreOrErrors of
                Left errors -> do
                    for_ errors \error -> putTextLn (renderStdout (prettyErrorLoc (getLoc error) (pretty error)))
                    exitFailure
                Right _core -> putTextLn "success"