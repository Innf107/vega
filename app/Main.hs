module Main (main) where

import Vega.Driver qualified as Driver
import Vega.Loc (getLoc, prettyErrorLoc)
import Vega.Prelude
import Vega.Pretty
import Vega.Debug
import Vega.Trace (TraceConfig (..), traceStderrAction)

import Options.Generic 

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
            category : rest -> do
                putTextLn ("Invalid trace category: '" <> category <> "'. Valid categories include: " <> intercalate ", " (getRecordFields @TraceConfig) <> "\n")
                help
                exitFailure

main :: IO ()
main = do
    (MkArgumentsAndFlags { flags, arguments }, help) <- getWithHelp "Compiler for the Vega programming language"

    case arguments of
        Compile file -> do
            traceConfig <- parseTraceConfig help flags.trace

            let ?traceAction =
                            traceStderrAction
                                prettyANSII
                                traceConfig
            contents <- decodeUtf8 <$> readFileBS file

            coreOrErrors <- Driver.parseRenameTypeCheck file contents

                    -- TODO: Only use prettyANSII if the output is a tty
            case coreOrErrors of
                Left errors ->
                    for_ errors \error -> putTextLn (prettyANSII (prettyErrorLoc (getLoc error) (pretty error)))
                Right core -> putTextLn "success"