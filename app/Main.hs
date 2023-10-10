module Main (main) where

import Vega.Driver qualified as Driver
import Vega.Loc (getLoc, prettyErrorLoc)
import Vega.Prelude
import Vega.Pretty
import Vega.Trace (TraceConfig (..), traceStderrAction)

main :: IO ()
main =
    getArgs >>= \case
        [file] -> do
            let ?traceAction =
                    traceStderrAction
                        prettyANSII
                        ( MkTraceConfig
                            { types = True
                            , unify = True
                            , subst = True
                            }
                        )
            contents <- decodeUtf8 <$> readFileBS file

            coreOrErrors <- Driver.parseRenameTypeCheck file contents

            -- TODO: Only use prettyANSII if the output is a tty
            case coreOrErrors of
                Left errors ->
                    for_ errors \error -> putTextLn (prettyANSII (prettyErrorLoc (getLoc error) (pretty error)))
                Right core -> putTextLn "success"
        _ -> do
            putStrLn "usage: vega <FILE>"
            exitFailure
