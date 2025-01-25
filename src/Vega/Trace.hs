module Vega.Trace (
    Category(..),
    traceIO,
    trace,
    tracePure,
) where

import Data.Text qualified as Text
import Relude hiding (trace)
import System.Environment (getEnv)
import System.IO.Unsafe (unsafePerformIO)

data Category
    = Driver
    deriving (Show)

data Traces = MkTraces
    { driver :: Bool
    }

getTraces :: IO Traces
getTraces = do
    traceSetting <- Text.pack <$> getEnv "VEGA_TRACE"
    let traceNames = Text.splitOn "," traceSetting
    go (MkTraces{driver = False}) traceNames
  where
    go traces names = case names of
        [] -> pure traces
        ("driver" : rest) -> go (traces{driver = True}) rest
        (trace_ : rest) -> do
            -- TODO: make the warning prettier
            putTextLn $ "WARNING: unrecognized trace category: " <> trace_
            go traces rest

enabledTraces :: Traces
enabledTraces = unsafePerformIO $ getTraces
{-# NOINLINE enabledTraces #-}

-- This is NOINLINE to avoid duplicating work but since getTraces is deterministic, it doesn't
-- actually do anything dangerous

traceEnabled :: Category -> Bool
traceEnabled = \case
    Driver -> enabledTraces.driver

-- TODO: Use a doc here
traceIO :: Category -> Text -> IO ()
traceIO category text =
    when (traceEnabled category) do
        putTextLn ("[" <> show category <> "]: " <> text)

tracePure :: Category -> Text -> a -> a
tracePure category text a =
    unsafePerformIO (traceIO category text) `seq` a

trace :: (Applicative f) => Category -> Text -> f ()
trace category text = tracePure category text (pure ())
