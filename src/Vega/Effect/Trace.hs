{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}

module Vega.Effect.Trace (
    Trace (..),
    trace,
    withTrace,
    traceEnabled,
    whenTraceEnabled,
    runTrace,
    Traces (..),
    Category (..),
) where

import Relude hiding (Reader, ask, local, runReader, trace)

import Effectful

import Data.List (maximum)
import Data.Text qualified as Text
import Data.Text.IO (hPutStrLn)
import Effectful.Dispatch.Dynamic (EffectHandler, impose, interpose, interpret, localSeqUnlift, localSeqUnliftIO, reinterpret)
import Effectful.Reader.Dynamic (Reader, ask, local, runReader)
import Effectful.TH (makeEffect)
import Vega.Pretty (Ann, Doc, defaultPrettyANSIIConfig, prettyANSII)

data Category
    = Driver
    | WorkItems
    | AssembleJS
    | Dependencies
    | TypeCheck
    deriving (Generic, Show, Enum, Bounded)

data Trace :: Effect where
    Trace :: Category -> Doc Ann -> Trace m ()
    TraceEnabled :: Category -> Trace m Bool
    WithTrace :: Category -> Doc Ann -> m a -> Trace m a

makeEffect ''Trace

whenTraceEnabled :: (Trace :> es) => Category -> Eff es () -> Eff es ()
whenTraceEnabled category cont = do
    enabled <- traceEnabled category
    when enabled cont

data Traces = MkTraces
    { driver :: Bool
    , workItems :: Bool
    , assembleJS :: Bool
    , dependencies :: Bool
    , typeCheck :: Bool
    }

categoryWidth :: Traces -> Int
categoryWidth traces =
    maximum $
        map (length @[] . show) $
            filter (`traceEnabledIn` traces) $
                enumFrom (minBound @Category)

runTrace :: forall es a. (IOE :> es) => Eff (Trace : es) a -> Eff es a
runTrace eff = do
    enabledTraces <- getTraces
    let width = categoryWidth enabledTraces
    let ?config = defaultPrettyANSIIConfig
    let trace category message = do
            depth <- ask @Int
            when (traceEnabledIn category enabledTraces) do
                liftIO $ hPutStrLn stderr ("[" <> Text.justifyLeft (width + 4) ' ' (show category <> "]: ") <> Text.replicate depth "│ " <> message)
    let handler :: EffectHandler Trace (Reader Int : es)
        handler env operation = do
            case operation of
                Trace category message -> do
                    trace category (prettyANSII message)
                WithTrace category message inner -> localSeqUnlift env \unlift -> do
                    trace category (prettyANSII message)
                    local ((+) @Int 1) $ unlift inner
                TraceEnabled category -> pure $ traceEnabledIn category enabledTraces
    reinterpret (runReader (0 :: Int)) handler eff

traceEnabledIn :: Category -> Traces -> Bool
traceEnabledIn category enabledTraces = case category of
    Driver -> enabledTraces.driver
    WorkItems -> enabledTraces.workItems
    AssembleJS -> enabledTraces.assembleJS
    Dependencies -> enabledTraces.dependencies
    TypeCheck -> enabledTraces.typeCheck

getTraces :: (MonadIO io) => io Traces
getTraces =
    lookupEnv "VEGA_TRACE" >>= \case
        Nothing -> pure defaultTraces
        Just traceSettings -> do
            let traceNames = Text.splitOn "," (Text.pack traceSettings)
            go defaultTraces traceNames
  where
    go traces names = case names of
        [] -> pure traces
        ("" : rest) -> go traces rest
        ("driver" : rest) -> go (traces{driver = True}) rest
        ("work-items" : rest) -> go (traces{workItems = True}) rest
        ("assemble-js" : rest) -> go (traces{assembleJS = True}) rest
        ("dependencies" : rest) -> go (traces{dependencies = True}) rest
        ("types" : rest) -> go (traces{typeCheck = True}) rest
        (trace_ : rest) -> do
            -- TODO: make the warning prettier
            putTextLn $ "WARNING: unrecognized trace category: " <> trace_
            go traces rest

defaultTraces :: Traces
defaultTraces =
    MkTraces
        { driver = False
        , workItems = False
        , assembleJS = False
        , dependencies = False
        , typeCheck = False
        }
