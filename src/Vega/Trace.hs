{-# LANGUAGE AllowAmbiguousTypes #-}

module Vega.Trace (
    MonadTrace (..),
    Category (..),
    TraceAction (..),
    traceStderrAction,
    TraceConfig (..),
) where

import Vega.Prelude

import Vega.Pretty

import Control.Monad.Base (MonadBase, liftBase)
import Data.Text.IO (hPutStrLn)

newtype TraceAction m = MkTraceAction (Category -> Doc Ann -> m ())

data Category
    = Types
    | Unify
    | Subst
    deriving (Show)

class MonadTrace m where
    trace :: Category -> Doc Ann -> m ()

instance (MonadBase traceM m) => MonadTrace (ReaderT (TraceAction traceM) m) where
    trace category doc = do
        MkTraceAction action <- ask
        liftBase (action category doc)

data TraceConfig = MkTraceConfig
    { types :: Bool
    , unify :: Bool
    , subst :: Bool
    } deriving (Generic)

traceEnabled :: Category -> TraceConfig -> Bool
traceEnabled category config = case category of
    Types -> config.types
    Unify -> config.unify
    Subst -> config.subst

traceStderrAction :: (Doc Ann -> Text) -> TraceConfig -> TraceAction IO
traceStderrAction render config = MkTraceAction \category doc ->
    when (traceEnabled category config) do
        hPutStrLn stderr ("[" <> show category <> "]: " <> render doc)
