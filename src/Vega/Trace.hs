{-# LANGUAGE AllowAmbiguousTypes #-}

module Vega.Trace (
    MonadTrace (..),
    Category (..),
    TraceAction (..),
    traceStderrAction,
    ignoredTraceAction,
    TraceConfig (..),
) where

import Vega.Prelude

import Vega.Pretty

import Control.Monad.Base (MonadBase, liftBase)
import Data.Text.IO (hPutStrLn)

import Data.List (maximum)
import Data.Text qualified as Text

data TraceAction m = MkTraceAction
    { depth :: Int
    , action :: Int -> Category -> Doc Ann -> m ()
    }

data Category
    = Types
    | Unify
    | Subst
    | Patterns
    | Eval
    deriving (Show, Enum, Bounded)

class MonadTrace m where
    trace :: Category -> Doc Ann -> m ()
    withTrace :: Category -> Doc Ann -> m a -> m a

instance (MonadBase traceM m) => MonadTrace (ReaderT (TraceAction traceM) m) where
    trace category doc = do
        MkTraceAction{action, depth} <- ask
        liftBase (action depth category doc)
    withTrace category doc cont = do
        trace category doc
        local (\action -> action{depth = action.depth + 1}) cont

data TraceConfig = MkTraceConfig
    { types :: Bool
    , unify :: Bool
    , subst :: Bool
    , patterns :: Bool
    , eval :: Bool
    }
    deriving (Generic)

traceEnabled :: Category -> TraceConfig -> Bool
traceEnabled category config = case category of
    Types -> config.types
    Unify -> config.unify
    Subst -> config.subst
    Patterns -> config.patterns
    Eval -> config.eval

categoryWidth :: TraceConfig -> Int
categoryWidth config =
    maximum
        $ map (length @[] . show)
        $ filter (`traceEnabled` config)
        $ enumFrom (minBound @Category)

traceStderrAction :: (Doc Ann -> Text) -> TraceConfig -> TraceAction IO
traceStderrAction render config = do
    let width = categoryWidth config
    MkTraceAction 0 \depth category doc ->
        when (traceEnabled category config) do
            hPutStrLn stderr ("[" <> Text.justifyLeft (width + 4) ' ' (show category <> "]: ") <> Text.replicate depth "│ " <> render doc)

ignoredTraceAction :: (Applicative f) => TraceAction f
ignoredTraceAction = MkTraceAction 0 \_ _ _ -> pure ()
