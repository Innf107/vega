{-# LANGUAGE TemplateHaskell #-}

module Vega.Effect.DebugEmit where

import Data.ByteString qualified as ByteString
import Effectful
import Effectful.Dispatch.Dynamic (interpret_)
import Effectful.FileSystem.IO (openFile, runFileSystem, withBinaryFile)
import Effectful.TH (makeEffect)
import Relude
import Vega.Pretty (Ann, Doc, Pretty, PrettyANSIIConfig, eprintANSII, pretty, prettyPlain)

data DebugEmit a :: Effect where
    DebugEmit :: a -> DebugEmit a m ()

makeEffect ''DebugEmit

emitAllToFile :: (IOE :> es) => (a -> ByteString) -> FilePath -> Eff (DebugEmit a : es) b -> Eff es b
emitAllToFile renderValue filePath eff = runFileSystem do
    withBinaryFile filePath WriteMode \handle -> do
        raise $
            eff & interpret_ \case
                DebugEmit value ->
                    liftIO $ ByteString.hPut handle (renderValue value)

emitToStderr :: (?config :: PrettyANSIIConfig, IOE :> es) => (a -> Doc Ann) -> Eff (DebugEmit a : es) b -> Eff es b
emitToStderr prettyValue = do
    interpret_ \case
        DebugEmit value ->
            eprintANSII (prettyValue value)

ignoreEmit :: Eff (DebugEmit a : es) b -> Eff es b
ignoreEmit = interpret_ \case
    DebugEmit _ -> pure ()