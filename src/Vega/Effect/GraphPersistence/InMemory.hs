module Vega.Effect.GraphPersistence.InMemory (runInMemory) where

import Relude
import Relude.Extra

import Data.Map qualified as Map

import Vega.Effect.GraphPersistence

import Data.Time (UTCTime (UTCTime))
import Effectful
import Effectful.Dispatch.Dynamic
import Vega.Syntax

runInMemory :: (IOE :> es) => Eff (GraphPersistence : es) a -> Eff es a
runInMemory action = do
    trackedModules :: IORef (Map FilePath UTCTime) <- liftIO $ newIORef mempty
    lastKnownDeclarationsPerFile :: IORef (HashMap FilePath (HashMap GlobalName (Declaration Parsed))) <- liftIO $ newIORef mempty

    action & interpret \_ -> \case
        AddTrackedModule filePath timestamp -> do
            liftIO $ modifyIORef' trackedModules (Map.insert filePath timestamp)
        GetTrackedModules -> liftIO $ readIORef trackedModules
        LastKnownDeclarations filePath -> liftIO do
            declarationsPerFile <- readIORef lastKnownDeclarationsPerFile
            pure $ lookup filePath declarationsPerFile
        GetGlobalType name -> undefined
        RegisterDeclarationError name error -> undefined
        ClearDeclarationError name -> undefined
        GetPreviousDeclarationErrors name -> undefined
        SetKnownDeclarations filePath declarations -> undefined
