{-# LANGUAGE TemplateHaskell #-}

module Vega.Effect.GraphPersistence where

import Relude hiding (Type)

import Vega.Syntax hiding (Effect)

import Effectful
import Effectful.Dispatch.Dynamic (send)
import Effectful.TH (makeEffect)

import Data.Time (UTCTime)
import Vega.Error (Error)

data GraphPersistence :: Effect where
    AddTrackedModule :: FilePath -> UTCTime -> GraphPersistence m ()
    GetTrackedModules :: GraphPersistence m (Map FilePath UTCTime)
    LastKnownDeclarations :: FilePath -> GraphPersistence m (Maybe (HashMap GlobalName (Declaration Parsed)))
    SetKnownDeclarations :: FilePath -> HashMap GlobalName (Declaration Parsed) -> GraphPersistence m ()
    GetGlobalType :: GlobalName -> GraphPersistence m (Maybe Type)
    RegisterDeclarationError :: GlobalName -> Error -> GraphPersistence m ()
    ClearDeclarationError :: GlobalName -> GraphPersistence m ()
    GetPreviousDeclarationErrors :: GlobalName -> GraphPersistence m (Maybe Error)

makeEffect ''GraphPersistence
