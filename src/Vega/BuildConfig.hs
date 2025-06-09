{-# LANGUAGE RecordWildCards #-}

module Vega.BuildConfig (BuildConfigContents (..), BuildConfig (..), sourceDirectory, BuildConfigPresence (..), findBuildConfig) where

import Relude

import Control.Exception
import Effectful
import Effectful.FileSystem (FileSystem, canonicalizePath, listDirectory)

import Data.Aeson qualified as Aeson
import Data.Yaml as Yaml hiding (object)

import System.FilePath ((</>))

data BuildConfigContents = MkBuildConfigContents
    { name :: Text
    , sourceDirectory :: Maybe FilePath
    }
    deriving (Generic, Show)

instance FromJSON BuildConfigContents where
    parseJSON =
        Aeson.genericParseJSON
            ( Aeson.defaultOptions
                { Aeson.fieldLabelModifier = Aeson.camelTo2 '-'
                , Aeson.rejectUnknownFields = True
                }
            )

data BuildConfig = MkBuildConfig
    { contents :: BuildConfigContents
    , projectRoot :: FilePath
    }
    deriving stock (Generic, Show)

sourceDirectory :: BuildConfig -> FilePath
sourceDirectory config = case config.contents.sourceDirectory of
    Nothing -> config.projectRoot </> "src"
    Just sourceDirectory -> config.projectRoot </> sourceDirectory

data BuildConfigPresence
    = Found BuildConfig
    | Invalid Yaml.ParseException
    | Missing

findBuildConfig :: (FileSystem :> es, IOE :> es) => FilePath -> Eff es BuildConfigPresence
findBuildConfig directory = do
    files <- listDirectory directory
    case "vega.yaml" `elem` files of
        True -> do
            projectRoot <- canonicalizePath $ directory
            let foundPath = projectRoot </> "vega.yaml"

            configOrError <- liftIO $ Yaml.decodeFileEither foundPath
            case configOrError of
                Left error -> pure (Invalid error)
                Right contents -> pure (Found (MkBuildConfig{contents, projectRoot}))
        False -> do
            parentDirectory <- canonicalizePath (directory </> "..")
            if parentDirectory == directory
                then -- We have hit the root directory
                    pure Missing
                else findBuildConfig parentDirectory
