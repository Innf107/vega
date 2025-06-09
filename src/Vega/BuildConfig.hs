{-# LANGUAGE RecordWildCards #-}

module Vega.BuildConfig (BuildConfig (..), BuildConfigPresence (..), buildConfigDecoder, findBuildConfig) where

import Relude

import Control.Exception
import Effectful
import Effectful.FileSystem (FileSystem, canonicalizePath, listDirectory)

import Dhall qualified
import Dhall.Marshal.Decode (Decoder, field, record)
import Dhall.Src (Src)
import System.FilePath ((</>))

data BuildConfig = MkBuildConfig
    { name :: Text
    , projectRoot :: FilePath
    , sourceDirectory :: FilePath
    }
    deriving (Generic, Show)

buildConfigDecoder :: FilePath -> Decoder BuildConfig
buildConfigDecoder projectRoot =
    record do
        name <- field "name" Dhall.auto
        -- TODO: Figure out how to make this optional or switch back to YAML
        sourceDirectory <- (projectRoot </>) <$> field "source-directory" Dhall.auto
        pure MkBuildConfig{..}

data BuildConfigPresence
    = Found BuildConfig
    | Invalid (Dhall.ExtractErrors Src Void)
    | Missing

findBuildConfig :: (FileSystem :> es, IOE :> es) => FilePath -> Eff es BuildConfigPresence
findBuildConfig directory = do
    files <- listDirectory directory
    case "vega.dhall" `elem` files of
        True -> do
            projectRoot <- canonicalizePath $ directory
            let foundPath = projectRoot </> "vega.dhall"

            -- TODO: catch the remaining errors
            configOrError <- liftIO $ try @(Dhall.ExtractErrors Src Void) $ Dhall.inputFile (buildConfigDecoder projectRoot) foundPath
            case configOrError of
                Left error -> pure (Invalid error)
                Right config -> pure (Found config)
        False -> do
            parentDirectory <- canonicalizePath (directory </> "..")
            if parentDirectory == directory
                then -- We have hit the root directory
                    pure Missing
                else findBuildConfig parentDirectory
