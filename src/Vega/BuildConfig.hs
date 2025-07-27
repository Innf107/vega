{-# LANGUAGE RecordWildCards #-}

module Vega.BuildConfig (
    BuildConfigPresence (..),
    findBuildConfig,
    BuildConfigContents (..),
    BuildConfig (..),
    sourceDirectory,
    entryPoint,
    backend,
    Backend (..),
    moduleNameForPath,
) where

import Relude

import Control.Exception
import Effectful
import Effectful.FileSystem (FileSystem, canonicalizePath, listDirectory)

import Data.Aeson qualified as Aeson
import Data.Yaml as Yaml hiding (object)

import Data.Text qualified as Text
import System.FilePath ((</>))
import System.FilePath qualified as FilePath
import Vega.Seq.NonEmpty (NonEmpty (..))
import Vega.Syntax (DeclarationName (..), GlobalName (..), ModuleName (..), PackageName (..))

data BuildConfigContents = MkBuildConfigContents
    { name :: Text
    , sourceDirectory :: Maybe FilePath
    , entryPoint :: Maybe Text
    , backend :: Maybe Backend
    }
    deriving (Generic, Show)

instance FromJSON BuildConfigContents where
    parseJSON :: Value -> Parser BuildConfigContents
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

data Backend
    = JavaScript
    | NativeRelease
    | NativeDebug
    deriving (Generic, Show)

instance FromJSON Backend where
    parseJSON = \case
        String "javascript" -> pure JavaScript
        String "debug" -> pure NativeDebug
        String "release" -> pure NativeRelease
        _ -> undefined

sourceDirectory :: BuildConfig -> FilePath
sourceDirectory config = case config.contents.sourceDirectory of
    Nothing -> config.projectRoot </> "src"
    Just sourceDirectory -> config.projectRoot </> sourceDirectory

entryPoint :: BuildConfig -> GlobalName
entryPoint config = case config.contents.entryPoint of
    Nothing -> MkGlobalName{moduleName = moduleNameForPath config (sourceDirectory config </> "Main.vega"), name = "main"}
    -- TODO: figure out how exactly to parse declaration names here
    Just name -> undefined

backend :: BuildConfig -> Backend
backend config = case config.contents.backend of
    Nothing -> JavaScript
    Just backend -> backend

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

moduleNameForPath :: (HasCallStack) => BuildConfig -> FilePath -> ModuleName
moduleNameForPath buildConfig path = do
    -- TODO: validate that the path is actually relative to the project root
    let relativePath = FilePath.makeRelative (sourceDirectory buildConfig) path

    let package = MkPackageName (buildConfig.contents.name)
    -- TODO: validate that the path components are valid identifiers, etc.
    let rawSubModules = case Text.splitOn "/" (toText relativePath) of
            [] -> error "empty file path after root"
            (x : xs) -> (x :<|| fromList xs)

    let subModules = case rawSubModules of
            (rest :||> last) -> rest :||> toText (FilePath.dropExtension (toString last))
    MkModuleName{package, subModules}
