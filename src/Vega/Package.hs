{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}

module Vega.Package (
    -- * Configuration
    PackageConfig,
    Dependency (..),
    Backend (..),
    name,
    sourceDirectory,
    entryPoint,
    backend,
    dependencies,

    -- * Config Files
    PackageConfigPresence (..),
    findConfig,
    parseConfigFile,

    -- * Build Artifacts
    ensureOutputDirectory,
    ensureJavascriptOutputFile,

    -- * Other
    moduleNameForPath,
) where

import Relude

import Effectful

import Data.Aeson qualified as Aeson
import Data.Yaml as Yaml hiding (object)

import Data.Aeson.Types (typeMismatch)
import Data.Aeson.Types qualified as Aeson
import Data.Text qualified as Text
import Data.Traversable (for)
import Effectful.Error.Static (Error)
import System.Directory.OsPath (canonicalizePath, listDirectory, createDirectoryIfMissing)
import System.IO.Unsafe (unsafePerformIO)
import System.OsPath (OsPath, osp, (</>))
import System.OsPath qualified as OsPath
import Vega.Seq.NonEmpty (NonEmpty (..))
import Vega.Syntax (GlobalName (..), ModuleName (..), PackageName (..))
import Vega.Util (decodeOsPathUnchecked)

data Dependency = LocalDependency {src :: OsPath}
    deriving (Generic, Show)

instance FromJSON Dependency where
    parseJSON :: Value -> Parser Dependency
    parseJSON = Aeson.withObject "dependency" \object -> do
        type_ :: Text <- object .: "type"
        case type_ of
            "local" -> parseLocalDependency object
            _ -> Aeson.parseFail $ toString $ "Invalid dependency type: " <> type_

parseLocalDependency :: Aeson.Object -> Parser Dependency
parseLocalDependency object = do
    MkJSONOsPath src <- object .: "src"
    pure (LocalDependency{src})

data PackageConfigContents = MkPackageConfigContents
    { name :: Text
    , sourceDirectory :: Maybe JSONOsPath
    , entryPoint :: Maybe Text
    , backend :: Maybe Backend
    , dependencies :: Maybe (Seq Dependency)
    }
    deriving (Generic, Show)

newtype JSONOsPath = MkJSONOsPath OsPath
    deriving newtype (Show)

instance FromJSON JSONOsPath where
    parseJSON value = do
        string <- parseJSON @String value
        case OsPath.encodeUtf string of
            Left error -> Aeson.parseFail $ "Invalid file path: " <> show error
            Right osPath -> pure (MkJSONOsPath osPath)

instance FromJSON PackageConfigContents where
    parseJSON :: Value -> Parser PackageConfigContents
    parseJSON =
        Aeson.genericParseJSON
            ( Aeson.defaultOptions
                { Aeson.fieldLabelModifier = Aeson.camelTo2 '-'
                , Aeson.rejectUnknownFields = True
                }
            )

data PackageConfig = MkPackageConfig
    { contents :: PackageConfigContents
    , projectRoot :: OsPath
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
        String backend -> fail $ toString $ "Invalid backend: '" <> backend <> "'. Expected one of 'javascript', 'debug', 'release'"
        other -> typeMismatch "string" other

sourceDirectory :: PackageConfig -> OsPath
sourceDirectory config = case config.contents.sourceDirectory of
    Nothing -> config.projectRoot </> [osp|src|]
    Just (MkJSONOsPath sourceDirectory) -> config.projectRoot </> sourceDirectory

entryPoint :: PackageConfig -> GlobalName
entryPoint config = case config.contents.entryPoint of
    Nothing -> MkGlobalName{moduleName = moduleNameForPath config (sourceDirectory config </> [osp|Main.vega|]), name = "main"}
    -- TODO: figure out how exactly to parse declaration names here
    Just name -> undefined

backend :: PackageConfig -> Backend
backend config = case config.contents.backend of
    Nothing -> JavaScript
    Just backend -> backend

dependencies :: PackageConfig -> Seq Dependency
dependencies config = case config.contents.dependencies of
    Nothing -> []
    Just dependencies -> dependencies

name :: PackageConfig -> Text
name config = config.contents.name

data PackageConfigPresence
    = Found PackageConfig
    | Invalid Yaml.ParseException
    | Missing

findConfig :: (MonadIO io) => OsPath -> io PackageConfigPresence
findConfig directory = liftIO do
    files <- listDirectory directory
    case [osp|vega.yaml|] `elem` files of
        True -> do
            projectRoot <- canonicalizePath $ directory
            let foundPath = projectRoot </> [osp|vega.yaml|]

            configOrError <- parseConfigFile foundPath
            case configOrError of
                Left error -> pure (Invalid error)
                Right config -> pure (Found config)
        False -> do
            parentDirectory <- canonicalizePath (directory </> [osp|..|])
            if parentDirectory == directory
                then -- We have hit the root directory
                    pure Missing
                else findConfig parentDirectory

parseConfigFile :: (MonadIO io) => OsPath -> io (Either Yaml.ParseException PackageConfig)
parseConfigFile inputPath = liftIO do
    path <- canonicalizePath inputPath
    contents <- liftIO $ Yaml.decodeFileEither (decodeOsPathUnchecked path)

    let projectRoot = OsPath.dropFileName path
    case contents of
        Left error -> pure (Left error)
        Right contents -> pure (Right (MkPackageConfig{contents, projectRoot}))

moduleNameForPath :: (HasCallStack) => PackageConfig -> OsPath -> ModuleName
moduleNameForPath buildConfig path = do
    -- TODO: validate that the path is actually relative to the project root
    let relativePath = OsPath.makeRelative (sourceDirectory buildConfig) path

    let package = MkPackageName (buildConfig.contents.name)
    -- TODO: validate that the path components are valid identifiers, etc.
    let rawSubModules = case OsPath.splitDirectories relativePath of
            [] -> error "empty file path after root"
            (x : xs) -> (x :<|| fromList xs)

    let subModulePaths = case rawSubModules of
            (rest :||> last) -> rest :||> OsPath.dropExtension last

    let subModules = unsafePerformIO $ for subModulePaths \osPath -> toText <$> (OsPath.decodeFS osPath)

    MkModuleName{package, subModules}

-- | Create the output directory of this package if necessary and return it
ensureOutputDirectory :: MonadIO io => PackageConfig -> io OsPath
ensureOutputDirectory config = liftIO do
    let path = config.projectRoot </> [osp|.vega|]
    createDirectoryIfMissing True path
    pure path

-- | Return the javascript output file of this package and ensure that it can be written to (i.e. create its parent directories)
ensureJavascriptOutputFile :: MonadIO io => PackageConfig -> io OsPath
ensureJavascriptOutputFile config = do
    outputDir <- ensureOutputDirectory config
    pure $ outputDir </> (OsPath.unsafeEncodeUtf (toString (name config) <> ".js"))
