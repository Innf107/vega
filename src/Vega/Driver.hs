module Vega.Driver (
    rebuild,
    execute,
    CompilationResult (..),
) where

-- TODO: check that imports make sense somewhere
-- TODO: diff imports and invalidate all declarations if they changed
-- TODO: check file modifications to avoid having to diff every module every time
-- TODO: remove modules if their files are deleted
-- TODO: catch duplicate declarations (in the parser i guess??)

import Relude hiding (Reader, ask, trace)

import Effectful
import Effectful.FileSystem (FileSystem, doesDirectoryExist, listDirectory)
import Effectful.Reader.Static
import System.FilePath (takeExtension, (</>))

import Data.Sequence (Seq (..))
import Data.Traversable (for)
import Effectful.Concurrent (Concurrent)
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError, throwError_)
import TextBuilder (TextBuilder)
import TextBuilder qualified

import Data.Text qualified as Text
import Effectful.Exception (try)
import System.FilePath qualified as FilePath
import Vega.BuildConfig (BuildConfig (..))
import Vega.BuildConfig qualified as BuildConfig
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.Core.VegaToCore qualified as VegaToCore
import Vega.Compilation.JavaScript.Assemble (assembleFromEntryPoint)
import Vega.Compilation.JavaScript.VegaToJavaScript qualified as JavaScript
import Vega.Diff (DiffChange (..))
import Vega.Diff qualified as Diff
import Vega.Effect.DebugEmit (DebugEmit, debugEmit)
import Vega.Effect.GraphPersistence (GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Effect.Trace (Category (..), Trace, trace, traceEnabled, whenTraceEnabled)
import Vega.Error (CompilationError (..), RenameErrorSet (..), TypeErrorSet (..))
import Vega.Error qualified as Error
import Vega.Lexer qualified as Lexer
import Vega.Parser qualified as Parser
import Vega.Pretty (keyword, pretty)
import Vega.Rename qualified as Rename
import Vega.Seq.NonEmpty (NonEmpty (..))
import Vega.Syntax
import Vega.TypeCheck qualified as TypeCheck
import Vega.Util (viaList)

data CompilationResult
    = CompilationSuccessful
    | CompilationFailed
        {errors :: Seq CompilationError}

-- TODO: distinguish between new and repeated errors

type Driver es =
    ( Reader BuildConfig :> es
    , GraphPersistence :> es
    , IOE :> es
    , FileSystem :> es
    , Concurrent :> es
    , Trace :> es
    , DebugEmit (Seq Core.Declaration) :> es
    )

findSourceFiles :: (Driver es) => Eff es (Seq FilePath)
findSourceFiles = do
    config <- ask @BuildConfig
    go (BuildConfig.sourceDirectory config)
  where
    go path = do
        files <- listDirectory path
        fold <$> for files \file -> do
            let filePath = path </> file
            doesDirectoryExist filePath >>= \case
                True -> go filePath
                False
                    | takeExtension file == ".vega" -> pure [filePath]
                    | otherwise -> pure []

computeImportScope :: (Driver es) => Seq Import -> Eff es ImportScope
computeImportScope imports = foldMapM toImportScope imports
  where
    -- TODO: allow importing from other packages without explicitly spelling out their module name
    resolveModuleName MkParsedModuleName{package, subModules} = case package of
        Nothing -> do
            buildConfig <- ask @BuildConfig
            let package = MkPackageName (buildConfig.contents.name)
            pure (MkModuleName{package, subModules})
        Just package -> pure (MkModuleName{package, subModules})

    toImportScope = \case
        ImportUnqualified{moduleName, importedDeclarations} -> do
            moduleName <- resolveModuleName moduleName
            pure $
                MkImportScope
                    { imports =
                        fromList
                            [
                                ( moduleName
                                , MkImportedItems
                                    { qualifiedAliases = mempty
                                    , unqualifiedItems = viaList importedDeclarations
                                    }
                                )
                            ]
                    }
        ImportQualified{moduleName, importedAs} -> do
            moduleName <- resolveModuleName moduleName
            pure $
                MkImportScope
                    { imports =
                        fromList
                            [
                                ( moduleName
                                , MkImportedItems
                                    { qualifiedAliases = [importedAs]
                                    , unqualifiedItems = mempty
                                    }
                                )
                            ]
                    }

parseAndDiff :: (Driver es, Error CompilationError :> es) => FilePath -> Eff es (Seq DiffChange)
parseAndDiff filePath = do
    buildConfig <- ask @BuildConfig
    let moduleName = BuildConfig.moduleNameForPath buildConfig filePath

    contents <- decodeUtf8 <$> readFileBS filePath
    tokens <- case Lexer.run (toText filePath) contents of
        Left error -> throwError_ (Error.LexicalError error)
        Right tokens -> pure tokens
    parsedModule <- case Parser.parse moduleName filePath tokens of
        Left errors -> throwError_ (Error.ParseError errors)
        Right parsedModule -> pure parsedModule

    importScope <- computeImportScope parsedModule.imports
    previousDeclarations <- GraphPersistence.lastKnownDeclarations filePath
    GraphPersistence.setKnownDeclarations filePath (viaList (fmap (\decl -> (decl.name, decl)) parsedModule.declarations))
    case previousDeclarations of
        Nothing -> do
            GraphPersistence.setModuleImportScope moduleName importScope
            pure $ Diff.reportNewModule parsedModule
        Just previous -> do
            previousImportScope <- GraphPersistence.getModuleImportScope moduleName
            if importScope /= previousImportScope
                then do
                    GraphPersistence.setModuleImportScope moduleName importScope
                    -- If imports changed, we simply invalidate every declaration in the module
                    pure $ fmap (\decl -> Changed decl) parsedModule.declarations
                else
                    Diff.diffDeclarations parsedModule.declarations previous

applyDiffChange :: (Driver es) => DiffChange -> Eff es ()
applyDiffChange = \case
    Added decl -> GraphPersistence.addDeclaration decl
    Changed decl ->
        GraphPersistence.setParsed decl
    Removed decl -> GraphPersistence.removeDeclaration decl

trackSourceChanges :: (Driver es) => Eff es (Seq CompilationError)
trackSourceChanges = do
    sourceFiles <- findSourceFiles
    (parseErrors, diffChanges) <- second fold . partitionEithers <$> for (toList sourceFiles) (runErrorNoCallStack . parseAndDiff)

    whenTraceEnabled Driver do
        for_ diffChanges \case
            Diff.Added decl -> trace Driver ("Declaration added: " <> pretty decl.name)
            Diff.Removed declName -> trace Driver ("Declaration removed: " <> pretty declName)
            Diff.Changed decl -> trace Driver ("Declaration changed: " <> pretty decl.name)

    for_ diffChanges applyDiffChange

    pure (fromList parseErrors)

performAllRemainingWork :: (Driver es) => Eff es ()
performAllRemainingWork = do
    config <- ask @BuildConfig

    remainingWorkItems <- GraphPersistence.getRemainingWork (BuildConfig.backend config)
    for_ remainingWorkItems \workItem -> do
        trace WorkItems ("Processing work item: " <> pretty workItem)
        case workItem of
            GraphPersistence.Rename name -> do
                rename name
            GraphPersistence.TypeCheck name -> do
                typecheck name
            GraphPersistence.CompileToJS name -> do
                compileToJS name
            GraphPersistence.CompileToCore name -> do
                compileToCore name

rebuild :: (Driver es) => Eff es CompilationResult
rebuild =
    try @SomeException go >>= \case
        Right result -> pure result
        Left exception -> do
            errors <- GraphPersistence.getCurrentErrors
            pure (CompilationFailed{errors = errors <> [Panic exception]})
  where
    go = do
        parseErrors <- trackSourceChanges

        performAllRemainingWork
        nonParseErrors <- GraphPersistence.getCurrentErrors
        case parseErrors <> nonParseErrors of
            [] -> do
                runErrorNoCallStack compileBackend >>= \case
                    Left error -> do
                        pure (CompilationFailed{errors = [DriverError error]})
                    Right () -> pure (CompilationSuccessful)
            errors -> pure (CompilationFailed{errors = errors})

compileBackend :: (Error Error.DriverError :> es, Driver es) => Eff es ()
compileBackend = do
    config <- ask @BuildConfig

    let entryPoint = BuildConfig.entryPoint config

    -- TODO: check that the entry point has the right type
    GraphPersistence.getDefiningDeclaration entryPoint >>= \case
        Just _ -> pure ()
        Nothing -> throwError_ (Error.EntryPointNotFound entryPoint)

    case BuildConfig.backend config of
        BuildConfig.JavaScript -> do
            jsCode <- assembleFromEntryPoint entryPoint

            -- TODO: make this configurable and make the path absolute
            writeFileLBS (toString $ config.contents.name <> ".js") (encodeUtf8 (TextBuilder.toText jsCode))
        BuildConfig.NativeRelease -> do
            undefined
        _ -> undefined

execute :: FilePath -> Text -> Eff es ()
execute = undefined

getLastKnownRenamed :: (Driver es) => DeclarationName -> Eff es (Maybe (Declaration Renamed))
getLastKnownRenamed name = do
    GraphPersistence.getRenamed name >>= \case
        Ok renamed -> pure $ Just renamed
        Missing{previous} -> pure previous
        Failed{previous} -> pure previous

typeChanged :: Declaration Renamed -> Declaration Renamed -> Bool
typeChanged old new = case old.syntax of
    DefineFunction{typeSignature = oldTypeSignature} -> case new.syntax of
        DefineFunction{typeSignature = newTypeSignature} -> Diff.diff oldTypeSignature newTypeSignature
        DefineVariantType{} -> undefined
    DefineVariantType{} -> undefined

rename :: (Driver es) => DeclarationName -> Eff es ()
rename name = do
    previous <- getLastKnownRenamed name

    parsed <- GraphPersistence.getParsed name
    (renamed, errors, dependencies) <- Rename.rename parsed
    trace Dependencies (show name <> " --> " <> show dependencies)

    for_ dependencies \dependency -> do
        GraphPersistence.addDependency name dependency

    case errors of
        MkRenameErrorSet (_ :|> _) -> do
            GraphPersistence.invalidateRenamed (Just errors) name
        MkRenameErrorSet Empty -> do
            GraphPersistence.setRenamed renamed

            case previous of
                Just previous
                    | typeChanged previous renamed -> do
                        dependents <- GraphPersistence.getDependents name
                        for_ dependents (GraphPersistence.invalidateTyped Nothing)
                _ -> pure ()

typecheck :: (Driver es) => DeclarationName -> Eff es ()
typecheck name =
    GraphPersistence.getRenamed name >>= \case
        Missing{} -> error $ "missing renamed in typecheck: " <> show name
        Failed{} -> pure ()
        Ok renamed -> do
            typedOrErrors <- TypeCheck.checkDeclaration renamed
            case typedOrErrors of
                Left errors -> do
                    GraphPersistence.invalidateTyped (Just errors) name
                Right typed -> do
                    GraphPersistence.setTyped typed

compileToJS :: (Driver es) => DeclarationName -> Eff es ()
compileToJS name =
    GraphPersistence.getTyped name >>= \case
        -- TODOOOO
        Missing{} -> pure () -- error $ "missing typed in compilation to JS: " <> show name
        Failed{} -> pure () -- If the previous stage errored, we won't try to compile it
        Ok typedDeclaration -> do
            compiled <- JavaScript.compileDeclaration typedDeclaration
            GraphPersistence.setCompiledJS name compiled

compileToCore :: (Driver es) => DeclarationName -> Eff es ()
compileToCore name =
    GraphPersistence.getTyped name >>= \case
        Missing{} -> pure ()
        Failed{} -> pure ()
        Ok typedDeclaration -> do
            compiled <- VegaToCore.compileDeclaration typedDeclaration
            debugEmit compiled
            GraphPersistence.setCompiledCore name compiled
