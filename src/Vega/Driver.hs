module Vega.Driver (
    rebuild,
    execute,
    CompilationResult (..),
    DriverConfig (..),
) where

-- TODO: check that imports make sense somewhere
-- TODO: diff imports and invalidate all declarations if they changed
-- TODO: check file modifications to avoid having to diff every module every time
-- TODO: remove modules if their files are deleted
-- TODO: catch duplicate declarations (in the parser i guess??)

import Relude hiding (Reader, ask, trace)

import Effectful
import Effectful.FileSystem (FileSystem, createDirectoryIfMissing, doesDirectoryExist, listDirectory)
import Effectful.Reader.Static
import System.FilePath (takeDirectory, takeExtension, (</>))

import Data.Sequence (Seq (..))
import Data.Traversable (for)
import Effectful.Concurrent (Concurrent)
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError_)
import TextBuilder qualified

import Effectful.Exception (try)
import Effectful.Process (Process, callProcess)
import LLVM.Core qualified as LLVM
import Streaming.Prelude qualified as Streaming
import Vega.BuildConfig (BuildConfig (..))
import Vega.BuildConfig qualified as BuildConfig
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.Core.VegaToCore qualified as VegaToCore
import Vega.Compilation.JavaScript.Assemble (assembleFromEntryPoint)
import Vega.Compilation.JavaScript.VegaToJavaScript qualified as JavaScript
import Vega.Compilation.MIR.CoreToMIR qualified as CoreToMIR
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Compilation.MIR.Verify qualified as VerifyMIR
import Vega.Compilation.MIRToLLVM qualified as MIRToLLVM
import Vega.Diff (DiffChange (..))
import Vega.Diff qualified as Diff
import Vega.Effect.DebugEmit (DebugEmit, debugEmit)
import Vega.Effect.GraphPersistence (GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Effect.Trace (Category (..), Trace, trace, traceEnabled, whenTraceEnabled)
import Vega.Effect.Unique.Static.Local (runNewUnique)
import Vega.Error (CompilationError (..), RenameErrorSet (..))
import Vega.Error qualified as Error
import Vega.Lexer qualified as Lexer
import Vega.Panic (panic)
import Vega.Parser qualified as Parser
import Vega.Pretty (keyword, pretty)
import Vega.Pretty qualified as Pretty
import Vega.Rename qualified as Rename
import Vega.Syntax
import Vega.TypeCheck qualified as TypeCheck
import Vega.Util (viaList)

data CompilationResult
    = CompilationSuccessful
    | CompilationFailed
        {errors :: Seq CompilationError}

data DriverConfig = MkDriverConfig
    { verifyMIR :: Bool
    }

-- TODO: distinguish between new and repeated errors
type Driver es =
    ( Reader BuildConfig :> es
    , Reader DriverConfig :> es
    , GraphPersistence :> es
    , IOE :> es
    , FileSystem :> es
    , Concurrent :> es
    , Trace :> es
    , DebugEmit (Seq Core.Declaration) :> es
    , DebugEmit (Seq MIR.Declaration) :> es
    , DebugEmit LLVM.Module :> es
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
computeImportScope imports = do
    foldMapM toImportScope imports
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
    trace ImportScope (keyword (toText filePath) <> ": " <> show importScope)

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
    entryPointDeclaration <-
        GraphPersistence.getDefiningDeclaration entryPoint >>= \case
            Just declaration -> pure declaration
            Nothing -> throwError_ (Error.EntryPointNotFound entryPoint)

    case BuildConfig.backend config of
        BuildConfig.JavaScript -> do
            jsCode <- assembleFromEntryPoint entryPoint

            -- TODO: make this configurable and make the path absolute
            writeFileLBS (toString $ config.contents.name <> ".js") (encodeUtf8 (TextBuilder.toText jsCode))
        BuildConfig.NativeRelease -> runNewUnique do
            MkDriverConfig{verifyMIR} <- ask
            let compileToMIR declarationName = do
                    core <-
                        GraphPersistence.getCompiledCore declarationName >>= \case
                            Ok core -> pure core
                            Missing{} -> panic $ "Missing Core for " <> pretty declarationName <> " in NativeRelease compilation to LIR"
                    fold <$> for core \declaration -> do
                        mir <- CoreToMIR.compileDeclaration declaration
                        debugEmit mir
                        pure mir

            let reachableStream = GraphPersistence.reachableFrom entryPointDeclaration

            traceEnabled Reachable >>= \case
                False -> pure ()
                True -> Streaming.mapM_ (\declarationName -> trace Reachable (pretty declarationName)) reachableStream

            mirDeclarations <- mconcat <$> Streaming.toList_ (Streaming.mapM compileToMIR reachableStream)

            let mirProgram = MIR.MkProgram{declarations = mirDeclarations}
            when verifyMIR do
                VerifyMIR.verify mirProgram >>= \case
                    [] -> pure ()
                    errors -> for_ errors \error -> do
                        -- TODO: make this more configurable than logging straight to stderr
                        let ?config = Pretty.defaultPrettyANSIIConfig
                        Pretty.eprintANSII (keyword "MIR VERIFICATION ERROR: " <> error)

            llvmModule <- MIRToLLVM.compile mirProgram
            debugEmit llvmModule

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
        DefineExternalFunction{type_ = newTypeSignature} -> Diff.diff oldTypeSignature newTypeSignature
        DefineVariantType{} -> True
    DefineVariantType{} -> undefined
    DefineExternalFunction{type_ = oldTypeSignature} -> case new.syntax of
        DefineExternalFunction{type_ = newTypeSignature} -> Diff.diff oldTypeSignature newTypeSignature
        DefineFunction{typeSignature = newTypeSignature} -> Diff.diff oldTypeSignature newTypeSignature
        DefineVariantType{} -> True

rename :: (Driver es) => DeclarationName -> Eff es ()
rename name = do
    previous <- getLastKnownRenamed name

    parsed <- GraphPersistence.getParsed name
    (renamed, errors, dependencies) <- Rename.rename parsed
    trace Dependencies (pretty name <> keyword " —> " <> Pretty.lparen "[" <> Pretty.intercalateDoc (keyword ", ") (map pretty (toList dependencies)) <> Pretty.rparen "]")

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

buildFilePath :: (Driver es) => FilePath -> Eff es FilePath
buildFilePath localPath = do
    MkBuildConfig{projectRoot} <- ask
    pure $ projectRoot </> ".vega" </> localPath

writeBuildFile :: (Driver es) => FilePath -> Text -> Eff es ()
writeBuildFile localPath contents = do
    MkBuildConfig{projectRoot} <- ask
    createDirectoryIfMissing False (projectRoot </> ".vega")

    filePath <- buildFilePath localPath

    createDirectoryIfMissing True (takeDirectory filePath)
    writeFileText filePath contents
