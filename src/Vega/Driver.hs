{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Vega.Driver (
    rebuild,
    execute,
    CompilationResult (..),
    DriverConfig (..),
    Monomorphized (..),
) where

-- TODO: check that imports make sense somewhere
-- TODO: diff imports and invalidate all declarations if they changed
-- TODO: check file modifications to avoid having to diff every module every time
-- TODO: remove modules if their files are deleted
-- TODO: catch duplicate declarations (in the parser i guess??)

import Relude hiding (NonEmpty, Reader, ask, readFile, trace, writeFile)

import Effectful
import Effectful.FileSystem (FileSystem, createDirectoryIfMissing, doesDirectoryExist, findExecutable, listDirectory, removeFile)
import Effectful.Reader.Static

import Data.FileEmbed (embedFile)
import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Traversable (for)
import Data.Yaml qualified as Yaml
import Effectful.Concurrent (Concurrent, forkIO, threadDelay)
import Effectful.Error.Static (Error, runErrorNoCallStack, throwError_)
import Effectful.Exception (evaluate, try)
import Effectful.Process (Process, callProcess, runProcess)
import LLVM.Core qualified as LLVM
import LLVM.Internal.Wrappers (CodeModel (CodeModelDefault), RelocMode (RelocDefault))
import LLVM.Internal.Wrappers qualified as LLVM
import LLVM.Target qualified
import Streaming.Prelude qualified as Streaming
import System.Directory.OsPath qualified as OsPathDirectory
import System.File.OsPath (readFile, readFile', writeFile)
import System.IO.Unsafe (unsafePerformIO)
import System.OsPath (OsPath, osp, (</>))
import System.OsPath qualified as OsPath
import TextBuilder qualified
import Vega.Builtins qualified as Builtins
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.Core.VegaToCore qualified as VegaToCore
import Vega.Compilation.JavaScript.Assemble (assembleFromEntryPoint)
import Vega.Compilation.JavaScript.CoreToJavaScript qualified as JavaScript
import Vega.Compilation.JavaScript.Syntax qualified as JavaScript.Syntax
import Vega.Compilation.LLVM.MIRToLLVM qualified as MIRToLLVM
import Vega.Compilation.MIR.CoreToMIR qualified as CoreToMIR
import Vega.Compilation.MIR.Monomorphize qualified as Monomorphize
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Compilation.MIR.Verify qualified as VerifyMIR
import Vega.Diff (DiffChange (..))
import Vega.Diff qualified as Diff
import Vega.Effect.DebugEmit (DebugEmit, debugEmit)
import Vega.Effect.GraphPersistence (GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Effect.Output.Static.Local (Output, output, runOutputList, runOutputSeq)
import Vega.Effect.Trace (Category (..), Trace, trace, traceEnabled, whenTraceEnabled)
import Vega.Effect.Unique.Static.Local (runNewUnique)
import Vega.Error (CompilationError (..), RenameErrorSet (..))
import Vega.Error qualified as Error
import Vega.Lexer qualified as Lexer
import Vega.Package (Dependency (..), PackageConfig)
import Vega.Package qualified as Package
import Vega.Panic (panic)
import Vega.Parser qualified as Parser
import Vega.Pretty (keyword, pretty)
import Vega.Pretty qualified as Pretty
import Vega.Rename qualified as Rename
import Vega.Runtime (runtimeArchive)
import Vega.Seq.NonEmpty (NonEmpty, pattern NonEmpty)
import Vega.Syntax
import Vega.TypeCheck qualified as TypeCheck
import Vega.Util (decodeOsPathUnchecked, viaList)

data CompilationResult
    = CompilationSuccessful
    | CompilationFailed
        {errors :: Seq CompilationError}

data DriverConfig = MkDriverConfig
    { verifyMIR :: Bool
    , linker :: Text
    }

-- TODO: distinguish between new and repeated errors
type Driver es =
    ( ?mainPackage :: PackageConfig
    , Reader DriverConfig :> es
    , GraphPersistence :> es
    , IOE :> es
    , FileSystem :> es
    , Concurrent :> es
    , Trace :> es
    , DebugEmit (Seq Core.Declaration) :> es
    , DebugEmit (Seq MIR.Declaration) :> es
    , DebugEmit (Monomorphized MIR.Program) :> es
    , DebugEmit LLVM.Module :> es
    )

-- | Newtype wrapper so we can distinguish the two debug emits for MIR programs (pre and post monomorphization)
newtype Monomorphized a = MkMonomorphized a

findSourceFilesForPackage :: (Driver es) => PackageConfig -> Eff es (Seq OsPath)
findSourceFilesForPackage package = do
    go (Package.sourceDirectory package)
  where
    go path = do
        files <- liftIO $ OsPathDirectory.listDirectory path
        fold <$> for files \file -> do
            let filePath = path OsPath.</> file
            liftIO (OsPathDirectory.doesDirectoryExist filePath) >>= \case
                True -> go filePath
                False
                    | OsPath.takeExtension file == [osp|.vega|] -> pure [filePath]
                    | otherwise -> pure []

computeImportScope :: (Driver es, ?package :: PackageConfig) => Seq Import -> Eff es ImportScope
computeImportScope imports = do
    foldMapM toImportScope imports
  where
    -- TODO: allow importing from other packages without explicitly spelling out their module name
    resolveModuleName MkParsedModuleName{package, subModules} = case package of
        Nothing -> do
            let package = MkPackageName (Package.name ?package)
            pure (MkModuleName{package, subModules})
        Just package -> pure (MkModuleName{package, subModules})

    toImportScope = \case
        ImportUnqualified{moduleName, importedDeclarations} -> do
            moduleName <- resolveModuleName moduleName
            pure $
                MkImportScope
                    { unqualifiedImports =
                        fromList
                            [
                                ( moduleName
                                , viaList importedDeclarations
                                )
                            ]
                    , qualifiedImports = []
                    }
        ImportQualified{moduleName, importedAs} -> do
            moduleName <- resolveModuleName moduleName
            pure $
                MkImportScope
                    { unqualifiedImports = []
                    , qualifiedImports =
                        fromList
                            [ (importedAs, moduleName)
                            ]
                    }

parseAndDiff :: (Driver es, ?package :: PackageConfig, Error CompilationError :> es) => OsPath -> Eff es (Seq DiffChange)
parseAndDiff filePath = do
    let moduleName = Package.moduleNameForPath ?package filePath

    contents <- decodeUtf8 <$> liftIO (readFile filePath)
    tokens <- case Lexer.run filePath contents of
        Left error -> throwError_ (Error.LexicalError error)
        Right tokens -> pure tokens

    trace Tokens (pretty filePath <> ":\n  " <> Pretty.align (Pretty.intercalateDoc " " (fmap (\(token, _) -> pretty token) tokens)))

    parsedModule <- case Parser.parse moduleName filePath tokens of
        Left errors -> throwError_ (Error.ParseError errors)
        Right parsedModule -> pure parsedModule

    importScope <- computeImportScope parsedModule.imports
    trace ImportScope (keyword (toText (decodeOsPathUnchecked filePath)) <> ": " <> show importScope)

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

trackSourceChanges :: (Driver es) => PackageConfig -> Eff es (Seq CompilationError)
trackSourceChanges package = do
    let ?package = package
    sourceFiles <- findSourceFilesForPackage package
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
    remainingWorkItems <- GraphPersistence.getRemainingWork (Package.backend ?mainPackage)
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
        ((), dependencyErrors) <- runOutputSeq @CompilationError loadDependencies
        case dependencyErrors of
            NonEmpty _ -> pure (CompilationFailed{errors = dependencyErrors})
            Empty -> do
                parseErrors <- trackSourceChanges ?mainPackage

                performAllRemainingWork
                nonParseErrors <- GraphPersistence.getCurrentErrors
                case parseErrors <> nonParseErrors of
                    [] -> do
                        runErrorNoCallStack compileBackend >>= \case
                            Left error -> do
                                pure (CompilationFailed{errors = [DriverError error]})
                            Right () -> pure (CompilationSuccessful)
                    errors -> pure (CompilationFailed{errors = errors})

loadDependencies :: (Output CompilationError :> es, Driver es) => Eff es ()
loadDependencies = do
    -- TODO: this should let the backend decide how to load dependencies (or not) instead
    -- of always re-compiling them
    -- (TODO TODO: would this even rebuild them with a proper backend? maybe this does actually work)

    -- TODO: this doesn't work for transitive dependencies.
    -- We either need to compute the transitive closure here or
    -- process packages' dependencies recursively
    -- (probably the first since we will also need to resolve module versions once we go beyond
    -- simple local dependencies)
    for_ (Package.dependencies ?mainPackage) \case
        LocalDependency{src} -> do
            trace Driver ("Loading local dependency from " <> pretty src)
            let filePath = src </> [osp|vega.yaml|]
            Package.parseConfigFile filePath >>= \case
                Left parseError -> do
                    trace Driver (Pretty.errorText "Unable to parse package config")
                    output (Error.DriverError (Error.UnableToParsePackageConfig filePath parseError))
                Right dependency -> do
                    errors <- trackSourceChanges dependency
                    for_ errors \error -> output (DependencyError{dependencyName = Package.name dependency, error})
    trace Driver "Finished loading dependencies"

compileBackend :: (Error Error.DriverError :> es, Driver es) => Eff es ()
compileBackend = do
    let entryPoint = Package.entryPoint ?mainPackage

    -- TODO: check that the entry point has the right type
    entryPointDeclaration <-
        GraphPersistence.getDefiningDeclaration entryPoint >>= \case
            Just declaration -> pure declaration
            Nothing -> throwError_ (Error.EntryPointNotFound entryPoint)

    case Package.backend ?mainPackage of
        Package.JavaScript -> do
            jsCode <- assembleFromEntryPoint entryPoint

            outputFile <- Package.ensureJavascriptOutputFile ?mainPackage
            liftIO $ writeFile outputFile (encodeUtf8 (TextBuilder.toText jsCode))
        Package.NativeRelease -> runNewUnique do
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

            let reachableStream = GraphPersistence.reachableFrom ([entryPointDeclaration] <> Builtins.wiredInDeclarations)

            traceEnabled Reachable >>= \case
                False -> pure ()
                True -> Streaming.mapM_ (\declarationName -> trace Reachable (pretty declarationName)) reachableStream

            let toHashMap declarations =
                    HashMap.fromList $ mconcat $ fmap (\seq -> fmap (\declaration -> (declaration.name, declaration)) (toList seq)) declarations
            mirDeclarations <- toHashMap <$> Streaming.toList_ (Streaming.mapM compileToMIR reachableStream)

            let mirProgram = MIR.MkProgram{declarations = mirDeclarations}

            monomorphizedMIRProgram <- Monomorphize.monomorphize mirProgram entryPoint
            debugEmit (MkMonomorphized monomorphizedMIRProgram)

            -- TODO: it might be nice to verify the non-monomorphized MIR (especially since that is what we're logging)
            when verifyMIR do
                VerifyMIR.verify monomorphizedMIRProgram >>= \case
                    [] -> pure ()
                    errors -> for_ errors \error -> do
                        -- TODO: make this more configurable than logging straight to stderr
                        let ?config = Pretty.defaultPrettyANSIIConfig
                        Pretty.eprintANSII (Pretty.errorText "MIR VERIFICATION ERROR: " <> error)

            context <- LLVM.contextCreate
            let ?context = context
            llvmModule <- MIRToLLVM.compile monomorphizedMIRProgram
            MIRToLLVM.addMainFunction entryPoint llvmModule
            debugEmit llvmModule

            LLVM.initializeNativeTarget >>= \case
                False -> pure ()
                True -> panic "Unable to initialize native target in LLVM"
            LLVM.Target.initializeNativeAsmPrinter >>= \case
                False -> pure ()
                True -> panic "Unable to initialize native asm printer in LLVM"

            -- TODO: for now we're just building for the host machine.
            -- we will eventually want to make this configurable
            triple <- LLVM.Target.getDefaultTargetTriple
            target <- LLVM.Target.getTargetFromTriple triple

            targetMachineOptions <- LLVM.Target.createTargetMachineOptions

            targetMachine <-
                LLVM.Target.createTargetMachineWithOptions target triple targetMachineOptions >>= \case
                    Nothing -> panic "Unable to create LLVM target machine"
                    Just targetMachine -> pure targetMachine

            dataLayout <- LLVM.Target.createTargetDataLayout targetMachine
            LLVM.setTarget llvmModule triple
            LLVM.Target.setModuleDataLayout llvmModule dataLayout

            {-# SCC "LLVM.verifyModule" #-} LLVM.verifyModule llvmModule

            -- TODO: move this behind a flag
            -- LLVM.Target.targetMachineEmitToFile targetMachine llvmModule [osp|out.s|] LLVM.Target.AssemblyFile

            -- TODO: be smarter about where to put the output
            {-# SCC "LLVM.Target.targetMachineEmitToFile" #-} LLVM.Target.targetMachineEmitToFile targetMachine llvmModule [osp|out.o|] LLVM.Target.ObjectFile

            MkDriverConfig{linker} <- ask
            linkerCommand <- case linker of
                "auto" -> findLinker
                path -> pure $ toString path

            -- TODO: put this somewhere more sensible
            writeFileBS "libvega_runtime.a" runtimeArchive

            {-# SCC "linker" #-} runProcess $ callProcess linkerCommand ["out.o", "libvega_runtime.a"]
            removeFile "out.o"
            removeFile "libvega_runtime.a"
        _ -> undefined

execute :: FilePath -> Text -> Eff es ()
execute = undefined

findLinker :: (FileSystem :> es, Error Error.DriverError :> es) => Eff es FilePath
findLinker = do
    findExecutable "clang" >>= \case
        Just path -> pure path
        Nothing ->
            findExecutable "gcc" >>= \case
                Just path -> pure path
                Nothing -> throwError_ $ Error.NoLinkerFound

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
    GraphPersistence.getCompiledCore name >>= \case
        -- TODOOOO
        Missing{} -> pure () -- error $ "missing typed in compilation to JS: " <> show name
        Ok core -> do
            statements <- fold <$> for core JavaScript.compileDeclaration
            let rendered = TextBuilder.toText $ JavaScript.Syntax.renderStatements $ toList statements
            GraphPersistence.setCompiledJS name rendered

compileToCore :: (Driver es) => DeclarationName -> Eff es ()
compileToCore name =
    GraphPersistence.getTyped name >>= \case
        Missing{} -> pure ()
        Failed{} -> pure ()
        Ok typedDeclaration -> do
            compiled <- VegaToCore.compileDeclaration typedDeclaration
            debugEmit compiled
            GraphPersistence.setCompiledCore name compiled
