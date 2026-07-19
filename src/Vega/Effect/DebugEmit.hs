{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Vega.Effect.DebugEmit (
    DebugEmit,
    debugEmit,
    debugEmitLLVM,
    debugEmitMIR,
    debugEmitIncrementalMIR,
    debugEmitBytes,
    EmitConfig (..),
    Category (..),
    isCategoryEnabled,
    outputFile,
    runDebugEmit,
) where

import Data.ByteString qualified as ByteString
import Data.HashMap.Strict qualified as HashMap
import Effectful
import Effectful.Dispatch.Static
import Effectful.FileSystem.IO (runFileSystem, withBinaryFile)
import Effectful.TH (makeEffect)
import LLVM.Core qualified as LLVM
import Relude
import System.Directory.OsPath (removeFile, doesFileExist)
import System.File.OsPath (appendFile')
import System.OsPath (OsPath, osp)
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Pretty (Ann, Doc, PrettyANSIIConfig, eprintANSII)
import Vega.Pretty qualified as Pretty

data Category
    = Core
    | MIR
    | MonomorphizedMIR
    | LLVM
    | OptimizedLLVM
    | LLVMWithShadowStack
    | Assembly
    deriving (Enum, Bounded)

data EmitConfig = MkEmitConfig
    { core :: Bool
    , mir :: Bool
    , monomorphizedMIR :: Bool
    , llvm :: Bool
    , optimizedLLVM :: Bool
    , llvmWithShadowStack :: Bool
    , assembly :: Bool
    }

isCategoryEnabled :: (DebugEmit :> es) => Category -> Eff es Bool
isCategoryEnabled category = do
    DebugEmit config <- getStaticRep
    pure $ case category of
        Core -> config.core
        MIR -> config.mir
        MonomorphizedMIR -> config.monomorphizedMIR
        LLVM -> config.llvm
        OptimizedLLVM -> config.optimizedLLVM
        LLVMWithShadowStack -> config.llvmWithShadowStack
        Assembly -> config.assembly

outputFile :: Category -> OsPath
outputFile = \case
    Core -> [osp|core.vegacore|]
    MIR -> [osp|mir.vegamir|]
    MonomorphizedMIR -> [osp|monomorphized.vegamir|]
    LLVM -> [osp|llvm.ll|]
    OptimizedLLVM -> [osp|optimized.ll|]
    LLVMWithShadowStack -> [osp|shadow-stack.ll|]
    Assembly -> [osp|out.s|]

data DebugEmit :: Effect

type instance DispatchOf DebugEmit = Static WithSideEffects
data instance StaticRep DebugEmit = DebugEmit EmitConfig

-- These functions should all be inlined so that the printed argument can be moved into the branch and
-- doesn't need to allocate a thunk if the debug output is disabled

{-# INLINE debugEmit #-}
debugEmit :: (DebugEmit :> es) => Category -> Doc Ann -> Eff es ()
debugEmit category doc = debugEmitBytes category (encodeUtf8 $ Pretty.prettyPlain doc)

{-# INLINE debugEmitLLVM #-}
debugEmitLLVM :: (DebugEmit :> es) => Category -> LLVM.Module -> Eff es ()
debugEmitLLVM category module_ =
    isCategoryEnabled category >>= \case
        False -> pure ()
        True -> do
            unsafeEff_ $ LLVM.printModuleToFile module_ (outputFile category)

{-# INLINE debugEmitIncrementalMIR #-}
debugEmitIncrementalMIR :: (DebugEmit :> es) => Category -> Seq MIR.Declaration -> Eff es ()
debugEmitIncrementalMIR category declarations = debugEmit category (Pretty.intercalateDoc "\n\n" (fmap Pretty.pretty declarations))

{-# INLINE debugEmitMIR #-}
debugEmitMIR :: (DebugEmit :> es) => Category -> MIR.Program -> Eff es ()
debugEmitMIR category (MIR.MkProgram declarations) = debugEmitIncrementalMIR category (fromList $ HashMap.elems declarations)

{-# INLINE debugEmitBytes #-}
debugEmitBytes :: (DebugEmit :> es) => Category -> ByteString -> Eff es ()
debugEmitBytes category ~bytestring =
    isCategoryEnabled category >>= \case
        False -> pure ()
        True -> do
            unsafeEff_ $ appendFile' (outputFile category) bytestring

runDebugEmit :: (IOE :> es) => EmitConfig -> Eff (DebugEmit : es) a -> Eff es a
runDebugEmit config cont = evalStaticRep (DebugEmit config) do
    -- We clear all enabled files first so that we can append to them without keeping their previous contents
    for_ (universe @Category) \category -> do
        enabled <- isCategoryEnabled category
        when enabled do
            fileExists <- liftIO $ doesFileExist (outputFile category)
            when fileExists do
                liftIO $ removeFile (outputFile category)
    cont
