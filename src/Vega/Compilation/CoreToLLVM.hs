{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE ImplicitParams #-}
-- Workaround for https://gitlab.haskell.org/ghc/ghc/-/issues/20630 since we use
-- ImplicitParams with do blocks quite a lot here and we don't actually need ApplicativeDo
{-# LANGUAGE NoApplicativeDo #-}

module Vega.Compilation.CoreToLLVM where

import Relude

import Effectful (Eff, IOE, (:>))
import LLVM.Core qualified as LLVM
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Syntax qualified as Vega

type Compile es = (?context :: LLVM.Context, IOE :> es)

compile :: (IOE :> es) => Seq (Core.Declaration) -> Eff es LLVM.Module
compile declarations = do
    context <- liftIO LLVM.contextCreate
    let ?context = context
    module_ <- liftIO $ LLVM.moduleCreateWithName "idkwhattoputhereyet"
    for_ declarations \declaration -> do
        compileDeclaration module_ declaration
    pure module_

compileDeclaration :: (Compile es) => LLVM.Module -> Core.Declaration -> Eff es ()
compileDeclaration module_ = \case
    Core.DefineFunction
        { name
        , representationParameters
        , parameters
        , returnRepresentation
        , statements
        , result
        } -> do
            undefined

data Layout = MkLayout
    { size :: Int
    , alignment :: Int
    , llvmType :: LLVM.Type
    }

representationLayout :: (Compile es) => Core.Representation -> Eff es Layout
representationLayout = \case
    Core.PrimitiveRep primitive -> case primitive of
        Vega.IntRep -> pure (MkLayout{size = 8, alignment = 8, llvmType = LLVM.int64Type})
        Vega.BoxedRep -> pure (MkLayout {size = 8, alignment = 8, llvmType = LLVM.pointerType})
        _ -> undefined
    _ -> undefined
