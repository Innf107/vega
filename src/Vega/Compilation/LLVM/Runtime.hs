module Vega.Compilation.LLVM.Runtime (declareRuntimeDefinitions, RuntimeDefinitions (..)) where

import Relude

import LLVM.Core qualified as LLVM

data RuntimeDefinitions = MkRuntimeDefinitions
    { vega_allocate_boxed :: (LLVM.Value, LLVM.FunctionType)
    }

declareRuntimeDefinitions :: (MonadIO io, ?context :: LLVM.Context) => LLVM.Module -> io RuntimeDefinitions
declareRuntimeDefinitions module_ = do
    let vega_allocate_boxed_type = LLVM.functionType [LLVM.pointerType] LLVM.pointerType False
    vega_allocate_boxed <- LLVM.addFunction module_ "vega_allocate_boxed" vega_allocate_boxed_type

    pure
        ( MkRuntimeDefinitions
            { vega_allocate_boxed = (vega_allocate_boxed, vega_allocate_boxed_type)
            }
        )
