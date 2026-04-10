module Vega.Compilation.LLVM.Runtime (declareRuntimeDefinitions, RuntimeDefinitions (..)) where

import Relude

import LLVM.Core qualified as LLVM
import Vega.Compilation.LLVM.AttributeFunctionType (AttributeFunctionType, attributeFunctionType, addFunctionWithAttributes)

data RuntimeDefinitions = MkRuntimeDefinitions
    { vega_allocate_boxed :: (LLVM.Value, AttributeFunctionType)
    }

declareRuntimeDefinitions :: (MonadIO io, ?context :: LLVM.Context) => LLVM.Module -> io RuntimeDefinitions
declareRuntimeDefinitions module_ = do
    let vega_allocate_boxed_type = attributeFunctionType [(LLVM.pointerType, [])] (LLVM.pointerType, [])
    vega_allocate_boxed <- addFunctionWithAttributes module_ "vega_allocate_boxed" vega_allocate_boxed_type

    pure
        ( MkRuntimeDefinitions
            { vega_allocate_boxed = (vega_allocate_boxed, vega_allocate_boxed_type)
            }
        )
