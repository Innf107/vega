module Vega.Compilation.LLVM.Runtime (declareRuntimeDefinitions, RuntimeDefinitions (..)) where

import Relude

import LLVM.Core qualified as LLVM
import Vega.Compilation.LLVM.AttributeFunctionType (AttributeFunctionType, attributeFunctionType, addFunctionWithAttributes)

data RuntimeDefinitions = MkRuntimeDefinitions
    { vega_allocate_boxed :: (LLVM.Value, AttributeFunctionType)
    , vega_debug_int :: (LLVM.Value, AttributeFunctionType)
    }

declareRuntimeDefinitions :: (MonadIO io, ?context :: LLVM.Context) => LLVM.Module -> io RuntimeDefinitions
declareRuntimeDefinitions module_ = do
    let vega_allocate_boxed_type = attributeFunctionType [(LLVM.pointerType, [])] (LLVM.pointerType, [])
    vega_allocate_boxed <- addFunctionWithAttributes module_ "vega_allocate_boxed" vega_allocate_boxed_type

    let vega_debug_int_type = attributeFunctionType [(LLVM.int64Type, [])] (LLVM.voidType, [])
    vega_debug_int <- addFunctionWithAttributes module_ "vega_debug_int" vega_debug_int_type

    pure
        ( MkRuntimeDefinitions
            { vega_allocate_boxed = (vega_allocate_boxed, vega_allocate_boxed_type)
            , vega_debug_int = (vega_debug_int, vega_debug_int_type)
            }
        )
