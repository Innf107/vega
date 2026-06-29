module Vega.Compilation.LLVM.Runtime (declareRuntimeDefinitions, RuntimeDefinitions (..)) where

import Relude

import LLVM.Core qualified as LLVM
import Vega.Compilation.LLVM.AttributeFunctionType (AttributeFunctionType, addFunctionWithAttributes, attributeFunctionType)
import qualified Vega.Compilation.LLVM.Layout as Layout

data RuntimeDefinitions = MkRuntimeDefinitions
    { vega_allocate_boxed :: (LLVM.Value, AttributeFunctionType)
    , vega_allocate_uninitialized_array :: (LLVM.Value, AttributeFunctionType)
    , vega_allocate_zero_initialized_array :: (LLVM.Value, AttributeFunctionType)
    , vega_debug_int :: (LLVM.Value, AttributeFunctionType)
    , vega_errno :: (LLVM.Value, AttributeFunctionType)
    }

declareRuntimeDefinitions :: (MonadIO io, ?context :: LLVM.Context) => LLVM.Module -> io RuntimeDefinitions
declareRuntimeDefinitions module_ = do
    let vega_allocate_boxed_type = attributeFunctionType [(LLVM.pointerType, [])] (Layout.boxedPointerType, [])
    vega_allocate_boxed <- addFunctionWithAttributes module_ "vega_allocate_boxed" vega_allocate_boxed_type

    let vega_debug_int_type = attributeFunctionType [(LLVM.int64Type, [])] (LLVM.voidType, [])
    vega_debug_int <- addFunctionWithAttributes module_ "vega_debug_int" vega_debug_int_type

    let vega_allocate_uninitialized_array_type = attributeFunctionType [(LLVM.pointerType, []), (LLVM.int64Type, [])] (Layout.boxedPointerType, [])
    vega_allocate_uninitialized_array <- addFunctionWithAttributes module_ "vega_allocate_uninitialized_array" vega_allocate_uninitialized_array_type

    let vega_allocate_zero_initialized_array_type = attributeFunctionType [(LLVM.pointerType, []), (LLVM.int64Type, [])] (Layout.boxedPointerType, [])
    vega_allocate_zero_initialized_array <- addFunctionWithAttributes module_ "vega_allocate_zero_initialized_array" vega_allocate_uninitialized_array_type

    let vega_errno_type = attributeFunctionType [] (LLVM.int32Type, [])
    vega_errno <- addFunctionWithAttributes module_ "vega_errno" vega_errno_type

    pure
        ( MkRuntimeDefinitions
            { vega_allocate_boxed = (vega_allocate_boxed, vega_allocate_boxed_type)
            , vega_allocate_uninitialized_array = (vega_allocate_uninitialized_array, vega_allocate_uninitialized_array_type)
            , vega_allocate_zero_initialized_array = (vega_allocate_zero_initialized_array, vega_allocate_zero_initialized_array_type)
            , vega_debug_int = (vega_debug_int, vega_debug_int_type)
            , vega_errno = (vega_errno, vega_errno_type)
            }
        )
