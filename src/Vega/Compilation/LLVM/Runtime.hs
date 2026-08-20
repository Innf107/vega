module Vega.Compilation.LLVM.Runtime (declareRuntimeDefinitions, RuntimeDefinitions (..), Definition (..)) where

import Relude

import LLVM.Core qualified as LLVM
import Vega.Compilation.LLVM.AttributeFunctionType (AttributeFunctionType, addFunctionWithAttributes, attributeFunctionType)
import Vega.Compilation.LLVM.Layout qualified as Layout

data Definition = MkDefinition
    { value :: LLVM.Value
    , type_ :: AttributeFunctionType
    , -- Functions that are safe points are special in two ways
      -- 1) they are passed the shadow stack pointer
      -- 2) they are marked with the (fake) vegagc gc strategy so that the
      -- shadow stack pass preserves all pointers that are live across it.
      --
      -- Every vega function is a safe point, but many runtime functions are not and
      -- don't need to pessimize the shadow stack generation
      isSafepoint :: Bool
    }

data RuntimeDefinitions = MkRuntimeDefinitions
    { vega_allocate_boxed :: Definition
    , vega_allocate_uninitialized_array :: Definition
    , vega_allocate_zero_initialized_array :: Definition
    , vega_debug_int :: Definition
    , vega_debug_stack_roots :: Definition
    , vega_errno :: Definition
    }

defineFunction :: (MonadIO io) => LLVM.Module -> Text -> Bool -> AttributeFunctionType -> io Definition
defineFunction module_ name isSafepoint type_ = do
    value <- addFunctionWithAttributes module_ name type_
    when isSafepoint do
        LLVM.setGC value "vegagc"
    pure (MkDefinition{value, type_, isSafepoint})

declareRuntimeDefinitions :: (MonadIO io, ?context :: LLVM.Context) => LLVM.Module -> io RuntimeDefinitions
declareRuntimeDefinitions module_ = do
    vega_allocate_boxed <- defineFunction module_ "vega_allocate_boxed" True $ attributeFunctionType [(LLVM.pointerType, []), (LLVM.pointerType, [])] (Layout.boxedPointerType, [])

    vega_allocate_uninitialized_array <- defineFunction module_ "vega_allocate_uninitialized_array" True $ attributeFunctionType [(LLVM.pointerType, []), (LLVM.pointerType, []), (LLVM.int64Type, [])] (Layout.boxedPointerType, [])

    vega_allocate_zero_initialized_array <- defineFunction module_ "vega_allocate_zero_initialized_array" True $ attributeFunctionType [(LLVM.pointerType, []), (LLVM.pointerType, []), (LLVM.int64Type, [])] (Layout.boxedPointerType, [])

    vega_debug_int <- defineFunction module_ "vega_debug_int" False $ attributeFunctionType [(LLVM.int64Type, [])] (LLVM.voidType, [])

    vega_debug_stack_roots <- defineFunction module_ "vega_debug_stack_roots" True $ attributeFunctionType [(LLVM.pointerType, [])] (LLVM.voidType, [])

    vega_errno <- defineFunction module_ "vega_errno" False $ attributeFunctionType [] (LLVM.int32Type, [])

    pure
        ( MkRuntimeDefinitions
            { vega_allocate_boxed
            , vega_allocate_uninitialized_array
            , vega_allocate_zero_initialized_array
            , vega_debug_int
            , vega_debug_stack_roots
            , vega_errno
            }
        )
