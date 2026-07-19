{-# LANGUAGE CApiFFI #-}
module Vega.Compilation.LLVM.ShadowStack (runShadowStackPass) where

import Relude

-- We need to import the internal MkModule constructor here to be able to pass a module to FFI
import LLVM.Internal.Wrappers (Module (MkModule))
import LLVM.Core qualified as LLVM
import Foreign (Ptr)

foreign import ccall unsafe "RunShadowStackPass"
    runShadowStackPass :: LLVM.Module -> IO ()
