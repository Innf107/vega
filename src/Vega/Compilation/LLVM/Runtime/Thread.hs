module Vega.Compilation.LLVM.Runtime.Thread (threadStateAllocationPointerOffset, threadStateAllocationLimitOffset) where

import Relude (Int)

threadStateAllocationPointerOffset :: Int
threadStateAllocationPointerOffset = 8

threadStateAllocationLimitOffset :: Int
threadStateAllocationLimitOffset = 16
