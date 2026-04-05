{- | These definitions follow runtime/src/heap.rs and are mostly necessary since we need to
generate some runtime objects (in particular info tables) at compile time
-}
module Vega.Compilation.LLVM.Runtime.Heap where

import Data.Word (Word64)
import GHC.Generics (Generic)
import Vega.Compilation.LLVM.Runtime.Serialize (CEnum (..), CStruct (..), CUnion (..), Serialize)

data InfoTable = MkInfoTable
    { objectType :: ObjectType
    , layout :: Layout
    }
    deriving stock (Generic)
    deriving (Serialize) via CStruct InfoTable

data ObjectType
    = Boxed
    | Array
    deriving stock (Generic)
    deriving (Serialize) via CEnum ObjectType

data Layout
    = BoxedLayout BoxedLayout
    | ArrayLayout ArrayLayout
    deriving stock (Generic)
    deriving (Serialize) via CUnion Layout

data BoxedLayout = MkBoxedLayout
    { -- This is technically a CSize in the runtime but that's a CSize in the *target*, not in
      -- the compiler. So to do this properly, we would need to thread the information about
      -- the target through serialization.
      -- For now, we just assume that all ints are 64 bit on the target platform.
      sizeInBytes :: Word64
    , boxedCount :: Word64
    }
    deriving stock (Generic)
    deriving (Serialize) via CStruct BoxedLayout

data ArrayLayout = MkArrayLayout
    { sizeInElements :: Word64
    , elementStrideInBytes :: Word64
    , elementBoxedCount :: Word64
    }
    deriving stock (Generic)
    deriving (Serialize) via CStruct ArrayLayout
