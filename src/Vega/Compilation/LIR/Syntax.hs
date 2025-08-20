module Vega.Compilation.LIR.Syntax (
    Program (..),
    LocalVariable (..),
    Declaration (..),
    Block (..),
    BlockDescriptor (..),
    Instruction (..),
    Terminator (..),
    Value (..),
    Layout (MkLayout, MkLayoutUnchecked),
) where

import Data.Sequence (Seq (..))
import GHC.Num (integerLog2)
import Relude
import Prelude (log)

-- TODO: move this somewhere else
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Effect.Unique.Static.Local (Unique)

newtype LocalVariable = MkVariable Int

data FunctionName

data Program = MkProgram
    { declarations :: Seq Declaration
    }

data Declaration = DefineFunction
    { name :: CoreName
    , parameters :: Seq LocalCoreName
    , locals :: HashMap LocalCoreName Layout
    , init :: BlockDescriptor
    , blocks :: HashMap BlockDescriptor Block
    }

newtype BlockDescriptor = MkBlockDescriptor Unique
    deriving stock (Generic)
    deriving newtype (Eq, Hashable)

data Block = MkBlock
    { arguments :: Seq LocalCoreName
    , instructions :: Seq Instruction
    , terminator :: Terminator
    }

data Instruction
    = Add LocalVariable LocalVariable LocalVariable
    | Allocate LocalCoreName Layout
    | AllocateClosure LocalCoreName FunctionName (Seq LocalVariable)
    | Store
        { pointer :: LocalVariable
        , value :: LocalVariable
        , offset :: Int
        }

data Value
    = Var CoreName
    | Literal Core.Literal

data Terminator
    = Return Value
    | Jump BlockDescriptor (Seq Value)
    | CallDirect LocalVariable FunctionName (Seq LocalVariable) BlockDescriptor
    | CallIndirect LocalVariable LocalVariable (Seq LocalVariable) BlockDescriptor
    | TailCallDirect CoreName (Seq Value)
    | TailCallIndirect LocalVariable (Seq LocalVariable)

data LayoutStructure
    = IntLayout
    | PointerLayout
    | -- | INVARIANT: the elements are correctly aligned
      ProductLayout (Seq Layout)
    | TagLayout {numberOfTags :: Int}
    | -- INVARIANT: all elements have the same size
      UnionLayout (Seq Layout)
    | Padding {bits :: Int}

data Layout = MkLayoutUnchecked
    { structure :: LayoutStructure
    , size :: ~Int
    , alignment :: ~Int
    }

pattern MkLayout :: LayoutStructure -> Layout
pattern MkLayout structure <- MkLayoutUnchecked{structure}
    where
        MkLayout structure = MkLayoutUnchecked{structure, size = computeSize structure, alignment = computeAlignment structure}
{-# COMPLETE MkLayout #-}

-- | The size of a layout in bits
computeSize :: LayoutStructure -> Int
computeSize = \case
    IntLayout -> 64
    PointerLayout -> 64
    ProductLayout elements -> case elements of
        Empty -> 0
        _ -> do
            let go currentExactSize = \case
                    Empty -> undefined
                    layout :<| rest -> do
                        undefined

            undefined
    TagLayout{numberOfTags} -> closestPowerOf2 numberOfTags
    UnionLayout variants -> do
        -- We use the invariant that all elements have the same size
        case variants of
            Empty -> 0
            (layout :<| _) -> do
                layout.size
    Padding bits -> bits

computeAlignment :: LayoutStructure -> Int
computeAlignment = \case
    IntLayout -> 64
    PointerLayout -> 64
    ProductLayout elements -> case elements of
        Empty -> 0
        _ -> undefined
    _ -> undefined

closestPowerOf2 :: (HasCallStack) => Int -> Int
closestPowerOf2 n = 2 ^ (ceiling (log (fromIntegral n) / log 2))
