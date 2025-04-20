module Vega.Compilation.LIR (
    Program (..),
    LocalVariable (..),
    Declaration (..),
    Block (..),
    Instruction (..),
    Terminator (..),
) where

import Relude
import Vega.Compilation.Shape (Shape (..))

newtype LocalVariable = MkVariable Int

data FunctionName

data Program = MkProgram
    { declarations :: Seq Declaration
    }

data Declaration = Function
    { name :: FunctionName
    , arguments :: Seq Shape
    , init :: Block
    }

data Block = MkBlock
    { instructions :: Seq Instruction
    , terminator :: Terminator
    }

data Instruction
    = Add LocalVariable LocalVariable LocalVariable
    | Allocate LocalVariable Shape
    | AllocateClosure LocalVariable FunctionName (Seq LocalVariable)
    | Store
        { pointer :: LocalVariable
        , value :: LocalVariable
        , offset :: Int
        }

data Terminator
    = Return LocalVariable
    | CallDirect LocalVariable FunctionName (Seq LocalVariable) Block
    | CallIndirect LocalVariable LocalVariable (Seq LocalVariable) Block
    | TailCallDirect FunctionName (Seq LocalVariable)
    | TailCallIndirect LocalVariable (Seq LocalVariable)
