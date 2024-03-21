module Vega.Compile.X86_64 (Program (..), Register (..), Instruction (..), DataDefinition (..)) where

import Vega.Prelude

import Vega.Name

data Program = MkProgram
    { instructions :: Seq Instruction
    , data_ :: Seq (Name, Seq DataDefinition)
    }

data Register = RAX | RBX | RCX | RDX | RBP | RSI | RDI | RSP | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 | RIP

-- | Instructions are given in Intel argument order, so e.g. Mov RAX RBX will copy the value in RBX to RAX
data Instruction
    = Label Text
    | SubLabel Text
    | Mov Register Register
    | Add Register Register
    | Jmp Text

data DataDefinition
    = Times Int DataDefinition
    | DQ Int
    | DB Int
    | DW Int

renderNASM :: Program -> Text
renderNASM program = undefined
