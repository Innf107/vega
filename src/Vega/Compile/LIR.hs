module Vega.Compile.LIR (
    Program (..),
    Block (..),
    Instruction (..),
    Target,
    Source (..),
    FunctionDefinition (..),
    Terminator (..),
) where

import Vega.Prelude

import Vega.Name

data Program = MkProgram
    { blocks :: Map Name Block
    , globalsWithInitializers :: Map Name (Seq Instruction)
    }

data Block = MkBlock {instructions :: Seq Instruction, terminator :: Terminator, arguments :: Seq Name}

type Target = Name

data Source
    = Var Name
    | ImmediateInt Int

data Instruction
    = Mov Target Source
    | Add Target Source Source
    | Allocate Target Int
    | AllocateClosure
        { target :: Target
        , function :: FunctionDefinition
        , size :: Int
        }
    | WriteField Target Int Source
    | ReadField Target Int Source

data Terminator
    = Return Source
    | -- | Directly call a known function and write the returned valued to `target`.
      -- This will *NOT* perform any arity checks and assumes that the arguments match the target exactly.
      CallDirect {target :: Target, function :: Name, arguments :: Vector Source, cont :: Maybe Block}
    | -- | Call a function through a closure and write the returned value to `target`.
      -- This will check the arity and convert to closures or iteratively call on overapplication.
      CallIndirect {target :: Target, closureSource :: Source, arguments :: Vector Source, cont :: Maybe Block}
    | CaseInt {target :: Target, cases :: Vector (Int, Block), default_ :: Block}
    | CaseConstructor {target :: Target, cases :: Vector (Int, Block), default_ :: Block}

data FunctionDefinition = MkFunctionDefinition
    { arity :: Int
    , block :: Name
    }