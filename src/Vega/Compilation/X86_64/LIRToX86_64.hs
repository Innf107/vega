module Vega.Compilation.X86_64.LIRToX86_64 (compile) where

import Effectful
import Relude

import Vega.Compilation.LIR.Syntax qualified as LIR
import Vega.Compilation.X86_64.Syntax qualified as X86
import Data.Traversable (for)

type Compile es = () :: Constraint

compile :: (Compile es) => Seq LIR.Declaration -> Eff es X86.Program
compile declarations = do
    instructions <- fold <$> traverse compileDeclaration declarations
    pure
        ( X86.MkProgram
            { textSegment = instructions
            }
        )

compileDeclaration :: LIR.Declaration -> Eff es (Seq X86.Instruction)
compileDeclaration = \case
    LIR.DefineFunction
        { name
        , parameters
        , layouts
        , init
        , blocks
        } -> do
            fold <$> for blocks compileBlock

compileBlock :: LIR.Block -> Eff es (Seq X86.Instruction)
compileBlock block = do
    -- TODO: something something bb arguments
    registerMappings <- registerAllocation block
    instructions <- fold <$> for block.instructions (compileInstruction registerMappings)
    terminatorInstructions <- compileTerminator block.terminator
    pure (instructions <> terminatorInstructions)

compileInstruction :: HashMap LIR.Variable RegisterMapping -> LIR.Instruction -> Eff es (Seq X86.Instruction)
compileInstruction registerMappings = \case
    _ -> undefined

compileTerminator :: LIR.Terminator -> Eff es (Seq X86.Instruction)
compileTerminator = undefined

data RegisterMapping
    = PhysicalRegister X86.Register
    | SpilledToStack

registerAllocation :: LIR.Block -> Eff es (HashMap LIR.Variable RegisterMapping)
registerAllocation = pure undefined
