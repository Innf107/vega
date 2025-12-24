module Vega.Compilation.X86_64.LIRToX86_64 (compile) where

import Effectful
import Relude

import Vega.Compilation.LIR.Syntax qualified as LIR
import Vega.Compilation.X86_64.Syntax qualified as X86

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
            undefined
