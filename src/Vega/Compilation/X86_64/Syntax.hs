module Vega.Compilation.X86_64.Syntax (Program (..), Register (..), Instruction (..), renderASM) where

import Relude

import Data.Text qualified as Text
import TextBuilder (TextBuilder)
import TextBuilder qualified
import Vega.Syntax (GlobalName (..), ModuleName (..), renderModuleName)

data Register
    = RAX
    | RBX
    | RCX
    | RDX
    | RSI
    | RDI
    | RSP
    | RBP
    | R8
    | R9
    | R10
    | R11
    | R12
    | R13
    | R14
    | R15

data Instruction
    = NOP
    | Label Text

data Program = MkProgram
    { textSegment :: Seq Instruction
    }

-- TODO: We can probably be much more efficient than outputting text into memory here.
-- 1) we can output directly (but buffered) into a file, skipping the internal builder structure
-- 2) we can use ByteString instead of Text to skip Utf-8 overhead
renderASM :: GlobalName -> Program -> Text
renderASM entryPoint program = TextBuilder.toText do
    TextBuilder.intercalate @[] "\n" $
        [ ".global main"
        , "main:"
        , "  call " <> compileGlobalName entryPoint
        , "  xor %rax, %rax"
        , "  ret"
        ]
            <> map renderInstruction (toList program.textSegment)

renderInstruction :: Instruction -> TextBuilder
renderInstruction = \case
    NOP -> "nop"
    Label name -> TextBuilder.text name <> ":"

compileGlobalName :: GlobalName -> TextBuilder
compileGlobalName MkGlobalName{moduleName, name} =
    "v$" <> TextBuilder.text (Text.replace ":" "$" (renderModuleName moduleName)) <> "$" <> TextBuilder.text name
