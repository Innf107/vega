module Vega.Compilation.LIR.Syntax (
    Program (..),
    LocalVariable (..),
    Declaration (..),
    Block (..),
    BlockDescriptor (..),
    Instruction (..),
    Terminator (..),
    Value (..),
    Layout (..),
    UnboxedLayout (..),
) where

import Data.Sequence (Seq (..))
import GHC.Num (integerLog2)
import Relude
import Prelude (log)

-- TODO: move this somewhere else

import Data.HashMap.Strict qualified as HashMap
import Data.Unique (hashUnique)
import GHC.Generics (Generically (..))
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Effect.Unique.Static.Local (Unique)
import Vega.Pretty (Ann, Doc, Pretty, align, intercalateDoc, keyword, localIdentText, lparen, number, pretty, rparen, vsep, (<+>))

newtype LocalVariable = MkVariable Int

data FunctionName

data Program = MkProgram
    { declarations :: Seq Declaration
    }
    deriving (Generic)

data Declaration = DefineFunction
    { name :: CoreName
    , parameters :: Seq LocalCoreName
    , locals :: HashMap LocalCoreName Layout
    , init :: BlockDescriptor
    , blocks :: HashMap BlockDescriptor Block
    }
    deriving (Generic)

newtype BlockDescriptor = MkBlockDescriptor Unique
    deriving stock (Generic)
    deriving newtype (Eq, Hashable)

data Block = MkBlock
    { arguments :: Seq LocalCoreName
    , instructions :: Seq Instruction
    , terminator :: Terminator
    }
    deriving (Generic)

data Instruction
    = Add LocalCoreName LocalCoreName LocalCoreName
    | Allocate LocalCoreName Layout
    | AllocateClosure LocalCoreName FunctionName (Seq LocalVariable)
    | Store
        { pointer :: LocalVariable
        , value :: LocalVariable
        , offset :: Int
        }
    deriving (Generic)

data Value
    = Var CoreName
    | Literal Core.Literal
    deriving (Generic)

data Terminator
    = Return Value
    | Jump BlockDescriptor (Seq Value)
    | CallDirect LocalVariable FunctionName (Seq LocalVariable) BlockDescriptor
    | CallIndirect LocalVariable LocalVariable (Seq LocalVariable) BlockDescriptor
    | TailCallDirect CoreName (Seq Value)
    | TailCallIndirect LocalVariable (Seq LocalVariable)
    deriving (Generic)

data Layout
    = BoxedLayout
    | UnboxedLayout UnboxedLayout
    deriving (Generic)

data UnboxedLayout
    = IntLayout Int
    | FloatLayout Int
    deriving (Generic)

instance Pretty Declaration where
    pretty = \case
        DefineFunction{name, parameters, locals, init, blocks} -> do
            pretty name
                <> arguments parameters
                <> keyword "="
                <> lparen "{"
                <> "\n  "
                <> align
                    ( keyword "locals:"
                        <+> align (vsep (fmap (\(name, layout) -> pretty name <+> keyword ":" <+> pretty layout) (HashMap.toList locals)))
                        <> "\n"
                        <> keyword "init:"
                        <+> pretty init
                        <> "\n"
                        <> keyword "blocks:"
                        <> "\n  "
                        <> align (intercalateDoc "\n\n" (fmap (uncurry prettyBlock) (HashMap.toList blocks)))
                    )
                <> "\n"
                <> rparen "}"

prettyBlock :: BlockDescriptor -> Block -> Doc Ann
prettyBlock descriptor MkBlock{arguments = blockArguments, instructions, terminator} =
    align
        $ pretty descriptor
        <> arguments blockArguments
        <> "\n  "
        <> align
            ( intercalateDoc "\n" (fmap pretty instructions)
                <> "\n"
                <> pretty terminator
            )

deriving via Generically Instruction instance Pretty Instruction

deriving via Generically Terminator instance Pretty Terminator

deriving via Generically Layout instance Pretty Layout

deriving via Generically UnboxedLayout instance Pretty UnboxedLayout

instance Pretty BlockDescriptor where
    pretty (MkBlockDescriptor unique) = number (hashUnique unique)

instance Pretty Value where
    pretty = \case
        Var name -> pretty name
        Literal literal -> pretty literal

instance Pretty LocalVariable where
    pretty = undefined
instance Pretty FunctionName where
    pretty = \case {}

arguments :: (Pretty a, Foldable f) => f a -> Doc Ann
arguments elements = lparen "(" <> intercalateDoc (keyword ", ") (map pretty (toList elements)) <> rparen ")"
