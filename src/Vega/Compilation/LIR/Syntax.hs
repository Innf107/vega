module Vega.Compilation.LIR.Syntax (
    Program (..),
    Variable (..),
    Declaration (..),
    Block (..),
    BlockDescriptor (..),
    Instruction (..),
    Terminator (..),
    Layout (..),
    UnboxedLayout (..),
) where

import Relude

-- TODO: move this somewhere else

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence qualified as Seq
import Data.Unique (hashUnique)
import GHC.Generics (Generically (..))
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName)
import Vega.Effect.Unique.Static.Local (Unique)
import Vega.Pretty (Ann, Doc, Pretty, align, intercalateDoc, keyword, lparen, number, pretty, rparen, vsep, (<+>))

newtype Variable = MkVariable Int

data FunctionName

data Program = MkProgram
    { declarations :: Seq Declaration
    }
    deriving (Generic)

data Declaration = DefineFunction
    { name :: CoreName
    , parameters :: Seq LocalCoreName
    , layouts :: Seq Layout
    , init :: BlockDescriptor
    , blocks :: HashMap BlockDescriptor Block
    }
    deriving (Generic)

newtype BlockDescriptor = MkBlockDescriptor Unique
    deriving stock (Generic)
    deriving newtype (Eq, Hashable)

data Block = MkBlock
    { arguments :: Seq Variable
    , instructions :: Seq Instruction
    , terminator :: Terminator
    }
    deriving (Generic)

data Instruction
    = Add Variable Variable Variable
    | Allocate Variable Layout
    | AllocateClosure Variable CoreName Layout
    | IntConstant Variable Int
    | Global Variable CoreName
    deriving (Generic)

data Terminator
    = Return Variable
    | Jump BlockDescriptor (Seq Variable)
    | CallDirect Variable CoreName (Seq Variable) BlockDescriptor
    | CallIndirect Variable Variable (Seq Variable) BlockDescriptor
    | TailCallDirect CoreName (Seq Variable)
    | TailCallIndirect Variable (Seq Variable)
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
        DefineFunction{name, parameters, layouts, init, blocks} -> do
            pretty name
                <> arguments parameters
                <> keyword "="
                <> lparen "{"
                <> "\n  "
                <> align
                    ( keyword "layouts:"
                        <+> align (vsep (Seq.mapWithIndex (\index layout -> number index <+> keyword ":" <+> pretty layout) layouts))
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

instance Pretty Variable where
    pretty = undefined
instance Pretty FunctionName where
    pretty = \case {}

arguments :: (Pretty a, Foldable f) => f a -> Doc Ann
arguments elements = lparen "(" <> intercalateDoc (keyword ", ") (map pretty (toList elements)) <> rparen ")"
