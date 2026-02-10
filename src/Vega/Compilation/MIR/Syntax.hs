module Vega.Compilation.MIR.Syntax where

import Data.HashMap.Strict qualified as HashMap
import Data.Unique (Unique, hashUnique)
import GHC.Generics (Generically (..))
import Relude
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName, Representation)
import Vega.Pretty (Ann, Doc, Pretty, align, intercalateDoc, keyword, localIdentText, lparen, number, pretty, rparen, (<+>))

data Program = MkProgram
    { declarations :: Seq Declaration
    }
    deriving (Generic)

data Declaration = DefineFunction
    { name :: CoreName
    , parameters :: Seq (LocalCoreName, Representation)
    , init :: BlockDescriptor
    , blocks :: HashMap BlockDescriptor Block
    }
    deriving (Generic)

newtype BlockDescriptor = MkBlockDescriptor Unique
    deriving stock (Generic)
    deriving newtype (Eq, Hashable)

newtype Phis = MkPhys (HashMap Variable (Seq Variable))

data Block = MkBlock
    { phis :: Phis
    , instructions :: Seq Instruction
    , terminator :: Terminator
    }
    deriving (Generic)

newtype Variable = MkVariable Int
    deriving newtype (Eq, Hashable)

data Path = SumField Int
    deriving (Generic)

data Instruction
    = Add Variable Variable Variable
    | ReadField Variable Representation Path
    | Box
        { var :: Variable
        , target :: Variable
        , targetRepresentation :: Representation
        }
    | Unbox {var :: Variable, boxedTarget :: Variable, representation :: Representation}
    | ProductConstructor {var :: Variable, values :: Seq Variable, representation :: Representation}
    | SumConstructor {var :: Variable, tag :: Int, values :: Seq Variable, representation :: Representation}
    | AllocClosure {var :: Variable, closedValues :: Seq Variable, representation :: Representation}
    | LoadIntLiteral Variable Int
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

instance Pretty Declaration where
    pretty = \case
        DefineFunction{name, parameters, init, blocks} -> do
            pretty name
                <> typedArguments parameters
                <> keyword "="
                <> lparen "{"
                <> "\n  "
                <> align
                    ( keyword "init:"
                        <+> pretty init
                        <> "\n"
                        <> keyword "blocks:"
                        <> "\n  "
                        <> align (intercalateDoc "\n\n" (fmap (uncurry prettyBlock) (HashMap.toList blocks)))
                    )
                <> "\n"
                <> rparen "}"

prettyBlock :: BlockDescriptor -> Block -> Doc Ann
prettyBlock descriptor MkBlock{phis = MkPhys phiMap, instructions, terminator} =
    align $
        pretty descriptor
            <> keyword ":"
            <> "\n"
            <> ( case HashMap.toList phiMap of
                    [] -> ""
                    phis -> intercalateDoc "\n" (map (\(result, inputs) -> pretty result <> keyword " = " <> keyword "φ" <> arguments inputs) phis) <> "\n"
               )
            <> "  "
            <> align
                ( intercalateDoc "\n" (fmap pretty instructions)
                    <> "\n"
                    <> pretty terminator
                )

deriving via Generically Path instance Pretty Path

deriving via Generically Instruction instance Pretty Instruction

deriving via Generically Terminator instance Pretty Terminator

instance Pretty BlockDescriptor where
    pretty (MkBlockDescriptor unique) = number (hashUnique unique)

instance Pretty Variable where
    pretty (MkVariable name) = localIdentText ("x" <> show name)

arguments :: (Pretty a, Foldable f) => f a -> Doc Ann
arguments elements = lparen "(" <> intercalateDoc (keyword ", ") (map pretty (toList elements)) <> rparen ")"

typedArguments :: (Pretty a, Pretty b, Foldable f) => f (a, b) -> Doc Ann
typedArguments elements = lparen "(" <> intercalateDoc (keyword ", ") (map (\(x, y) -> pretty x <+> keyword ":" <+> pretty y) (toList elements)) <> rparen ")"