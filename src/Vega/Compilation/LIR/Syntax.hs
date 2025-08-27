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

data LayoutStructure
    = IntLayout
    | PointerLayout
    | -- | INVARIANT: the elements are correctly aligned
      ProductLayout (Seq Layout)
    | TagLayout {numberOfTags :: Int}
    | -- INVARIANT: all elements have the same size
      UnionLayout (Seq Layout)
    | Padding {bits :: Int}
    deriving (Generic)

data Layout = MkLayoutUnchecked
    { structure :: LayoutStructure
    , size :: ~Int
    , alignment :: ~Int
    }
    deriving (Generic)

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

deriving via Generically LayoutStructure instance Pretty LayoutStructure

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
