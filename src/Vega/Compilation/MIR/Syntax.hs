module Vega.Compilation.MIR.Syntax where

import Data.HashMap.Strict qualified as HashMap
import Data.Unique (Unique, hashUnique)
import GHC.Generics (Generically (..))
import Relude
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName, Representation)
import Vega.Pretty (Ann, Doc, Pretty, align, intercalateDoc, keyword, localIdentText, lparen, number, pretty, rparen, (<+>))
import Vega.Syntax qualified as Vega

data Program = MkProgram
    { declarations :: Seq Declaration
    }
    deriving (Generic)

data Declaration = DefineFunction
    { name :: CoreName
    , parameters :: Seq (Variable, Representation)
    , returnRepresentation :: Representation
    , init :: BlockDescriptor
    , blocks :: HashMap BlockDescriptor Block
    }
    deriving (Generic)

newtype BlockDescriptor = MkBlockDescriptor Unique
    deriving stock (Generic)
    deriving newtype (Eq, Hashable)

newtype Phis = MkPhis (HashMap Variable (Seq Variable))

data Block = MkBlock
    { phis :: Phis
    , instructions :: Seq Instruction
    , terminator :: Terminator
    }
    deriving (Generic)

newtype Variable = MkVariable Int
    deriving newtype (Eq, Hashable)

data PathSegment = SumConstructorPath Int
    | ProductFieldPath Int
    deriving (Generic)

type Path = Seq PathSegment

data Instruction
    = Add Variable Variable Variable
    | AccessField Variable Path Variable -- TODO: representation?
    | Box
        { var :: Variable
        , target :: Variable
        , targetRepresentation :: Representation
        }
    | Unbox {var :: Variable, boxedTarget :: Variable, representation :: Representation}
    | ProductConstructor {var :: Variable, values :: Seq Variable, representation :: Representation}
    | SumConstructor {var :: Variable, tag :: Int, values :: Seq Variable, representation :: Representation}
    | AllocClosure {var :: Variable, closedValues :: Seq Variable, representation :: Representation}
    | LoadGlobalClosure {var :: Variable, functionName :: Vega.GlobalName}
    | LoadGlobal {var :: Variable, globalName :: Vega.GlobalName}
    | LoadIntLiteral {var :: Variable, literal :: Int}
    | LoadSumTag {var :: Variable, sum :: Variable, sumRepresentation :: Representation}
    | CallDirect {var :: Variable, functionName :: Vega.GlobalName, arguments :: (Seq Variable)}
    | CallClosure {var :: Variable, closure :: Variable, arguments :: (Seq Variable)}
    deriving (Generic)

data Terminator
    = Return Variable
    | Jump BlockDescriptor
    | SwitchInt {var :: Variable, cases :: Seq (Int, BlockDescriptor)}
    | TailCallDirect {functionName :: Vega.GlobalName, arguments :: Seq Variable}
    | TailCallClosure {closure :: Variable, arguments :: Seq Variable}
    deriving (Generic)

instance Pretty Declaration where
    pretty = \case
        DefineFunction{name, parameters, init, blocks} -> do
            pretty name
                <> typedArguments parameters
                    <+> keyword "="
                    <+> lparen "{"
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
prettyBlock descriptor MkBlock{phis = MkPhis phiMap, instructions, terminator} =
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

deriving via Generically PathSegment instance Pretty PathSegment

prettyPath :: Path -> Doc Ann
prettyPath path = lparen "[" <> intercalateDoc (keyword "->") (fmap pretty path) <> rparen "]"

instance Pretty Instruction where
    pretty = \case
        Add var arg1 arg2 -> keywordInstruction "add" var [pretty arg1, pretty arg2]
        AccessField var path value -> keywordInstruction "accessField" var [prettyPath path, pretty value]
        Box
            { var
            , target
            , targetRepresentation
            } -> keywordInstruction "box" var [pretty target, pretty targetRepresentation]
        Unbox{var, boxedTarget, representation} -> keywordInstruction "unbox" var [pretty boxedTarget, pretty representation]
        ProductConstructor{var, values, representation} ->
            pretty var <+> keyword "=" <+> keyword "product" <+> arguments values <+> pretty representation
        SumConstructor{var, tag, values, representation} ->
            pretty var <+> keyword "=" <+> keyword "sum" <+> lparen "[" <> number tag <> rparen "]" <> arguments values <+> pretty representation
        AllocClosure{var, closedValues, representation} -> keywordInstruction "allocClosure" var (fmap pretty closedValues <> [pretty representation])
        LoadGlobalClosure{var, functionName} ->
            keywordInstruction "loadGlobalClosure" var [Vega.prettyGlobal Vega.VarKind functionName]
        LoadGlobal var globalName ->
            keywordInstruction "loadGlobal" var [Vega.prettyGlobal Vega.VarKind globalName]
        LoadIntLiteral var int ->
            keywordInstruction "int" var [number int]
        LoadSumTag{var, sum, sumRepresentation} -> keywordInstruction "loadSumTag" var [pretty sum, pretty sumRepresentation]
        CallDirect{var, functionName, arguments = callArguments} -> keywordInstruction "callDirect" var [Vega.prettyGlobal Vega.VarKind functionName] <> arguments callArguments
        CallClosure{var, closure, arguments = callArguments} -> keywordInstruction "callClosure" var [pretty closure] <> arguments callArguments

keywordInstruction :: Text -> Variable -> Seq (Doc Ann) -> Doc Ann
keywordInstruction name var arguments =
    pretty var <+> keyword "=" <+> keyword name <+> intercalateDoc " " arguments

instance Pretty Terminator where
    pretty = \case
        Return value -> keyword "return" <+> pretty value
        Jump block -> keyword "jump" <+> pretty block
        SwitchInt value targets ->
            keyword "switchInt" <+> pretty value <+> lparen "["
                <> "\n  "
                <> align (intercalateDoc "\n" (fmap (\(value, target) -> number value <+> keyword "->" <+> pretty target) targets))
                <> "\n"
                <> rparen "]"
        TailCallDirect functionName callArguments ->
            keyword "tailcallDirect" <+> Vega.prettyGlobal Vega.VarKind functionName <> arguments callArguments
        TailCallClosure closure callArguments ->
            keyword "tailcallClosure" <+> pretty closure <> arguments callArguments

instance Pretty BlockDescriptor where
    pretty (MkBlockDescriptor unique) = number (hashUnique unique)

instance Pretty Variable where
    pretty (MkVariable name) = localIdentText ("x" <> show name)

arguments :: (Pretty a, Foldable f) => f a -> Doc Ann
arguments elements = lparen "(" <> intercalateDoc (keyword ", ") (map pretty (toList elements)) <> rparen ")"

typedArguments :: (Pretty a, Pretty b, Foldable f) => f (a, b) -> Doc Ann
typedArguments elements = lparen "(" <> intercalateDoc (keyword ", ") (map (\(x, y) -> pretty x <+> keyword ":" <+> pretty y) (toList elements)) <> rparen ")"