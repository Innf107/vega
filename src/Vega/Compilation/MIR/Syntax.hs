module Vega.Compilation.MIR.Syntax where

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Unique (Unique, hashUnique)
import GHC.Generics (Generically (..))
import Relude hiding (Identity)
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName, Representation (..))
import Vega.Panic (panic)
import Vega.Pretty (Ann, Doc, Pretty, align, intercalateDoc, keyword, localIdentText, lparen, number, pretty, rparen, (<+>))
import Vega.Syntax qualified as Vega

data Program = MkProgram
    { declarations :: HashMap CoreName Declaration
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

newtype Phis = MkPhis (HashMap Variable (Representation, HashMap BlockDescriptor Variable))

data Block = MkBlock
    { phis :: Phis
    , instructions :: Seq Instruction
    , terminator :: Terminator
    }
    deriving (Generic)

data Variable = MkVariable Text Int
instance Eq Variable where
    MkVariable _ index1 == MkVariable _ index2 = index1 == index2

instance Hashable Variable where
    hashWithSalt salt (MkVariable _ index) = hashWithSalt salt index

data PathSegment
    = SumConstructorPath Int
    | ProductFieldPath Int
    deriving (Generic)

type Path = Seq PathSegment

data Instruction
    = Identity Variable Variable
    | ArithmeticOperator {var :: Variable, operatorExpr :: ArithmeticExpr}
    | AccessField {var :: Variable, path :: Path, target :: Variable, fieldRepresentation :: Representation}
    | Box
        { var :: Variable
        , target :: Variable
        }
    | Unbox {var :: Variable, boxedTarget :: Variable, representation :: Representation}
    | ProductConstructor {var :: Variable, values :: Seq Variable, representation :: Representation}
    | SumConstructor {var :: Variable, tag :: Int, payload :: Variable, representation :: Representation}
    | AllocClosure {var :: Variable, closedValues :: Seq Variable, representation :: Representation}
    | LoadGlobalClosure {var :: Variable, functionName :: Vega.GlobalName, representationArguments :: Seq Representation}
    | LoadGlobal {var :: Variable, representationArguments :: Seq Representation, globalName :: Vega.GlobalName, representation :: Representation}
    | LoadIntLiteral {var :: Variable, literal :: Int}
    | LoadSumTag {var :: Variable, sum :: Variable}
    | CallDirect
        { var :: Variable
        , functionName :: Vega.GlobalName
        , representationArguments :: Seq Representation
        , arguments :: (Seq Variable)
        , returnRepresentation :: Representation
        }
    | CallClosure {var :: Variable, closure :: Variable, arguments :: (Seq Variable), returnRepresentation :: Representation}
    deriving (Generic)

data ArithmeticExpr
    = Add Variable Variable
    | Subtract Variable Variable
    | Multiply Variable Variable
    | Divide Variable Variable
    | Less Variable Variable
    | LessEqual Variable Variable
    | Equal Variable Variable
    | NotEqual Variable Variable

data Terminator
    = Return Variable
    | Unreachable
    | Jump BlockDescriptor
    | SwitchInt {var :: Variable, cases :: Seq (Int, BlockDescriptor), default_ :: Maybe BlockDescriptor}
    | TailCallDirect
        { functionName :: Vega.GlobalName
        , representationArguments :: Seq Representation
        , arguments :: Seq Variable
        , returnRepresentation :: Representation
        }
    | TailCallClosure {closure :: Variable, arguments :: Seq Variable, returnRepresentation :: Representation}
    deriving (Generic)

representationAtPath :: Representation -> Path -> Representation
representationAtPath baseRepresentation fullPath = go baseRepresentation fullPath
  where
    go representation = \case
        Empty -> representation
        segment@(ProductFieldPath index) :<| rest -> case representation of
            ProductRep inner -> case Seq.lookup index inner of
                Nothing -> outOfBounds "product field" index
                Just innerRepresentation -> go innerRepresentation rest
            actual -> invalid segment actual
        segment@(SumConstructorPath index) :<| rest -> case representation of
            SumRep cases -> case Seq.lookup index cases of
                Nothing -> outOfBounds "sum constructor" index
                Just innerRepresentation -> go innerRepresentation rest
            actual -> invalid segment actual
    invalid segment actual = panic $ "Trying to acess path segment" <+> pretty segment <+> "on incompatible representation" <+> pretty actual <+> "while trying to access path" <+> prettyPath fullPath
    outOfBounds kind index = panic $ "Trying to access out-of-bounds" <+> kind <+> "at index" <+> number index <+> "while trying to access path" <+> prettyPath fullPath

instance Pretty Declaration where
    pretty :: Declaration -> Doc Ann
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
                    phis ->
                        intercalateDoc
                            "\n"
                            ( map
                                ( \(result, (representation, inputs)) ->
                                    pretty result <+> keyword ":" <+> pretty representation <> keyword " = " <> keyword "φ" <> arguments inputs
                                )
                                phis
                            )
                            <> "\n"
               )
            <> "  "
            <> align (intercalateDoc "\n" (fmap pretty instructions <> [pretty terminator]))

deriving via Generically PathSegment instance Pretty PathSegment

prettyPath :: Path -> Doc Ann
prettyPath path = lparen "[" <> intercalateDoc (keyword "->") (fmap pretty path) <> rparen "]"

instance Pretty Instruction where
    pretty = \case
        Identity var target -> keywordInstruction "identity" var [pretty target]
        ArithmeticOperator{var, operatorExpr} -> pretty var <+> keyword "=" <+> pretty operatorExpr
        AccessField{var, path, target, fieldRepresentation} -> keywordInstruction "accessField" var [prettyPath path, pretty target] <+> keyword ":" <+> pretty fieldRepresentation
        Box
            { var
            , target
            } -> keywordInstruction "box" var [pretty target]
        Unbox{var, boxedTarget, representation} -> keywordInstruction "unbox" var [pretty boxedTarget, pretty representation]
        ProductConstructor{var, values, representation} ->
            pretty var <+> keyword "=" <+> keyword "product" <+> arguments values <+> pretty representation
        SumConstructor{var, tag, payload, representation} ->
            pretty var <+> keyword "=" <+> keyword "sum" <+> lparen "[" <> number tag <> rparen "]" <> lparen "(" <> pretty payload <> rparen ")" <+> pretty representation
        AllocClosure{var, closedValues, representation} -> keywordInstruction "allocClosure" var (fmap pretty closedValues <> [pretty representation])
        LoadGlobalClosure{var, functionName, representationArguments} -> do
            let instantiation = case representationArguments of
                    [] -> mempty
                    _ -> lparen "[" <> intercalateDoc (keyword ", ") (fmap pretty representationArguments) <> rparen "]"
            keywordInstruction "loadGlobalClosure" var [Vega.prettyGlobal Vega.VarKind functionName <> instantiation]
        LoadGlobal var representationArguments globalName representation -> do
            let instantiation = case representationArguments of
                    [] -> mempty
                    _ -> lparen "[" <> intercalateDoc (keyword ", ") (fmap pretty representationArguments) <> rparen "]"
            keywordInstruction "loadGlobal" var [Vega.prettyGlobal Vega.VarKind globalName <> instantiation, pretty representation]
        LoadIntLiteral var int ->
            keywordInstruction "int" var [number int]
        LoadSumTag{var, sum} -> keywordInstruction "loadSumTag" var [pretty sum]
        CallDirect{var, representationArguments, functionName, arguments = callArguments} -> do
            let instantiation = case representationArguments of
                    [] -> mempty
                    _ -> lparen "[" <> intercalateDoc (keyword ", ") (fmap pretty representationArguments) <> rparen "]"
            keywordInstruction "callDirect" var [Vega.prettyGlobal Vega.VarKind functionName <> instantiation] <> arguments callArguments
        CallClosure{var, closure, arguments = callArguments} -> keywordInstruction "callClosure" var [pretty closure] <> arguments callArguments

instance Pretty ArithmeticExpr where
    pretty = \case
        Add var1 var2 -> pretty var1 <+> keyword "+" <+> pretty var2
        Subtract var1 var2 -> pretty var1 <+> keyword "-" <+> pretty var2
        Multiply var1 var2 -> pretty var1 <+> keyword "*" <+> pretty var2
        Divide var1 var2 -> pretty var1 <+> keyword "/" <+> pretty var2
        Less var1 var2 -> pretty var1 <+> keyword "<" <+> pretty var2
        LessEqual var1 var2 -> pretty var1 <+> keyword "<=" <+> pretty var2
        Equal var1 var2 -> pretty var1 <+> keyword "==" <+> pretty var2
        NotEqual var1 var2 -> pretty var1 <+> keyword "!=" <+> pretty var2

keywordInstruction :: Text -> Variable -> Seq (Doc Ann) -> Doc Ann
keywordInstruction name var arguments =
    pretty var <+> keyword "=" <+> keyword name <+> intercalateDoc " " arguments

instance Pretty Terminator where
    pretty = \case
        Return value -> keyword "return" <+> pretty value
        Unreachable -> keyword "unreachable"
        Jump block -> keyword "jump" <+> pretty block
        SwitchInt value targets default_ ->
            keyword "switchInt" <+> pretty value <+> lparen "["
                <> "\n  "
                <> align (intercalateDoc "\n" (fmap (\(value, target) -> number value <+> keyword "->" <+> pretty target) targets))
                <> "\n"
                <> ( case default_ of
                        Nothing -> mempty
                        Just defaultBlock -> "  " <> keyword "_" <+> keyword "->" <+> pretty defaultBlock <> "\n"
                   )
                <> rparen "]"
        TailCallDirect functionName representationArguments callArguments returnRepresentation -> do
            let instantiation = case representationArguments of
                    Empty -> mempty
                    _ -> lparen "[" <> intercalateDoc (keyword ", ") (fmap pretty representationArguments) <> rparen "]"
            keyword "tailcallDirect" <+> Vega.prettyGlobal Vega.VarKind functionName <> instantiation <> arguments callArguments <+> keyword ":" <+> pretty returnRepresentation
        TailCallClosure closure callArguments representation ->
            keyword "tailcallClosure" <+> pretty closure <> arguments callArguments <+> keyword ":" <+> pretty representation

instance Pretty BlockDescriptor where
    pretty (MkBlockDescriptor unique) = number (hashUnique unique)

instance Pretty Variable where
    pretty (MkVariable name index) = localIdentText (name <> "_" <> show index)

arguments :: (Pretty a, Foldable f) => f a -> Doc Ann
arguments elements = lparen "(" <> intercalateDoc (keyword ", ") (map pretty (toList elements)) <> rparen ")"

typedArguments :: (Pretty a, Pretty b, Foldable f) => f (a, b) -> Doc Ann
typedArguments elements = lparen "(" <> intercalateDoc (keyword ", ") (map (\(x, y) -> pretty x <+> keyword ":" <+> pretty y) (toList elements)) <> rparen ")"