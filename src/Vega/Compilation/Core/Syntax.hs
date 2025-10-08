module Vega.Compilation.Core.Syntax where

import Data.HashMap.Strict qualified as HashMap
import Data.Unique (Unique, hashUnique)
import Relude
import Vega.Pretty
import Vega.Syntax (GlobalName, NameKind (..), prettyGlobal, prettyLocal)
import Vega.Syntax qualified as Vega

data CoreName
    = Global GlobalName
    | Local {-# UNPACK #-} LocalCoreName
    deriving (Generic, Eq, Hashable)

data LocalCoreName
    = UserProvided Vega.LocalName
    | Generated Unique
    deriving (Generic, Eq, Hashable)

-- TODO: representations?
-- TODO: do we really want to use a seq of declarations over a hash map or something?
data Declaration
    = DefineFunction
    { name :: GlobalName
    , parameters :: Seq (LocalCoreName, Representation)
    , returnRepresentation :: Representation
    , statements :: Seq Statement
    , result :: Expr
    }

data Expr
    = Value Value
    | Application CoreName (Seq Value)
    | -- INVARIANT: JumpJoin never occurs in a let
      JumpJoin LocalCoreName (Seq Value)
    | Lambda (Seq (LocalCoreName, Representation)) (Seq Statement) Expr
    | TupleAccess Value Int
    | ConstructorCase Value (HashMap Vega.Name (Seq LocalCoreName, Seq Statement, Expr))

data Statement
    = Let LocalCoreName Representation Expr
    | LetJoin
        { name :: LocalCoreName
        , parameters :: Seq (LocalCoreName, Representation)
        , statements :: Seq Statement
        , result :: Expr
        }

data Value
    = Var CoreName
    | Literal Literal
    | DataConstructorApplication DataConstructor (Seq Value)

data DataConstructor
    = UserDefinedConstructor Vega.Name
    | TupleConstructor {size :: Int}
    deriving (Generic, Show, Eq, Hashable)

data Literal
    = IntLiteral Integer
    | DoubleLiteral Rational
    | StringLiteral Text

data Representation
    = ProductRep (Seq Representation)
    | SumRep (Seq Representation)
    | PrimitiveRep Vega.PrimitiveRep

nameToCoreName :: Vega.Name -> CoreName
nameToCoreName = \case
    Vega.Local localName -> Local (UserProvided localName)
    Vega.Global globalName -> Global globalName

instance Pretty Representation where
    pretty (ProductRep representations) = lparen "(" <> intercalateDoc (" " <> keyword "*" <> " ") (fmap pretty representations) <> rparen ")"
    pretty (SumRep representations) = lparen "(" <> intercalateDoc (" " <> keyword "+" <> " ") (fmap pretty representations) <> rparen ")"
    pretty (PrimitiveRep rep) = pretty rep

instance Pretty Declaration where
    pretty = \case
        DefineFunction
            { name
            , parameters
            , returnRepresentation
            , statements
            , result
            } ->
                prettyGlobal VarKind name <> arguments (fmap (\(param, rep) -> PrettyId (pretty param <+> keyword ":" <+> pretty rep)) parameters) <+> ":" <+> pretty returnRepresentation <+> keyword "=" <+> prettyBody statements result

instance Pretty Statement where
    pretty = \case
        Let name representation expr -> keyword "let" <+> pretty name <+> pretty representation <+> keyword "=" <+> pretty expr
        LetJoin name parameters bodyStatements bodyExpr ->
            keyword "letjoin" <+> pretty name <> typedParameters parameters <+> keyword "=" <+> prettyBody bodyStatements bodyExpr

instance Pretty Expr where
    pretty = \case
        Value value -> pretty value
        Application funValue argValues -> pretty funValue <> arguments argValues
        JumpJoin name jumpArguments -> keyword "join" <+> pretty name <> arguments jumpArguments
        Lambda parameters bodyStatements bodyExpr -> keyword "\\" <> typedParameters parameters <+> keyword "->" <+> prettyBody bodyStatements bodyExpr
        TupleAccess tupleValue index -> do
            pretty tupleValue <> lparen "[" <> number index <> rparen "]"
        ConstructorCase scrutinee cases -> do
            let prettyCase (constructor, (locals, bodyStatements, bodyExpr)) =
                    Vega.prettyName Vega.DataConstructorKind constructor <> arguments locals <+> keyword "->" <+> prettyBody bodyStatements bodyExpr

            keyword "match" <+> pretty scrutinee <+> lparen "{"
                <> "\n"
                <> indent 2 (align (intercalateDoc "\n" (map prettyCase (HashMap.toList cases))))
                <> "\n"
                <> rparen "}"

instance Pretty Value where
    pretty = \case
        Var name -> pretty name
        Literal literal -> pretty literal
        DataConstructorApplication constructor constructorArguments ->
            prettyConstructorApplication constructor constructorArguments

prettyConstructorApplication :: (Pretty a) => DataConstructor -> Seq a -> Doc Ann
prettyConstructorApplication constructor constructorArguments = case constructor of
    UserDefinedConstructor name -> Vega.prettyName Vega.DataConstructorKind name <> arguments constructorArguments
    TupleConstructor count
        | count == length constructorArguments -> arguments constructorArguments
        | otherwise -> errorText ("Tuple(" <> show count <> ")") <> arguments constructorArguments

instance Pretty Literal where
    pretty = \case
        IntLiteral int -> number int
        DoubleLiteral rational -> number rational
        -- TODO: use real vega quoting instead of haskell quoting
        StringLiteral string -> literal (show string)

prettyBody :: Seq Statement -> Expr -> Doc Ann
prettyBody statements expr =
    do
        lparen "{" <> "\n"
        <> indent 2 (align (fold (fmap (\statement -> pretty statement <> keyword ";" <> "\n") statements) <> pretty expr))
        <> "\n"
        <> rparen "}"

arguments :: (Pretty a, Foldable f) => f a -> Doc Ann
arguments elements = lparen "(" <> intercalateDoc (keyword "," <> " ") (map pretty (toList elements)) <> rparen ")"

typedParameters :: (Pretty a, Foldable f) => f (a, Representation) -> Doc Ann
typedParameters elements = lparen "(" <> intercalateDoc (keyword "," <> " ") (map (\(elem, rep) -> pretty elem <> " " <> keyword ":" <> " " <> pretty rep) (toList elements))

instance Pretty LocalCoreName where
    pretty = \case
        UserProvided local -> prettyLocal VarKind local
        Generated unique -> generatedVar unique "x"

instance Pretty CoreName where
    pretty = \case
        Global global -> prettyGlobal VarKind global
        Local local -> pretty local