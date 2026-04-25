{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Vega.Compilation.Core.Syntax where

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Unique (Unique)
import Relude hiding (NonEmpty)
import Vega.Debruijn qualified as Debruijn
import Vega.Pretty
import Vega.Seq.NonEmpty (NonEmpty)
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

-- TODO: do we really want to use a seq of declarations over a hash map or something?
data Declaration
    = DefineFunction
    { name :: GlobalName
    , representationParameters :: Debruijn.Limit
    , parameters :: Seq (LocalCoreName, Representation)
    , returnRepresentation :: Representation
    , statements :: Seq Statement
    , result :: Expr
    }

data Expr
    = Value Value
    | Unreachable
    | Application {function :: CoreName, representationArguments :: Seq Representation, arguments :: Seq Value, resultRepresentation :: Representation}
    | -- INVARIANT: JumpJoin never occurs in a let
      JumpJoin LocalCoreName (Seq Value)
    | Lambda (Seq (LocalCoreName, Representation)) (Seq Statement) Expr
    | ProductAccess {product :: Value, index :: Int, resultRepresentation :: Representation}
    | Box Value
    | Unbox {value :: Value, innerRepresentation :: Representation}
    | PureOperator PureOperatorExpr
    | ConstructorCase
        { scrutinee :: Value
        , scrutineeRepresentation :: Representation
        , cases :: (HashMap Int (Seq LocalCoreName, Seq Statement, Expr))
        , default_ :: Maybe (Seq Statement, Expr)
        }
    | IntCase
        { scrutinee :: Value
        , intCases :: HashMap Int (Seq Statement, Expr)
        , default_ :: Maybe (Seq Statement, Expr)
        }

data PureOperatorExpr
    = PureOperatorValue Value
    | Add PureOperatorExpr PureOperatorExpr
    | Subtract PureOperatorExpr PureOperatorExpr
    | Multiply PureOperatorExpr PureOperatorExpr
    | Divide PureOperatorExpr PureOperatorExpr
    | Less PureOperatorExpr PureOperatorExpr
    | LessEqual PureOperatorExpr PureOperatorExpr
    | Equal PureOperatorExpr PureOperatorExpr
    | NotEqual PureOperatorExpr PureOperatorExpr

data Statement
    = Let LocalCoreName Representation Expr
    | LetFunction
        { name :: LocalCoreName
        , parameters :: Seq (LocalCoreName, Representation)
        , returnRepresentation :: Representation
        , statements :: Seq Statement
        , result :: Expr
        }
    | LetJoin
        { name :: LocalCoreName
        , parameters :: Seq (LocalCoreName, Representation)
        , statements :: Seq Statement
        , result :: Expr
        }

data Value
    = Var {varName :: CoreName}
    | Instantiation {varName :: CoreName, representationArguments :: NonEmpty Representation}
    | Literal Literal
    | ProductConstructor
        { arguments :: Seq Value
        , resultRepresentation :: Representation
        }
    | SumConstructor
        { constructorIndex :: Int
        , payload :: Value
        , resultRepresentation :: Representation
        }

data Literal
    = IntLiteral Integer
    | DoubleLiteral Rational
    | StringLiteral Text

data Representation
    = ProductRep (Seq Representation)
    | SumRep (Seq Representation)
    | ArrayRep Representation
    | FunctionPointerRep
    | PrimitiveRep Vega.PrimitiveRep
    | ParameterRep Debruijn.Index
    deriving stock (Eq, Generic)
    deriving anyclass (Hashable)

nameToCoreName :: Vega.Name -> CoreName
nameToCoreName = \case
    Vega.Local localName -> Local (UserProvided localName)
    Vega.Global globalName -> Global globalName

instance Pretty Representation where
    pretty :: Representation -> Doc Ann
    pretty (ProductRep []) = keyword "Unit"
    pretty (ProductRep representations) = lparen "(" <> intercalateDoc (" " <> keyword "*" <> " ") (fmap pretty representations) <> rparen ")"
    pretty (SumRep []) = keyword "Empty"
    pretty (SumRep representations) = lparen "(" <> intercalateDoc (" " <> keyword "+" <> " ") (fmap pretty representations) <> rparen ")"
    pretty (ArrayRep inner) = keyword "ArrayRep" <> lparen "(" <> pretty inner <> rparen ")"
    pretty FunctionPointerRep = keyword "FunctionPointer"
    pretty (PrimitiveRep rep) = pretty rep
    pretty (ParameterRep index) = pretty index

instance Pretty Declaration where
    pretty = \case
        DefineFunction
            { name
            , parameters
            , returnRepresentation
            , statements
            , result
            , representationParameters
            } ->
                prettyGlobal VarKind name
                    <> ( case Debruijn.size representationParameters of
                            0 -> ""
                            parameterCount -> "[" <> number parameterCount <> "]"
                       )
                    <> arguments (fmap (\(param, rep) -> PrettyId (pretty param <+> keyword ":" <+> pretty rep)) parameters)
                        <+> ":"
                        <+> pretty returnRepresentation
                        <+> keyword "="
                        <+> prettyBody statements result

instance Pretty Statement where
    pretty = \case
        Let name representation expr -> keyword "let" <+> pretty name <+> keyword ":" <+> pretty representation <+> keyword "=" <+> pretty expr
        LetJoin name parameters bodyStatements bodyExpr ->
            keyword "letjoin" <+> pretty name <> typedParameters parameters <+> keyword "=" <+> prettyBody bodyStatements bodyExpr
        LetFunction{name, parameters, returnRepresentation, statements, result} ->
            keyword "letrec" <+> pretty name <> typedParameters parameters <+> keyword ":" <+> pretty returnRepresentation <+> keyword "=" <+> prettyBody statements result

instance Pretty Expr where
    pretty = \case
        Value value -> pretty value
        Unreachable -> keyword "unreachable"
        Application funName representationArguments argValues representation -> do
            let instantiation = case representationArguments of
                    Empty -> pretty funName
                    _ -> pretty funName <> lparen "[" <> intercalateDoc (keyword ", ") (fmap pretty representationArguments) <> rparen "]"
            instantiation <> arguments argValues <+> keyword ":" <+> pretty representation
        JumpJoin name jumpArguments -> keyword "join" <+> pretty name <> arguments jumpArguments
        Lambda parameters bodyStatements bodyExpr -> keyword "\\" <> typedParameters parameters <+> keyword "->" <+> prettyBody bodyStatements bodyExpr
        ProductAccess tupleValue index returnRepresentation -> do
            pretty tupleValue <> lparen "[" <> number index <> rparen "]" <+> keyword ":" <+> pretty returnRepresentation
        Box value -> keyword "box" <+> pretty value
        Unbox{value, innerRepresentation} -> keyword "unbox" <+> pretty value <+> keyword ":" <+> pretty innerRepresentation
        ConstructorCase scrutinee representation cases default_ -> do
            let prettyCase (constructor, (locals, bodyStatements, bodyExpr)) =
                    lparen "[" <> number constructor <> rparen "]" <+> arguments locals <+> keyword "->" <+> prettyBody bodyStatements bodyExpr

            keyword "match" <+> pretty scrutinee <+> keyword ":" <+> pretty representation <+> lparen "{"
                <> "\n"
                <> indent 2 (align (intercalateDoc "\n" (map prettyCase (HashMap.toList cases))))
                <> "\n"
                <> ( case default_ of
                        Nothing -> mempty
                        Just (statements, expr) -> indent 2 $ align $ prettyBody statements expr
                   )
                <> rparen "}"
        IntCase{scrutinee, intCases, default_} -> do
            let prettyCase (constructor, (bodyStatements, bodyExpr)) =
                    number constructor <+> keyword "->" <+> prettyBody bodyStatements bodyExpr

            keyword "match[Int]" <+> pretty scrutinee <+> lparen "{"
                <> "\n"
                <> indent 2 (align (intercalateDoc "\n" (map prettyCase (HashMap.toList intCases))))
                <> "\n"
                <> ( case default_ of
                        Nothing -> mempty
                        Just (statements, expr) ->
                            ( indent 2 $
                                align $
                                    keyword "_" <+> keyword "->" <+> prettyBody statements expr
                            )
                                <> "\n"
                   )
                <> rparen "}"
        PureOperator operator -> pretty operator

instance Pretty PureOperatorExpr where
    pretty = \case
        PureOperatorValue value -> pretty value
        Add left right -> lparen "(" <> pretty left <+> keyword "+" <+> pretty right <> rparen ")"
        Subtract left right -> lparen "(" <> pretty left <+> keyword "-" <+> pretty right <> rparen ")"
        Multiply left right -> lparen "(" <> pretty left <+> keyword "*" <+> pretty right <> rparen ")"
        Divide left right -> lparen "(" <> pretty left <+> keyword "/" <+> pretty right <> rparen ")"
        Less left right -> lparen "(" <> pretty left <+> keyword "<" <+> pretty right <> rparen ")"
        LessEqual left right -> lparen "(" <> pretty left <+> keyword "<=" <+> pretty right <> rparen ")"
        Equal left right -> lparen "(" <> pretty left <+> keyword "==" <+> pretty right <> rparen ")"
        NotEqual left right -> lparen "(" <> pretty left <+> keyword "!=" <+> pretty right <> rparen ")"

instance Pretty Value where
    pretty = \case
        Var name -> pretty name
        Instantiation name arguments -> pretty name <> lparen "[" <> intercalateDoc (keyword ", ") (fmap pretty arguments) <> rparen "]"
        Literal literal -> pretty literal
        ProductConstructor{arguments = constructorArguments, resultRepresentation} -> arguments constructorArguments <+> keyword ":" <+> pretty resultRepresentation
        SumConstructor{constructorIndex, payload, resultRepresentation} ->
            lparen "[" <> number constructorIndex <> rparen "]" <> lparen "(" <> pretty payload <> rparen ")" <+> keyword ":" <+> pretty resultRepresentation

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
typedParameters elements = lparen "(" <> intercalateDoc (keyword "," <> " ") (map (\(elem, rep) -> pretty elem <> " " <> keyword ":" <> " " <> pretty rep) (toList elements)) <> rparen ")"

instance Pretty LocalCoreName where
    pretty = \case
        UserProvided local -> prettyLocal VarKind local
        Generated unique -> generatedVar unique "x"

instance Pretty CoreName where
    pretty = \case
        Global global -> prettyGlobal VarKind global
        Local local -> pretty local

-- | The representation of string literals (and in particular string literals)
stringRepresentation :: Representation
stringRepresentation = PrimitiveRep Vega.BoxedRep

-- The representation of functions. This *will* probably change in the future so code
-- should treat it abstractly instead of depending on its concrete value
functionRepresentation :: Representation
functionRepresentation = ProductRep [FunctionPointerRep, PrimitiveRep Vega.BoxedRep]

boolRepresentation :: Representation
boolRepresentation = SumRep [ProductRep [], ProductRep []]

trueValue :: Value
trueValue =
    SumConstructor
        { constructorIndex = 0
        , payload = unitValue
        , resultRepresentation = boolRepresentation
        }

falseValue :: Value
falseValue =
    SumConstructor
        { constructorIndex = 1
        , payload = unitValue
        , resultRepresentation = boolRepresentation
        }


unitValue :: Value
unitValue = ProductConstructor{arguments = [], resultRepresentation = ProductRep []}
