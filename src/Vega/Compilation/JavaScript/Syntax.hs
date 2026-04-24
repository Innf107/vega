module Vega.Compilation.JavaScript.Syntax (
    Name,
    Statement (..),
    Expr (..),
    BinaryOperator (..),
    renderStatements,
    compileGlobalName,
    compileLocalName,
    compileName,
    compileLocalCoreName,
    compileCoreName,
) where

import Data.Char qualified as Char
import Data.Text qualified as Text
import Data.Unique (hashUnique)
import Numeric (showHex)
import Relude hiding (Const, Undefined)
import TextBuilder (TextBuilder)
import TextBuilder qualified
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Syntax qualified as Vega

type Name = Text

data Statement
    = Const Name Expr
    | Let Name (Maybe Expr)
    | Function Name (Seq Name) (Seq Statement)
    | Return Expr
    | If Expr (Seq Statement) (Seq Statement)
    | SwitchString
        { scrutinee :: Expr
        , cases :: Seq (Text, Seq Statement)
        , default_ :: Maybe (Seq Statement)
        }
    | SwitchInt
        { scrutinee :: Expr
        , intCases :: Seq (Int, Seq Statement)
        , default_ :: Maybe (Seq Statement)
        }
    | DestructureArray (Seq Name) Expr
    | Panic Expr
    | Assign Expr Expr

data Expr
    = IIFE (Seq Statement)
    | Var Name
    | Application Expr (Seq Expr)
    | FieldAccess Expr Text
    | Index Expr Expr
    | Lambda (Seq Name) (Seq Statement)
    | StringLiteral Text
    | IntLiteral Integer
    | DoubleLiteral Rational
    | BoolLiteral Bool
    | ArrayLiteral (Seq Expr)
    | ObjectLiteral (Seq (Name, Expr))
    | BinaryOperator Expr BinaryOperator Expr
    | Undefined

data BinaryOperator
    = Add
    | Subtract
    | Multiply
    | Divide
    | And
    | Or
    | Less
    | LessEqual
    | Equal
    | NotEqual
    | GreaterEqual
    | Greater
    deriving stock (Generic)

renderStatement :: Statement -> TextBuilder
renderStatement = \case
    Const name expr -> "const " <> TextBuilder.text name <> " = " <> renderExpr expr
    Let name initializer ->
        ("let " <> TextBuilder.text name) <> case initializer of
            Just initializer -> " = " <> renderExpr initializer
            _ -> ""
    Function name parameters body ->
        "function "
            <> (TextBuilder.text name)
            <> "("
            <> intercalateMap "," TextBuilder.text parameters
            <> "){\n"
            <> renderStatements body
            <> "\n}"
    Return expr -> "return " <> renderExpr expr
    If condition then_ else_ ->
        "if("
            <> renderExpr condition
            <> "){\n"
            <> renderStatements then_
            <> "\n} else {\n"
            <> renderStatements else_
            <> "\n}"
    SwitchString{scrutinee, cases, default_} -> do
        let renderCase (string, body) =
                "case \""
                    <> escapeString string
                    <> "\":\n"
                    <> renderStatements body
                    <> "\nbreak;"
        let renderedDefault = case default_ of
                Nothing -> ""
                Just statements -> "default:\n" <> renderStatements statements
        "switch("
            <> renderExpr scrutinee
            <> "){\n"
            <> intercalateMap "\n" renderCase cases
            <> renderedDefault
            <> "}\n"
    SwitchInt{scrutinee, intCases, default_} -> do
        let renderCase (int, body) =
                "case "
                    <> show int
                    <> ":\n"
                    <> renderStatements body
                    <> "\nbreak;"
        let renderedDefault = case default_ of
                Nothing -> ""
                Just statements -> "default:\n" <> renderStatements statements
        "switch("
            <> renderExpr scrutinee
            <> "){\n"
            <> intercalateMap "\n" renderCase intCases
            <> renderedDefault
            <> "}\n"
    DestructureArray bindings arrayExpr -> "const [" <> intercalateMap ", " TextBuilder.text bindings <> "] = " <> renderExpr arrayExpr
    Panic message -> "throw new Error('PANIC: ' + (" <> renderExpr message <> "))"
    Assign expr1 expr2 -> renderExpr expr1 <> " = " <> renderExpr expr2

renderStatements :: (Foldable f) => f Statement -> TextBuilder
renderStatements statements = intercalateMap ";\n" renderStatement statements

renderExpr :: Expr -> TextBuilder
renderExpr = \case
    IIFE statements -> "((() => {" <> renderStatements statements <> "})())"
    Var name -> TextBuilder.text name
    Application funExpr argExprs -> "(" <> renderExpr funExpr <> ")(" <> intercalateMap ", " renderExpr argExprs <> ")"
    FieldAccess expr field -> "(" <> renderExpr expr <> ")." <> TextBuilder.text field
    Index object index -> "(" <> renderExpr object <> ")[" <> renderExpr index <> "]"
    Lambda parameters body -> "((" <> intercalateMap "," TextBuilder.text parameters <> ") => {" <> renderStatements body <> "})"
    StringLiteral string -> "\"" <> escapeString string <> "\""
    IntLiteral int -> show int
    DoubleLiteral rational -> undefined
    BoolLiteral True -> "true"
    BoolLiteral False -> "false"
    ArrayLiteral elements -> "[" <> intercalateMap ", " renderExpr elements <> "]"
    ObjectLiteral bindings -> "{" <> intercalateMap ", " (\(name, expr) -> TextBuilder.text name <> ": " <> renderExpr expr) bindings <> "}"
    BinaryOperator left operator right -> "(" <> renderExpr left <> " " <> renderBinaryOperator operator <> " " <> renderExpr right <> ")"
    Undefined -> "undefined"

renderBinaryOperator :: BinaryOperator -> TextBuilder
renderBinaryOperator = \case
    Add -> "+"
    Subtract -> "-"
    Multiply -> "*"
    Divide -> "/"
    And -> "&&"
    Or -> "||"
    Less -> "<"
    LessEqual -> "<="
    Equal -> "=="
    NotEqual -> "!="
    GreaterEqual -> ">="
    Greater -> ">"

intercalateMap :: (Foldable f) => TextBuilder -> (a -> TextBuilder) -> f a -> TextBuilder
intercalateMap separator f xs = TextBuilder.intercalate separator (map f (toList xs))

-- | Render global names into a format suitable for JS names
compileGlobalName :: Vega.GlobalName -> Name
compileGlobalName (Vega.MkGlobalName{moduleName, name}) = do
    -- TODO: do something less naive
    let escapedModuleName =
            Vega.renderModuleName moduleName
                & Text.replace "-" "____"
                & Text.replace "." "___"
                & Text.replace "/" "__"
                & Text.replace ":" "$"
    escapedModuleName <> "$" <> name

compileLocalName :: Vega.LocalName -> Name
compileLocalName (Vega.MkLocalName{parent = _, name, count}) =
    case count of
        0 -> name
        _ -> name <> "$$" <> show count

compileLocalCoreName :: Core.LocalCoreName -> Name
compileLocalCoreName = \case
    Core.UserProvided local -> compileLocalName local
    Core.Generated unique -> "$x" <> show (hashUnique unique)

compileName :: Vega.Name -> Name
compileName = \case
    Vega.Local localName -> compileLocalName localName
    Vega.Global globalName -> compileGlobalName globalName

compileCoreName :: Core.CoreName -> Name
compileCoreName = \case
    Core.Local localName -> compileLocalCoreName localName
    Core.Global globalName -> compileGlobalName globalName

-- TODO
escapeString :: Text -> TextBuilder
escapeString string = TextBuilder.text $ Text.concatMap escapeChar string
  where
    escapeChar = \case
        '\0' -> "\\0"
        '\a' -> "\\a"
        '\b' -> "\\b"
        '\ESC' -> "\\e"
        '\f' -> "\\f"
        '\n' -> "\\n"
        '\r' -> "\\r"
        '\t' -> "\\t"
        '\v' -> "\\v"
        '\\' -> "\\\\"
        '"' -> "\\\""
        char
            | Char.isPrint char -> [char]
            | otherwise -> "\\x" <> toText (showHex (fromEnum char) "")
