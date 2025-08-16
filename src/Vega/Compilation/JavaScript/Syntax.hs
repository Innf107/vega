module Vega.Compilation.JavaScript.Syntax (
    Name,
    Statement (..),
    Expr (..),
    renderStatements,
    compileGlobalName,
    compileLocalName,
    compileName,
) where

import Data.Text qualified as Text
import Relude hiding (Const)
import TextBuilder (TextBuilder)
import TextBuilder qualified
import Vega.Syntax qualified as Vega

type Name = Text

data Statement
    = Const Name Expr
    | Function Name (Seq Name) (Seq Statement)
    | Return Expr
    | If Expr (Seq Statement) (Seq Statement)
    | SwitchString
        { scrutinee :: Expr
        , cases :: Seq (Text, Seq Statement)
        , default_ :: Maybe (Seq Statement)
        }
    | DestructureArray (Seq Name) Expr

data Expr
    = IIFE (Seq Statement)
    | Var Name
    | Application Expr (Seq Expr)
    | FieldAccess Expr Text
    | Lambda (Seq Name) (Seq Statement)
    | StringLiteral Text
    | IntLiteral Integer
    | DoubleLiteral Rational
    | ArrayLiteral (Seq Expr)
    | ObjectLiteral (Seq (Name, Expr))

renderStatement :: Statement -> TextBuilder
renderStatement = \case
    Const name expr -> "const " <> TextBuilder.text name <> " = " <> renderExpr expr
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
    DestructureArray bindings arrayExpr -> "const [" <> intercalateMap ", " TextBuilder.text bindings <> "] = " <> renderExpr arrayExpr

renderStatements :: (Foldable f) => f Statement -> TextBuilder
renderStatements statements = intercalateMap ";\n" renderStatement statements

renderExpr :: Expr -> TextBuilder
renderExpr = \case
    IIFE statements -> "((() => {" <> renderStatements statements <> "})())"
    Var name -> TextBuilder.text name
    Application funExpr argExprs -> "(" <> renderExpr funExpr <> ")(" <> intercalateMap ", " renderExpr argExprs <> ")"
    FieldAccess expr field -> "(" <> renderExpr expr <> ")." <> TextBuilder.text field
    Lambda parameters body -> "((" <> intercalateMap "," TextBuilder.text parameters <> ") => {" <> renderStatements body <> "})"
    StringLiteral string -> "\"" <> escapeString string <> "\""
    IntLiteral int -> show int
    DoubleLiteral rational -> undefined
    ArrayLiteral elements -> "[" <> intercalateMap ", " renderExpr elements <> "]"
    ObjectLiteral bindings -> "{" <> intercalateMap ", " (\(name, expr) -> TextBuilder.text name <> ": "<> renderExpr expr) bindings <> "}"

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

compileName :: Vega.Name -> Name
compileName = \case
    Vega.Local localName -> compileLocalName localName
    Vega.Global globalName -> compileGlobalName globalName

-- TODO
escapeString :: Text -> TextBuilder
escapeString string = TextBuilder.text string
