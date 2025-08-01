{-# OPTIONS_GHC -Wno-type-defaults #-}

{- | Vega to JavaScript compilation. This goes directly from the type checked Vega code
    without performing any optimizations or further transformations.

    "Dead code elimination" is however automatically performed on declarations, since we only compile the ones that
    are reachable from the entry point anyway.
-}
module Vega.Compilation.JavaScript (compileDeclaration, assembleFromEntryPoint) where

import Relude hiding (State, evalState, get, intercalate, modify, put, trace)

import Effectful
import Vega.Effect.GraphPersistence (GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence

import Data.Text.Lazy.Builder qualified as TextBuilder
import Effectful.State.Static.Local (State, evalState, get, modify, put)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)

import Data.HashSet qualified as HashSet
import Data.Sequence (Seq (..))
import Data.Text qualified as Text
import Effectful.Error.Static (Error)
import Vega.Effect.Trace (Category (..), Trace, trace)
import Vega.Error (DriverError)
import Vega.Syntax

-- In this module, we want string literals to default to text builders.
-- This does *not* influence any other modules, however it does remove defaulting of other
-- classes like Num (GHC 9.12 fixes this with NamedDefaults).
-- Since those would usually throw a warning anyway, this is not a problem for us.
default (TextBuilder.Builder)

type Compile es =
    ( GraphPersistence :> es
    , Writer TextBuilder.Builder :> es
    , Trace :> es
    )

compileDeclaration :: (GraphPersistence :> es, Trace :> es) => Declaration Typed -> Eff es LText
compileDeclaration declaration = fmap (TextBuilder.toLazyText . snd) $ runWriter @TextBuilder.Builder do
    compileDeclarationSyntax declaration.syntax

-- TODO: we need to support actual decision tree compilation for non-variable patterns
compilePattern :: Pattern Typed -> TextBuilder.Builder
compilePattern = \case
    VarPattern _ localName -> compileLocalName localName
    TypePattern _ inner _ -> compilePattern inner
    WildcardPattern _loc -> "_"
    TuplePattern _ patterns -> "[" <> intercalate "," (fmap compilePattern patterns) <> "]"
    _ -> undefined

compileDeclarationSyntax :: (Compile es) => DeclarationSyntax Typed -> Eff es ()
compileDeclarationSyntax = \case
    DefineFunction
        { name
        , typeSignature = _
        , declaredTypeParameters = _
        , parameters
        , body
        } -> do
            tell ("const " <> compileGlobalName name <> " = " <> "(")

            for_ parameters \parameter -> do
                tell (compilePattern parameter)
                tell ", "
            tell ") => "
            compileExpr body
    DefineVariantType
        { name = _
        , typeParameters = _
        , constructors
        } -> do
            for_ constructors \(_loc, constructorName, arguments) -> case arguments of
                [] -> tell $ "const " <> compileGlobalName constructorName <> " = " <> "({ tag: \"" <> compileGlobalName constructorName <> "\" })\n"
                _ -> do
                    let parameters = ["x" <> show i | i <- [1 .. length arguments]]

                    tell $ "const " <> compileGlobalName constructorName <> " = ("
                    tell $ intercalate ", " parameters
                    tell $ ") => ({ tag: \"" <> compileGlobalName constructorName <> "\", payload: ["
                    tell $ intercalate ", " parameters
                    tell $ "] })\n"

compileExpr :: (Compile es) => Expr Typed -> Eff es ()
compileExpr = \case
    Var _loc name -> tell (compileName name)
    DataConstructor _loc name -> tell (compileName name)
    Application
        { functionExpr
        , arguments
        } -> do
            tell "("
            compileExpr functionExpr
            tell ")("
            for_ arguments compileExpr
            tell ")"
    PartialApplication
        { functionExpr
        , partialArguments
        } -> undefined
    VisibleTypeApplication
        { loc
        , varName
        , typeArguments = _
        } -> compileExpr (Var loc varName)
    Lambda _loc _typeParameters parameters body -> do
        let compileParameter = \case
                VarPattern _loc name -> compileLocalName name
                TypePattern _ inner _ -> compileParameter inner
                _ -> undefined
        tell "(("
        for_ parameters \parameter -> do
            tell (compileParameter parameter)
            tell ","
        tell ") => "
        compileExpr body
        tell ")"
    -- TODO: this uses haskell's escaping rules which might not line up 100% with JS
    StringLiteral _loc literal -> tell (show literal)
    IntLiteral _loc literal -> tell (show literal)
    -- TODO: this is probably not quite correct for many numbers
    DoubleLiteral _loc literal -> tell (show literal)
    TupleLiteral _loc elements -> do
        tell "["
        for_ elements \expr -> do
            compileExpr expr
            tell ", "
        tell "]"
    BinaryOperator _loc left op right -> undefined
    If
        { condition
        , thenBranch
        , elseBranch
        } -> undefined
    SequenceBlock
        { statements
        } -> do
            tell "((() => "
            compileStatements statements
            tell ")())"
    Match
        { scrutinee
        , cases
        } -> undefined

compileStatements :: (Compile es) => Seq (Statement Typed) -> Eff es ()
compileStatements Empty = tell "return []"
compileStatements (statements :|> Run _loc lastExpression) = do
    for_ statements \statement -> do
        compileStatement statement
        tell "; "
    tell "return "
    compileExpr lastExpression
compileStatements statements = do
    for_ statements \statement -> do
        compileStatement statement
        tell "; "
    tell "return []"

compileStatement :: (Compile es) => Statement Typed -> Eff es ()
compileStatement = \case
    Run _ expr -> do
        tell "const _ = "
        compileExpr expr
    Let _ pattern_ body -> do
        tell $ "const " <> compilePattern pattern_ <> " = "
        compileExpr body 
    LetFunction{} -> undefined
    Use{} -> undefined

{- | Assemble all the alrady compiled JS declarations into a single JS file.
This assumes that
   - the passed entry point exists and is valid (has the right type, accessibility, etc.)
   - all other declarations have already been compiled to JS
-}
assembleFromEntryPoint :: (HasCallStack, GraphPersistence :> es, Trace :> es) => GlobalName -> Eff es TextBuilder.Builder
assembleFromEntryPoint entryPoint = fmap snd $ runWriter $ evalState @(HashSet DeclarationName) mempty do
    entryPointDeclaration <-
        GraphPersistence.getDefiningDeclaration entryPoint >>= \case
            Just declaration -> pure declaration
            Nothing -> error $ "JavaScript.assembleFromEntryPoint: entry point not found (this should have been caught by the driver): " <> show entryPoint

    includeDeclarationRecursively entryPointDeclaration

    tell (compileGlobalName entryPoint <> "()")

includeDeclarationRecursively ::
    (GraphPersistence :> es, Trace :> es, Writer TextBuilder.Builder :> es, State (HashSet DeclarationName) :> es) =>
    DeclarationName ->
    Eff es ()
includeDeclarationRecursively name = do
    processedDeclarations <- get @(HashSet DeclarationName)
    case HashSet.member name processedDeclarations of
        True -> do
            trace AssembleJS ("Skipping already included declaration: " <> show name)
            pure ()
        False -> do
            trace AssembleJS ("Including declaration: " <> show name)

            put (HashSet.insert name processedDeclarations)

            code <-
                GraphPersistence.getCompiledJS name >>= \case
                    Ok code -> pure code
                    Missing{} -> error $ "Trying to assemble missing JS code for declaration: " <> show name

            tell (TextBuilder.fromLazyText code <> "\n\n")

            dependencies <- GraphPersistence.getDependencies name

            for_ dependencies \dependency ->
                includeDeclarationRecursively dependency

-- | Render global names into a format suitable for JS names
compileGlobalName :: GlobalName -> TextBuilder.Builder
compileGlobalName (MkGlobalName{moduleName, name}) = do
    -- TODO: do something less naive
    let escapedModuleName =
            renderModuleName moduleName
                & Text.replace "-" "____"
                & Text.replace "." "___"
                & Text.replace "/" "__"
                & Text.replace ":" "$"
    TextBuilder.fromText escapedModuleName <> "$" <> TextBuilder.fromText name

compileLocalName :: LocalName -> TextBuilder.Builder
compileLocalName (MkLocalName{parent = _, name, count}) =
    case count of
        0 -> TextBuilder.fromText name
        _ -> TextBuilder.fromText name <> "$$" <> show count

compileName :: Name -> TextBuilder.Builder
compileName = \case
    Local localName -> compileLocalName localName
    Global globalName -> compileGlobalName globalName

intercalate :: (Foldable f) => TextBuilder.Builder -> f TextBuilder.Builder -> TextBuilder.Builder
intercalate separator elements = go (toList elements)
  where
    go = \case
        [] -> ""
        [x] -> x
        (x : xs) -> x <> separator <> go xs
