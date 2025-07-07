{-# OPTIONS_GHC -Wno-type-defaults #-}

{- | Vega to JavaScript compilation. This goes directly from the type checked Vega code
    without performing any optimizations or further transformations.

    "Dead code elimination" is however automatically performed on declarations, since we only compile the ones that
    are reachable from the entry point anyway.
-}
module Vega.Compilation.JavaScript (compileDeclaration, assembleFromEntryPoint) where

import Relude hiding (State, evalState, get, modify, put, trace)

import Effectful
import Vega.Effect.GraphPersistence (GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence

import Data.Text.Lazy.Builder qualified as TextBuilder
import Effectful.State.Static.Local (State, evalState, get, modify, put)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)

import Data.HashSet qualified as HashSet
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
            -- TODO: we need to support actual decision tree compilation for non-variable patterns
            for_ parameters \case
                VarPattern _ localName -> tell (compileLocalName localName)
                _ -> undefined
            tell ") => "
            compileExpr body
    DefineVariantType
        { name=_
        , typeParameters = _
        , constructors
        } -> do
            for_ constructors \(_loc, constructorName, arguments) -> case arguments of
                [] -> tell $ "const " <> compileGlobalName constructorName <> " = " <> "({ tag: \"" <> compileGlobalName constructorName <> "\" })\n"
                _ -> do
                    let parameters = ["x" <> show i | i <- [1 .. length arguments]]

                    tell $ "const " <> compileGlobalName constructorName <> " = ("
                    tell $ TextBuilder.fromText $ Text.intercalate ", " parameters
                    tell $ ") => ({ tag: \"" <> compileGlobalName constructorName <> "\", payload: ["
                    tell $ TextBuilder.fromText $ Text.intercalate ", " parameters
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
        { expr
        , typeArguments = _
        } -> compileExpr expr
    Lambda _loc parameters body -> undefined
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
        } -> undefined
    Match
        { scrutinee
        , cases
        } -> undefined

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
compileGlobalName (MkGlobalName{moduleName = MkModuleName moduleName, name}) = do
    -- TODO: update this when module names are more sensible (and do something less naive)
    let escapedModuleName = Text.replace "-" "____" $ Text.replace "." "___" $ Text.replace "/" "__" moduleName
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
