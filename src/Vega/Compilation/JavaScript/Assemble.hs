module Vega.Compilation.JavaScript.Assemble (assembleFromEntryPoint) where

import Relude hiding (State, evalState, get, intercalate, modify, put, trace)

import Effectful
import Vega.Effect.GraphPersistence (GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence

import Effectful.State.Static.Local (State, evalState, get, put)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import TextBuilder (TextBuilder)
import TextBuilder qualified

import Data.HashSet qualified as HashSet
import Vega.Compilation.JavaScript.Syntax (compileGlobalName)
import Vega.Effect.Trace (Category (..), Trace, trace)
import Vega.Syntax

{- | Assemble all the alrady compiled JS declarations into a single JS file.
This assumes that
   - the passed entry point exists and is valid (has the right type, accessibility, etc.)
   - all other declarations have already been compiled to JS
-}
assembleFromEntryPoint :: (HasCallStack, GraphPersistence :> es, Trace :> es) => GlobalName -> Eff es TextBuilder
assembleFromEntryPoint entryPoint = fmap snd $ runWriter $ evalState @(HashSet DeclarationName) mempty do
    entryPointDeclaration <-
        GraphPersistence.getDefiningDeclaration entryPoint >>= \case
            Just declaration -> pure declaration
            Nothing -> error $ "JavaScript.assembleFromEntryPoint: entry point not found (this should have been caught by the driver): " <> show entryPoint

    includeDeclarationRecursively entryPointDeclaration

    tell (TextBuilder.text (compileGlobalName entryPoint) <> "()")

includeDeclarationRecursively ::
    (GraphPersistence :> es, Trace :> es, Writer TextBuilder :> es, State (HashSet DeclarationName) :> es) =>
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

            tell (TextBuilder.text code <> "\n\n")

            dependencies <- GraphPersistence.getDependencies name

            for_ dependencies \dependency ->
                includeDeclarationRecursively dependency
