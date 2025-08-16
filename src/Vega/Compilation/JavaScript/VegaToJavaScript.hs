{-# OPTIONS_GHC -Wno-type-defaults #-}

{- | Vega to JavaScript compilation. This goes directly from the type checked Vega code
    without performing any optimizations or further transformations.

    "Dead code elimination" is however automatically performed on declarations, since we only compile the ones that
    are reachable from the entry point anyway.
-}
module Vega.Compilation.JavaScript.VegaToJavaScript (compileDeclaration) where

import Relude hiding (State, evalState, get, intercalate, modify, put, trace)

import Effectful
import Vega.Effect.GraphPersistence (GraphData (..), GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence

import Effectful.State.Static.Local (State, evalState, get, modify, put)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import TextBuilder (TextBuilder)
import TextBuilder qualified

import Data.HashSet qualified as HashSet
import Data.Map qualified as Map
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Data.Text.Lazy qualified as LText
import Data.Traversable (for)
import Data.Unique (hashUnique, newUnique)
import Effectful.Error.Static (Error)
import Vega.Compilation.JavaScript.Syntax qualified as JS
import Vega.Compilation.PatternMatching (CaseTree (..), RecursiveCaseTree (..))
import Vega.Compilation.PatternMatching qualified as PatternMatching
import Vega.Debug (showHeadConstructor)
import Vega.Effect.Trace (Category (..), Trace, trace)
import Vega.Error (DriverError)
import Vega.Panic (panic)
import Vega.Seq.NonEmpty (NonEmpty (..), pattern NonEmpty)
import Vega.Syntax

type Compile es =
    ( Trace :> es
    , IOE :> es
    )

compileDeclaration :: (Compile es) => Declaration Typed -> Eff es Text
compileDeclaration declaration = do
    jsDeclarations <- compileDeclarationSyntax declaration.syntax
    pure $ TextBuilder.toText $ JS.renderStatements $ toList jsDeclarations

freshVar :: (Compile es) => Text -> Eff es JS.Name
freshVar base = do
    unique <- liftIO newUnique
    pure (base <> show (hashUnique unique))

compileDeclarationSyntax :: (Compile es) => DeclarationSyntax Typed -> Eff es (Seq JS.Statement)
compileDeclarationSyntax = \case
    DefineFunction{name, typeSignature = _, declaredTypeParameters = _, parameters, body} -> do
        parameterVariables <- for parameters \_ -> freshVar "x"

        body <- compileSequentialPatterns (Seq.zip parameterVariables parameters) body

        pure [JS.Function (JS.compileGlobalName name) parameterVariables body]
    DefineVariantType
        { typeParameters = _
        , constructors
        , name = _
        } -> do
            for constructors \(_, dataConstructorName, parameters) -> do
                case parameters of
                    [] ->
                        pure
                            ( JS.Const
                                (JS.compileGlobalName dataConstructorName)
                                (JS.ObjectLiteral [("tag", JS.StringLiteral (JS.compileGlobalName dataConstructorName))])
                            )
                    _ -> do
                        parameterVariables <- for parameters \_ -> freshVar "x"
                        pure
                            ( JS.Function
                                (JS.compileGlobalName dataConstructorName)
                                parameterVariables
                                [ JS.Return
                                    ( JS.ObjectLiteral
                                        [ ("tag", JS.StringLiteral (JS.compileGlobalName dataConstructorName))
                                        , ("payload", JS.ArrayLiteral (fmap JS.Var parameterVariables))
                                        ]
                                    )
                                ]
                            )

compileExpr :: (Compile es) => Expr Typed -> Eff es JS.Expr
compileExpr = \case
    Var _ varName -> pure $ JS.Var (JS.compileName varName)
    DataConstructor _ name -> pure $ JS.Var (JS.compileName name)
    Application _ funExpr argExprs -> do
        jsFunExpr <- compileExpr funExpr
        jsArgExprs <- for argExprs compileExpr
        pure (JS.Application jsFunExpr jsArgExprs)
    PartialApplication{} -> undefined
    VisibleTypeApplication{varName} -> pure $ JS.Var (JS.compileName varName)
    Lambda{parameters, body} -> do
        parameterVariables <- for parameters \_ -> freshVar "x"
        body <- compileSequentialPatterns (Seq.zip parameterVariables parameters) body

        pure (JS.Lambda parameterVariables body)
    StringLiteral _ literal -> pure $ JS.StringLiteral literal
    IntLiteral _ literal -> pure $ JS.IntLiteral literal
    DoubleLiteral _ rational -> pure $ JS.DoubleLiteral rational
    TupleLiteral _ elements -> do
        jsElements <- for elements compileExpr
        pure $ JS.ArrayLiteral jsElements
    BinaryOperator{} -> undefined
    If{condition, thenBranch, elseBranch} -> do
        jsCondition <- compileExpr condition
        jsThen <- compileExpr thenBranch
        jsElse <- compileExpr elseBranch
        pure $ JS.IIFE [JS.If jsCondition [JS.Return jsThen] [JS.Return jsElse]]
    SequenceBlock _ statements -> do
        jsStatements <- compileStatements statements
        pure $ JS.IIFE jsStatements
    Match{scrutinee, cases} -> do
        jsScrutineeExpr <- compileExpr scrutinee
        scrutineeName <- freshVar "s"
        jsStatements <- compilePatternMatch scrutineeName cases
        pure $ JS.IIFE ([JS.Const scrutineeName jsScrutineeExpr] <> jsStatements)

compileStatements :: (Compile es) => Seq (Statement Typed) -> Eff es (Seq JS.Statement)
compileStatements Empty = pure []
compileStatements [Run _loc expr] = do
    jsExpr <- compileExpr expr
    pure [JS.Return jsExpr]
compileStatements (statement :<| rest) = case statement of
    Run _ expr -> do
        jsExpr <- compileExpr expr
        rest <- compileStatements rest
        pure $ [JS.Const "_" jsExpr] <> rest
    Let _ pattern_ expr -> do
        jsExpr <- compileExpr expr
        varName <- freshVar "x"

        let caseTree = PatternMatching.compileMatch ((pattern_, ()) :<|| [])
        rest <- compileStatements rest
        matchStatements <- compileCaseTree (\_ -> pure rest) varName caseTree

        pure $ ([JS.Const varName jsExpr] <> matchStatements)
    LetFunction{name, typeSignature = _, parameters, body} -> do
        parameterVariables <- for parameters \_ -> freshVar "x"

        body <- compileSequentialPatterns (Seq.zip parameterVariables parameters) body

        pure [JS.Function (JS.compileLocalName name) parameterVariables body]
    Use{} -> undefined

compileSequentialPatterns :: (Compile es) => Seq (JS.Name, Pattern Typed) -> Expr Typed -> Eff es (Seq JS.Statement)
compileSequentialPatterns scrutineesAndPatterns expr = do
    let caseTree = PatternMatching.serializeSubPatterns (fmap snd scrutineesAndPatterns) expr

    compileRecursiveCaseTree compileLeaf (fmap fst scrutineesAndPatterns) caseTree

compilePatternMatch :: (Compile es) => JS.Name -> Seq (MatchCase Typed) -> Eff es (Seq JS.Statement)
compilePatternMatch scrutinee cases = case cases of
    Empty -> undefined
    NonEmpty cases -> do
        let caseTree = PatternMatching.compileMatch (fmap (\MkMatchCase{pattern_, body} -> (pattern_, body)) cases)
        compileCaseTree compileLeaf scrutinee caseTree

compileLeaf :: (Compile es) => Expr Typed -> Eff es (Seq JS.Statement)
compileLeaf expr = do
    jsExpr <- compileExpr expr
    pure [JS.Return jsExpr]

compileCaseTree :: (Compile es) => (goal -> Eff es (Seq JS.Statement)) -> JS.Name -> CaseTree goal -> Eff es (Seq JS.Statement)
compileCaseTree compileGoal scrutinee = \case
    Leaf goal -> compileGoal goal
    ConstructorCase{constructors} -> do
        cases <-
            fromList <$> for (Map.toList constructors) \(constructor, (parameterCount, continuation)) -> case parameterCount of
                0 -> do
                    statements <- compileRecursiveCaseTree compileGoal [] continuation
                    pure (JS.compileName constructor, statements)
                _ -> do
                    payloadVariables <- Seq.replicateM parameterCount (freshVar "p")
                    rest <- compileRecursiveCaseTree compileGoal payloadVariables continuation

                    pure
                        ( JS.compileName constructor
                        , [JS.DestructureArray payloadVariables (JS.FieldAccess (JS.Var scrutinee) "payload")]
                            <> rest
                        )
        pure
            [ JS.SwitchString
                { scrutinee = JS.FieldAccess (JS.Var scrutinee) "tag"
                , default_ = Nothing
                , cases = cases
                }
            ]
    TupleCase size continuation -> do
        variables <- Seq.replicateM size (freshVar "x")

        rest <- compileRecursiveCaseTree compileGoal variables continuation

        pure $ [JS.DestructureArray variables (JS.Var scrutinee)] <> rest
    BindVar varName cont -> do
        rest <- compileCaseTree compileGoal scrutinee cont
        pure $ [JS.Const (JS.compileLocalName varName) (JS.Var scrutinee)] <> rest
    OrDefault{} -> undefined

compileRecursiveCaseTree :: (HasCallStack, Compile es) => (goal -> Eff es (Seq JS.Statement)) -> Seq JS.Name -> RecursiveCaseTree goal -> Eff es (Seq JS.Statement)
compileRecursiveCaseTree compileGoal scrutinees tree = case (scrutinees, tree) of
    (Empty, Done goal) -> compileGoal goal
    (scrutinee :<| scrutinees, Continue caseTree) -> do
        let continue nextCaseTree = compileRecursiveCaseTree compileGoal scrutinees nextCaseTree

        compileCaseTree continue scrutinee caseTree
    (_ :<| _, Done _) -> do
        panic $ "Recursive case tree finished compilation early. Remaining scrutinees: " <> show scrutinees
    (Empty, Continue caseTree) -> do
        panic $ "Recursive case tree returned continue after all scrutinees were exhausted. Next case tree: " <> showHeadConstructor caseTree