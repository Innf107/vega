{-# LANGUAGE PartialTypeSignatures #-}

module Vega.Compilation.Core.VegaToCore where

import Effectful
import Relude

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Vega.Compilation.Core.Syntax (nameToCoreName)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.PatternMatching (CaseTree, RecursiveCaseTree)
import Vega.Compilation.PatternMatching qualified as PatternMatching
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique, runNewUnique)
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Syntax (Pass (..))
import Vega.Syntax qualified as Vega
import Vega.Util qualified as Util
import Witherable (wither)

type Compile es =
    ( GraphPersistence :> es
    , NewUnique :> es
    )

compileDeclaration :: (GraphPersistence :> es, IOE :> es) => Vega.Declaration Typed -> Eff es (Seq Core.Declaration)
compileDeclaration declaration =
    runNewUnique $
        compileDeclarationSyntax declaration.syntax

compileDeclarationSyntax :: (Compile es) => Vega.DeclarationSyntax Typed -> Eff es (Seq Core.Declaration)
compileDeclarationSyntax = \case
    Vega.DefineFunction{name, typeSignature, declaredTypeParameters, parameters, body} -> do
        undefined
    Vega.DefineVariantType{} -> undefined

compileExpr :: (Compile es) => Vega.Expr Typed -> Eff es (Seq Core.Statement, Core.Expr)
compileExpr expr = do
    let deferToValue = do
            (statements, value) <- compileExprToValue expr
            pure (statements, Core.Value value)
    case expr of
        Vega.Var{} -> deferToValue
        Vega.DataConstructor{} -> deferToValue
        Vega.Application _ functionExpr argExprs -> do
            (functionStatements, function) <- compileExprToValue functionExpr
            (argumentStatements, arguments) <-
                Seq.unzip <$> for argExprs \argument -> do
                    compileExprToValue argument
            functionVar <- case function of
                Core.Var name -> pure name
                value -> panic $ "function compiled to non-variable value: " <> pretty value <> ". this should have been a type error"
            pure (functionStatements <> fold argumentStatements, Core.Application functionVar arguments)
        Vega.PartialApplication{} -> undefined
        Vega.VisibleTypeApplication{} -> deferToValue
        Vega.Lambda{parameters, body} -> do
            let caseTree = PatternMatching.serializeSubPatterns parameters ()
            compileCaseTree (\() -> body) caseTree
        Vega.StringLiteral{} -> deferToValue
        Vega.IntLiteral{} -> deferToValue
        Vega.DoubleLiteral{} -> deferToValue
        Vega.TupleLiteral{} -> deferToValue
        Vega.BinaryOperator{} -> undefined
        Vega.If{condition, thenBranch, elseBranch} -> do
            (conditionStatements, conditionValue) <- compileExprToValue condition
            (thenStatements, thenExpr) <- compileExpr thenBranch
            (elseStatements, elseExpr) <- compileExpr elseBranch
            pure
                ( conditionStatements
                , Core.ConstructorCase
                    conditionValue
                    [ (booleanConstructor True, ([], thenStatements, thenExpr))
                    , (booleanConstructor False, ([], elseStatements, elseExpr))
                    ]
                )
        _ -> undefined

compileExprToValue :: (Compile es) => Vega.Expr Typed -> Eff es (Seq Core.Statement, Core.Value)
compileExprToValue expr = do
    let deferToLet = do
            (statements, expr) <- compileExpr expr
            name <- newLocal
            pure (statements <> [Core.Let name expr], Core.Var (Core.Local name))
    case expr of
        Vega.Var _ name -> pure ([], Core.Var (nameToCoreName name))
        Vega.DataConstructor _ name -> do
            -- TODO: determine the number of parameters, then desugar to a lambda with that many parameters
            undefined
        Vega.Application{} -> deferToLet
        Vega.PartialApplication{} -> undefined
        -- We can erase type applications since Core is untyped
        Vega.VisibleTypeApplication{varName} -> pure ([], Core.Var (nameToCoreName varName))
        Vega.Lambda{} -> deferToLet
        Vega.StringLiteral _loc literal -> pure ([], Core.Literal (Core.StringLiteral literal))
        Vega.IntLiteral _loc literal -> pure ([], Core.Literal (Core.IntLiteral literal))
        Vega.DoubleLiteral _loc literal -> pure ([], Core.Literal (Core.DoubleLiteral literal))
        Vega.TupleLiteral _loc elements -> do
            (statements, elementValues) <- Seq.unzip <$> for elements compileExprToValue
            pure (fold statements, Core.DataConstructorApplication (Core.TupleConstructor (length elementValues)) elementValues)
        Vega.BinaryOperator{} -> undefined
        Vega.If{} -> deferToLet
        _ -> undefined

compileCaseTree ::
    (Compile es, Hashable goal) =>
    (goal -> Vega.Expr Typed) ->
    RecursiveCaseTree goal ->
    Eff es (Seq Core.Statement, Core.Expr)
compileCaseTree getExprForGoal caseTree = do
    let toJoinPoint = \case
            (_goal, (_, 1)) -> pure Nothing
            (goal, (boundVars, _count)) -> do
                local <- newLocal
                (bodyStatements, bodyExpr) <- compileExpr (getExprForGoal goal)
                pure (Just (local, (local, Core.LetJoin local boundVars bodyStatements bodyExpr)))
    joinPoints <- fmap HashMap.fromList $ wither toJoinPoint $ HashMap.toList (boundVarsAndFrequencies caseTree)

    undefined

boundVarsAndFrequencies :: forall goal. (Hashable goal) => RecursiveCaseTree goal -> HashMap goal (Seq Core.LocalCoreName, Int)
boundVarsAndFrequencies tree = undefined

newLocal :: (Compile es) => Eff es Core.LocalCoreName
newLocal = do
    unique <- newUnique
    pure (Core.Generated unique)

booleanConstructor :: Bool -> Core.CoreName
booleanConstructor = undefined