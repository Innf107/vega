{-# LANGUAGE PartialTypeSignatures #-}

module Vega.Compilation.Core.VegaToCore where

import Effectful
import Relude hiding (NonEmpty, trace)

import Data.HashMap.Strict (alter)
import Data.HashMap.Strict qualified as HashMap
import Data.Map qualified as Map
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Vega.Compilation.Core.Syntax (nameToCoreName)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.PatternMatching (CaseTree)
import Vega.Compilation.PatternMatching qualified as PatternMatching
import Vega.Debug (showHeadConstructor)
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Effect.Trace (Category (Patterns), Trace, trace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique, runNewUnique)
import Vega.Panic (panic)
import Vega.Pretty (align, indent, intercalateDoc, keyword, pretty, (<+>))
import Vega.Pretty qualified as Pretty
import Vega.Seq.NonEmpty (NonEmpty (..), pattern NonEmpty)
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Syntax (Pass (..))
import Vega.Syntax qualified as Vega
import Vega.Util (viaList)
import Vega.Util qualified as Util
import Witherable (wither)

type Compile es =
    ( GraphPersistence :> es
    , NewUnique :> es
    , Trace :> es
    )

compileDeclaration :: (GraphPersistence :> es, IOE :> es, Trace :> es) => Vega.Declaration Typed -> Eff es (Seq Core.Declaration)
compileDeclaration declaration =
    runNewUnique $
        compileDeclarationSyntax declaration.syntax

compileDeclarationSyntax :: (Compile es) => Vega.DeclarationSyntax Typed -> Eff es (Seq Core.Declaration)
compileDeclarationSyntax = \case
    Vega.DefineFunction{name, typeSignature = _, declaredTypeParameters = _, parameters, body} -> do
        locals <- for parameters \_ -> newLocal

        let caseTree = PatternMatching.serializeSubPatterns parameters ()

        trace Patterns $ "compileDeclarationSyntax(" <> Vega.prettyGlobal Vega.VarKind name <> "):" <+> pretty caseTree

        (caseStatements, caseExpr) <- compileCaseTree (\() -> compileExpr body) caseTree (fmap (\local -> Core.Var (Core.Local local)) locals)
        pure [Core.DefineFunction name locals caseStatements caseExpr]
    Vega.DefineVariantType{} -> pure []

compileExpr :: (Compile es) => Vega.Expr Typed -> Eff es (Seq Core.Statement, Core.Expr)
compileExpr expr = do
    let deferToValue = do
            (statements, value) <- compileExprToValue expr
            pure (statements, Core.Value value)
    case expr of
        Vega.Var{} -> deferToValue
        Vega.DataConstructor{} -> deferToValue
        Vega.Application _ (Vega.DataConstructor _ _) _ -> deferToValue
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
            variables <- for parameters \_ -> newLocal
            (bodyStatements, body) <- compileCaseTree (\() -> compileExpr body) caseTree (fmap (\localName -> Core.Var (Core.Local localName)) variables)
            pure ([], Core.Lambda variables bodyStatements body)
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
                    [ (booleanConstructorName True, ([], thenStatements, thenExpr))
                    , (booleanConstructorName False, ([], elseStatements, elseExpr))
                    ]
                )
        Vega.SequenceBlock{statements} -> compileStatements statements
        Vega.Match{scrutinee, cases} -> compilePatternMatch scrutinee (fmap (\Vega.MkMatchCase{pattern_, body} -> (pattern_, body)) cases)

compileExprToValue :: (Compile es) => Vega.Expr Typed -> Eff es (Seq Core.Statement, Core.Value)
compileExprToValue expr = do
    let deferToLet = do
            (statements, expr) <- compileExpr expr
            name <- newLocal
            pure (statements <> [Core.Let name expr], Core.Var (Core.Local name))
    case expr of
        Vega.Var _ name -> pure ([], Core.Var (nameToCoreName name))
        Vega.DataConstructor _ name -> do
            -- TODO: THIS IS WRONG. It's just a temporary fix to get Nil working.
            -- To do this correctly, we need a GraphPersistence hook to look up the arity of a data constructor
            -- and desugar this to a lambda taking that many parameters
            pure ([], Core.DataConstructorApplication (Core.UserDefinedConstructor name) [])
        Vega.Application _ (Vega.DataConstructor _ name) argumentExprs -> do
            (argumentStatements, arguments) <- Seq.unzip <$> for argumentExprs compileExprToValue
            pure (fold argumentStatements, Core.DataConstructorApplication (Core.UserDefinedConstructor name) arguments)
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
        Vega.SequenceBlock{} -> deferToLet
        Vega.Match{} -> deferToLet

compileStatements ::
    (Compile es) =>
    Seq (Vega.Statement Typed) ->
    Eff es (Seq Core.Statement, Core.Expr)
compileStatements = \case
    Empty -> pure ([], Core.Value unitLiteral)
    [Vega.Run _ expr] -> compileExpr expr
    (Vega.Run _ expr :<| rest) -> do
        local <- newLocal
        (statements, coreExpr) <- compileExpr expr
        (restStatements, result) <- compileStatements rest
        pure (statements <> [Core.Let local coreExpr] <> restStatements, result)
    (Vega.Let _ pattern_ expr :<| rest) -> do
        (scrutineeStatements, scrutineeValue) <- compileExprToValue expr

        let caseTree = PatternMatching.serializeSubPatterns [pattern_] ()

        (statements, finalExpr) <- compileCaseTree (\() -> compileStatements rest) caseTree [scrutineeValue]
        pure (scrutineeStatements <> statements, finalExpr)
    (Vega.LetFunction{} :<| _) -> undefined
    (Vega.Use{} :<| _) -> undefined

unitLiteral :: Core.Value
unitLiteral = Core.DataConstructorApplication (Core.TupleConstructor 0) []

compilePatternMatch :: (Compile es) => Vega.Expr Typed -> Seq (Vega.Pattern Typed, Vega.Expr Typed) -> Eff es (Seq Core.Statement, Core.Expr)
compilePatternMatch scrutinee = \case
    Empty -> undefined
    NonEmpty cases -> do
        (scrutineeStatements, scrutineeValue) <- compileExprToValue scrutinee

        let compileGoal goal =
                case (NonEmpty.toSeq) cases Seq.!? goal of
                    Nothing -> error "tried to access a match RHS that doesn't exist"
                    Just (_, body) -> compileExpr body
        let caseTree = PatternMatching.compileMatch (NonEmpty.mapWithIndex (\i (pattern_, _) -> (pattern_, i)) cases)
        trace Patterns $
            "compilePatternMatch: ["
                <> intercalateDoc (keyword ", ") (fmap (\(pattern_, _expr) -> showHeadConstructor pattern_) cases)
                <> "]\n"
                <> indent 2 ("~>" <> align (pretty caseTree))
        (matchStatements, matchExpr) <- compileCaseTree compileGoal caseTree [scrutineeValue]

        pure (scrutineeStatements <> matchStatements, matchExpr)

compileCaseTree ::
    forall goal es.
    (Compile es, Hashable goal) =>
    (goal -> Eff es (Seq Core.Statement, Core.Expr)) ->
    CaseTree goal ->
    Seq Core.Value ->
    Eff es (Seq Core.Statement, Core.Expr)
compileCaseTree compileGoal caseTree scrutinees = do
    let toJoinPoint = \case
            (_goal, (_, 1)) -> pure Nothing
            (goal, (boundVars, _count)) -> do
                local <- newLocal
                (bodyStatements, bodyExpr) <- compileGoal goal
                pure (Just (goal, (local, Core.LetJoin local boundVars bodyStatements bodyExpr)))
    joinPoints <- fmap HashMap.fromList $ wither toJoinPoint $ HashMap.toList (boundVarsAndFrequencies caseTree)

    let
        consume :: (HasCallStack) => Seq Core.Value -> (Core.Value, Seq Core.Value)
        consume Empty = panic "Consumed more scrutinees than were produced"
        consume (x :<| xs) = (x, xs)

        go ::
            Seq Core.Value ->
            Seq Core.LocalCoreName ->
            CaseTree goal ->
            Eff es (Seq Core.Statement, Core.Expr)
        go scrutinees boundValues = \case
            PatternMatching.Leaf goal ->
                case scrutinees of
                    Empty -> case HashMap.lookup goal joinPoints of
                        Nothing -> compileGoal goal
                        Just (joinPointName, _) ->
                            pure ([], Core.JumpJoin joinPointName (fmap (\var -> Core.Var (Core.Local var)) boundValues))
                    _ -> panic $ "Not all scrutinees consumed. Remaining: [" <> intercalateDoc ", " (fmap pretty scrutinees) <> "]"
            PatternMatching.ConstructorCase{constructors} -> do
                let (scrutinee, rest) = consume scrutinees
                cases <-
                    fromList <$> for (Map.toList constructors) \(constructor, (argumentCount, subTree)) -> do
                        locals <- Seq.replicateA argumentCount newLocal
                        (subTreeStatements, subTreeExpr) <- go (fmap (Core.Var . Core.Local) locals <> rest) boundValues subTree

                        pure (constructor, (locals, subTreeStatements, subTreeExpr))
                pure ([], Core.ConstructorCase scrutinee cases)
            PatternMatching.TupleCase count subTree -> do
                let (scrutinee, rest) = consume scrutinees
                locals <- Seq.replicateA count newLocal
                let accessStatements = Seq.mapWithIndex (\i local -> Core.Let local (Core.TupleAccess scrutinee i)) locals

                (subTreeStatements, subTreeExpr) <- go (fmap (Core.Var . Core.Local) locals <> rest) boundValues subTree
                pure (accessStatements <> subTreeStatements, subTreeExpr)
            PatternMatching.BindVar name subTree -> do
                let (scrutinee, _) = consume scrutinees
                (subStatements, subExpr) <- go scrutinees (boundValues :|> Core.UserProvided name) subTree
                pure ([Core.Let (Core.UserProvided name) (Core.Value scrutinee)] <> subStatements, subExpr)
            PatternMatching.Ignore subTree -> do
                let (_, rest) = consume scrutinees
                go rest boundValues subTree

    (caseStatements, caseExpr) <- go scrutinees [] caseTree

    let joinPointDefinitions = fromList $ map (\(_, statement) -> statement) (toList joinPoints)
    pure (joinPointDefinitions <> caseStatements, caseExpr)

boundVarsAndFrequencies :: forall goal. (Hashable goal) => CaseTree goal -> HashMap goal (Seq Core.LocalCoreName, Int)
boundVarsAndFrequencies tree = flip execState mempty $ do
    PatternMatching.traverseLeavesWithBoundVars tree \locals goal -> do
        modify $ flip alter goal \case
            Nothing -> Just (fmap Core.UserProvided locals, 1)
            Just (locals, count) -> Just (locals, count + 1)

newLocal :: (Compile es) => Eff es Core.LocalCoreName
newLocal = do
    unique <- newUnique
    pure (Core.Generated unique)

booleanConstructorName :: Bool -> Vega.Name
booleanConstructorName True = Vega.Global (Vega.internalName "True")
booleanConstructorName False = Vega.Global (Vega.internalName "False")
