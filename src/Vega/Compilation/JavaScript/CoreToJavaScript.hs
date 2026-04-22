module Vega.Compilation.JavaScript.CoreToJavaScript (compileDeclaration) where

import Relude

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Text.Internal.StrictBuilder qualified as TextBuilder
import Data.Traversable (for)
import Data.Unique (hashUnique, newUnique)
import Effectful (Eff, IOE, type (:>))
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.JavaScript.Syntax qualified as JS
import Vega.Effect.Trace (Trace)
import Vega.Util (forIndexed)

type Compile es =
    ( Trace :> es
    , IOE :> es
    )

compileDeclaration :: (Trace :> es, IOE :> es) => Core.Declaration -> Eff es (Seq JS.Statement)
compileDeclaration = \case
    Core.DefineFunction
        { name
        , representationParameters = _
        , parameters
        , returnRepresentation = _
        , statements
        , result
        } -> do
            let jsParameters = fmap (\(name, _) -> JS.compileLocalCoreName name) parameters

            jsBody <- compileFunctionBody statements result
            pure [JS.Function (JS.compileGlobalName name) jsParameters jsBody]

compileStatements :: (Compile es) => Seq Core.Statement -> Eff es (Seq JS.Statement)
compileStatements = \case
    Empty -> pure []
    Core.Let _ _ Core.Unreachable :<| _rest -> do
        pure [JS.Panic (JS.StringLiteral "unreachable code evaluated")]
    Core.Let name _representation expr :<| rest -> do
        (statements, expr) <- compileExpr expr
        remainingStatements <- compileStatements rest
        pure (statements <> [JS.Const (JS.compileLocalCoreName name) expr] <> remainingStatements)
    Core.LetFunction
        { name
        , parameters
        , returnRepresentation = _
        , statements
        , result
        }
        :<| rest -> do
            let jsParameters = fmap (\(name, _) -> JS.compileLocalCoreName name) parameters

            jsBody <- compileFunctionBody statements result

            remainingStatements <- compileStatements rest
            pure $ (JS.Function (JS.compileLocalCoreName name) jsParameters jsBody) :<| remainingStatements
    Core.LetJoin{name, parameters, statements, result} :<| rest -> do
        let jsParameters = fmap (\(name, _) -> JS.compileLocalCoreName name) parameters
        jsBody <- compileFunctionBody statements result
        remainingStatements <- compileStatements rest
        pure $ (JS.Function (JS.compileLocalCoreName name) jsParameters jsBody) :<| remainingStatements

compileFunctionBody :: (Compile es) => Seq Core.Statement -> Core.Expr -> Eff es (Seq JS.Statement)
compileFunctionBody statements returnExpr = case statements of
    Empty -> do
        (returnStatements, returnExpr) <- compileExpr returnExpr
        pure (returnStatements <> [JS.Return returnExpr])
    Core.Let _ _ Core.Unreachable :<| _rest -> do
        pure [JS.Panic (JS.StringLiteral "unreachable code evaluated")]
    Core.Let name _representation expr :<| rest -> do
        (statements, expr) <- compileExpr expr
        remainingStatements <- compileFunctionBody rest returnExpr
        pure (statements <> [JS.Const (JS.compileLocalCoreName name) expr] <> remainingStatements)
    Core.LetFunction
        { name
        , parameters
        , returnRepresentation = _
        , statements
        , result
        }
        :<| rest -> do
            let jsParameters = fmap (\(name, _) -> JS.compileLocalCoreName name) parameters

            jsBody <- compileFunctionBody statements result

            remainingStatements <- compileFunctionBody rest result
            pure $ (JS.Function (JS.compileLocalCoreName name) jsParameters jsBody) :<| remainingStatements
    Core.LetJoin{name, parameters, statements, result} :<| rest -> do
        let jsParameters = fmap (\(name, _) -> JS.compileLocalCoreName name) parameters
        jsBody <- compileFunctionBody statements result
        remainingStatements <- compileFunctionBody rest result
        pure $ (JS.Function (JS.compileLocalCoreName name) jsParameters jsBody) :<| remainingStatements

compileExpr :: (Compile es) => Core.Expr -> Eff es (Seq JS.Statement, JS.Expr)
compileExpr = \case
    Core.Value value -> do
        jsExpr <- compileValue value
        pure ([], jsExpr)
    Core.Unreachable -> do
        pure ([JS.Panic (JS.StringLiteral "unreachable code evaluated")], JS.Undefined)
    Core.Application{function, representationArguments = _, arguments, resultRepresentation = _} -> do
        jsArguments <- for arguments compileValue
        pure ([], JS.Application (JS.Var (JS.compileCoreName function)) jsArguments)
    Core.JumpJoin name arguments -> do
        jsArguments <- for arguments compileValue
        pure ([], JS.Application (JS.Var (JS.compileLocalCoreName name)) jsArguments)
    Core.Lambda parameters statements returnExpr -> do
        let jsParameters = fmap (\(name, _) -> JS.compileLocalCoreName name) parameters
        bodyStatements <- compileFunctionBody statements returnExpr
        pure ([], JS.Lambda jsParameters bodyStatements)
    Core.ProductAccess{product, index} -> do
        jsProduct <- compileValue product
        pure ([], JS.Index jsProduct (JS.IntLiteral (fromIntegral index)))
    Core.Box x -> do
        jsExpr <- compileValue x
        pure ([], jsExpr)
    Core.Unbox{value, innerRepresentation = _} -> do
        jsExpr <- compileValue value
        pure ([], jsExpr)
    Core.PureOperator pureOperatorExpr -> do
        jsExpr <- compilePureOperatorExpr pureOperatorExpr
        pure ([], jsExpr)
    Core.ConstructorCase{scrutinee, scrutineeRepresentation = _, cases, default_} -> do
        jsScrutinee <- compileValue scrutinee
        resultVar <- newVar

        intCases <-
            fromList <$> for (HashMap.toList cases) \(key, (parameters, statements, expr)) -> do
                accessStatements <- forIndexed parameters \parameter index -> do
                    pure (JS.Const (JS.compileLocalCoreName parameter) $ productFieldAccess jsScrutinee index)
                bodyStatements <- compileStatements statements
                (exprStatements, jsExpr) <- compileExpr expr
                pure (key, accessStatements <> bodyStatements <> exprStatements <> [JS.Assign (JS.Var resultVar) jsExpr])

        default_ <- for default_ \(statements, expr) -> do
            bodyStatements <- compileStatements statements
            (exprStatements, jsExpr) <- compileExpr expr
            pure (bodyStatements <> exprStatements <> [JS.Assign (JS.Var resultVar) jsExpr])

        pure ([JS.Let resultVar Nothing] <> [JS.SwitchInt{scrutinee = jsScrutinee, intCases, default_}], JS.Var resultVar)
    Core.IntCase{scrutinee, intCases, default_} -> do
        jsScrutinee <- compileValue scrutinee
        resultVar <- newVar

        intCases <-
            fromList <$> for (HashMap.toList intCases) \(key, (statements, expr)) -> do
                bodyStatements <- compileStatements statements
                (exprStatements, jsExpr) <- compileExpr expr
                pure (key, bodyStatements <> exprStatements <> [JS.Assign (JS.Var resultVar) jsExpr])

        default_ <- for default_ \(statements, expr) -> do
            bodyStatements <- compileStatements statements
            (exprStatements, jsExpr) <- compileExpr expr
            pure (bodyStatements <> exprStatements <> [JS.Assign (JS.Var resultVar) jsExpr])

        pure ([JS.Let resultVar Nothing] <> [JS.SwitchInt{scrutinee = jsScrutinee, intCases, default_}], JS.Var resultVar)

newVar :: (Compile es) => Eff es Text
newVar = do
    unique <- liftIO newUnique
    pure $ "$gen$" <> show (hashUnique unique)

compilePureOperatorExpr :: (Compile es) => Core.PureOperatorExpr -> Eff es JS.Expr
compilePureOperatorExpr = \case
    Core.PureOperatorValue value -> compileValue value
    Core.Add left right -> simpleOperator JS.Add left right
    Core.Subtract left right -> simpleOperator JS.Subtract left right
    Core.Multiply left right -> simpleOperator JS.Multiply left right
    Core.Divide left right -> simpleOperator JS.Divide left right
    Core.Less left right -> simpleOperator JS.Less left right
    Core.LessEqual left right -> simpleOperator JS.LessEqual left right
    Core.Equal left right -> simpleOperator JS.Equal left right
    Core.NotEqual left right -> simpleOperator JS.NotEqual left right
  where
    simpleOperator binoperator left right = do
        left <- compilePureOperatorExpr left
        right <- compilePureOperatorExpr right
        pure (JS.BinaryOperator left binoperator right)

compileValue :: (Compile es) => Core.Value -> Eff es JS.Expr
compileValue = \case
    Core.Var varName -> pure $ JS.Var (JS.compileCoreName varName)
    Core.Instantiation{varName, representationArguments = _} -> pure $ JS.Var (JS.compileCoreName varName)
    Core.Literal literal -> case literal of
        Core.IntLiteral int -> pure (JS.IntLiteral int)
        Core.DoubleLiteral rational -> pure (JS.DoubleLiteral rational)
        Core.StringLiteral string -> pure (JS.StringLiteral string)
    Core.DataConstructorApplication{constructor = _, arguments, resultRepresentation = _} -> do
        -- TODO: we should actually use the index here
        undefined

-- It turns out that representing products as objects with uniformly named keys
-- is actually *much* more efficient than using (heterogeneous) arrays
productFieldAccess :: JS.Expr -> Int -> JS.Expr
productFieldAccess product index = JS.FieldAccess product ("x" <> show index)
