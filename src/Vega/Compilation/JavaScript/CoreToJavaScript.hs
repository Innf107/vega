module Vega.Compilation.JavaScript.CoreToJavaScript (compileDeclaration) where

import Relude

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Text.Internal.StrictBuilder qualified as TextBuilder
import Data.Traversable (for)
import Data.Unique (hashUnique, newUnique)
import Effectful (Eff, IOE, type (:>))
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.JavaScript.Syntax qualified as JS
import Vega.Effect.Trace (Trace)
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Syntax qualified as Vega
import Vega.Util (forIndexed)
import qualified Vega.Pretty as Pretty

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
    Core.Application{function, representationArguments = _, arguments, resultRepresentation = _}
        | Core.Global globalName <- function
        , Vega.isInternalName globalName -> do
            case HashMap.lookup globalName.name primops of
                Nothing -> panic $ "Unimplemented builtin function: " <> pretty function
                Just (_arity, makeBody) -> do
                    jsArguments <- for arguments compileValue
                    makeBody jsArguments
        | otherwise -> do
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
        pure ([], JS.FieldAccess jsProduct ("x" <> show index))
    Core.Box x -> do
        jsExpr <- compileValue x
        pure ([], jsExpr)
    Core.Unbox{value, innerRepresentation = _} -> do
        jsExpr <- compileValue value
        pure ([], jsExpr)
    Core.PureOperator pureOperatorExpr -> do
        jsExpr <- compilePureOperatorExpr pureOperatorExpr
        pure ([], jsExpr)
    Core.ConstructorCase{scrutinee, scrutineeRepresentation, cases, default_}
        | usesBooleans scrutineeRepresentation -> do
            jsScrutinee <- compileValue scrutinee
            resultVar <- newVar
            let thenBranch = HashMap.lookup 1 cases
            let elseBranch = HashMap.lookup 0 cases

            let ifThenElse (thenStatements, thenExpr) (elseStatements, elseExpr) = do
                    thenJSStatements <- compileStatements thenStatements
                    (thenReturnStatements, thenReturnExpr) <- compileExpr thenExpr
                    elseJSStatements <- compileStatements elseStatements
                    (elseReturnStatements, elseReturnExpr) <- compileExpr elseExpr
                    pure
                        (
                            [ JS.If
                                jsScrutinee
                                (thenJSStatements <> thenReturnStatements <> [JS.Assign (JS.Var resultVar) thenReturnExpr])
                                (elseJSStatements <> elseReturnStatements <> [JS.Assign (JS.Var resultVar) elseReturnExpr])
                            ]
                        , JS.Var resultVar
                        )

            let singleBranch (statements, expr) = do
                    jsStatements <- compileStatements statements
                    (returnStatements, returnExpr) <- compileExpr expr
                    pure (jsStatements <> returnStatements, returnExpr)

            case (thenBranch, elseBranch, default_) of
                (Just (_, thenStatements, thenExpr), Just (_, elseStatements, elseExpr), _) -> do
                    -- If both branches are set, we can ignore the default even if there is one
                    ifThenElse (thenStatements, thenExpr) (elseStatements, elseExpr)
                (Just (_, thenStatements, thenExpr), Nothing, Just default_) -> do
                    ifThenElse (thenStatements, thenExpr) default_
                (Nothing, Just (_, elseStatements, elseExpr), Just default_) -> do
                    ifThenElse default_ (elseStatements, elseExpr)
                (Just (_, thenStatements, thenExpr), Nothing, Nothing) -> do
                    -- Here we can assume that everything but the then branch is impossible
                    singleBranch (thenStatements, thenExpr)
                (Nothing, Just (_, elseStatements, elseExpr), Nothing) -> do
                    -- Here we can assume that everything but the else branch is impossible
                    singleBranch (elseStatements, elseExpr)
                (Nothing, Nothing, Just default_) -> do
                    singleBranch default_
                (Nothing, Nothing, Nothing) -> pure ([JS.Panic (JS.StringLiteral "empty case evaluated")], JS.Undefined)
        | otherwise -> do
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
    Core.Var varName
        | Core.Global globalName <- varName
        , Vega.isInternalName globalName -> do
            case HashMap.lookup globalName.name primops of
                Nothing -> panic $ "Unimplemented builtin function: " <> pretty varName
                Just (arity, makeBody) -> do
                    variables <- fromList <$> replicateM arity newVar
                    (bodyStatements, bodyExpr) <- makeBody (fmap JS.Var variables)
                    pure (JS.Lambda variables (bodyStatements <> [JS.Return bodyExpr]))
        | otherwise -> pure $ JS.Var (JS.compileCoreName varName)
    Core.Instantiation{varName, representationArguments = _} -> pure $ JS.Var (JS.compileCoreName varName)
    Core.Literal literal -> case literal of
        Core.IntLiteral int -> pure (JS.IntLiteral int)
        Core.DoubleLiteral rational -> pure (JS.DoubleLiteral rational)
        Core.StringLiteral string -> pure (JS.StringLiteral string)
    Core.ProductConstructor{arguments, resultRepresentation = _} -> do
        fields <- forIndexed arguments \argument i -> do
            jsArgument <- compileValue argument
            pure ("x" <> show i, jsArgument)
        pure (JS.ObjectLiteral fields)
    Core.SumConstructor{constructorIndex, payload, resultRepresentation}
        | usesBooleans resultRepresentation -> do
            case constructorIndex of
                0 -> pure $ JS.BoolLiteral False
                1 -> pure $ JS.BoolLiteral True
                _ -> panic $ "Invalid sum constructor index " <> Pretty.number constructorIndex <> " of supposedly boolean-like representation " <> pretty resultRepresentation
        | otherwise -> do
            jsPayload <- compileValue payload
            pure (JS.ObjectLiteral [("tag", JS.IntLiteral (fromIntegral constructorIndex)), ("payload", jsPayload)])

-- It turns out that representing products as objects with uniformly named keys
-- is actually *much* more efficient than using (heterogeneous) arrays
productFieldAccess :: JS.Expr -> Int -> JS.Expr
productFieldAccess product index = JS.FieldAccess product ("x" <> show index)

-- If a sum consists of exactly two constructors with unit payloads, we represent
-- it as a boolean. This means that our vega-level boolean representation will nicely
-- map onto javascript booleans and additionally gives us a nice little performance boost
-- for anything else that happens to fit the same shape.
--
-- In particular, matching on this kind of value can use if statements instead of a full switch.
usesBooleans :: Core.Representation -> Bool
usesBooleans = \case
    Core.SumRep constructors -> length constructors == 2 && all isUnitRepresentation constructors
    _ -> False

isUnitRepresentation :: Core.Representation -> Bool
isUnitRepresentation = \case
    Core.ProductRep [] -> True
    _ -> False

primops :: HashMap Text (Int, Seq JS.Expr -> Eff es (Seq JS.Statement, JS.Expr))
primops =
    [ ("debugInt", (1, \arguments -> pure $ ([], JS.Application (JS.Var "console.log") arguments)))
    ]

