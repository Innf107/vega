{-# OPTIONS_GHC -Wno-type-defaults #-}

{- | Vega to JavaScript compilation. This goes directly from the type checked Vega code
    without performing any optimizations or further transformations.

    "Dead code elimination" is however automatically performed on declarations, since we only compile the ones that
    are reachable from the entry point anyway.
-}
module Vega.Compilation.JavaScript.VegaToJavaScript (compileDeclaration) where

import Relude hiding (State, evalState, get, intercalate, modify, put, trace)

import Effectful

import TextBuilder qualified

import Data.Map qualified as Map
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Data.Unique (hashUnique, newUnique)
import Vega.Compilation.JavaScript.Syntax qualified as JS
import Vega.Compilation.PatternMatching (CaseTree (..))
import Vega.Compilation.PatternMatching qualified as PatternMatching
import Vega.Effect.Trace (Trace)
import Vega.Panic (panic)
import Vega.Pretty (localIdentText)
import Vega.Seq.NonEmpty (NonEmpty (..), pattern NonEmpty)
import Vega.Syntax
import qualified Vega.Seq.NonEmpty as NonEmpty

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

        body <- compileSequentialPatterns (Seq.zipWith (\var (pattern_, _) -> (var, pattern_)) parameterVariables parameters) body

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
    DefineExternalFunction{} -> pure []

compileExpr :: (Compile es) => Expr Typed -> Eff es JS.Expr
compileExpr = \case
    Var _ (Global builtinName)
        | isInternalName builtinName -> compileBuiltinVar builtinName.name
    Var _ varName -> pure $ JS.Var (JS.compileName varName)
    DataConstructor{valueRepresentation = _, name} -> pure $ JS.Var (JS.compileName name)
    Application _ _representation funExpr argExprs -> do
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
    RecordLiteral _ fields -> do
        jsFields <- for (NonEmpty.toSeq fields) \(name, expr) -> do
            jsExpr <- compileExpr expr
            pure (name, jsExpr)
        pure $ JS.ObjectLiteral jsFields
    BinaryOperator _ left operator right -> do
        leftExpr <- compileExpr left
        rightExpr <- compileExpr right
        pure (JS.BinaryOperator leftExpr (binaryOperatorToJS operator) rightExpr)
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

compileBuiltinVar :: (Compile es) => Text -> Eff es JS.Expr
compileBuiltinVar = \case
    "panic" -> do
        var <- freshVar "msg"
        pure
            ( JS.Lambda
                [var]
                [ JS.Panic (JS.Var var)
                ]
            )
    "replicateArray" -> pure (JS.Var ("internal$replicateArray"))
    "readArray" -> pure (JS.Var "internal$readArray")
    "arrayLength" -> do
        array <- freshVar "array"
        pure (JS.Lambda [array] [JS.Return (JS.FieldAccess (JS.Var array) "length")])
    "codePoints" -> pure (JS.Var "internal$codePoints")
    var -> panic $ "Builtin variable not implemented in the javascript backend: " <> localIdentText var

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
        matchStatements <- compileCaseTree (\_ -> pure rest) [varName] caseTree

        pure $ ([JS.Const varName jsExpr] <> matchStatements)
    LetFunction{name, typeSignature = _, parameters, body} -> do
        parameterVariables <- for parameters \_ -> freshVar "x"

        body <- compileSequentialPatterns (Seq.zipWith (\var (pattern_, _) -> (var, pattern_)) parameterVariables parameters) body

        rest <- compileStatements rest

        pure (JS.Function (JS.compileLocalName name) parameterVariables body :<| rest)
    Use{} -> undefined

compileSequentialPatterns :: (Compile es) => Seq (JS.Name, Pattern Typed) -> Expr Typed -> Eff es (Seq JS.Statement)
compileSequentialPatterns scrutineesAndPatterns expr = do
    let caseTree = PatternMatching.serializeSubPatterns (fmap snd scrutineesAndPatterns) expr

    compileCaseTree compileLeaf (fmap fst scrutineesAndPatterns) caseTree

compilePatternMatch :: (Compile es) => JS.Name -> Seq (MatchCase Typed) -> Eff es (Seq JS.Statement)
compilePatternMatch scrutinee cases = case cases of
    Empty -> pure [JS.Panic (JS.StringLiteral "empty match expression evaluated")]
    NonEmpty cases -> do
        let caseTree = PatternMatching.compileMatch (fmap (\MkMatchCase{pattern_, body} -> (pattern_, body)) cases)
        compileCaseTree compileLeaf [scrutinee] caseTree

compileLeaf :: (Compile es) => Expr Typed -> Eff es (Seq JS.Statement)
compileLeaf expr = do
    jsExpr <- compileExpr expr
    pure [JS.Return jsExpr]

-- TODO: Unlike VegaToCore, this currently doesn't attempt to deduplicate join points at all.
-- However, in the future, we're going to replace this entire module with CoreToJavaScript anyway
-- so it's probably not worth the effort.
compileCaseTree :: (Compile es) => (goal -> Eff es (Seq JS.Statement)) -> Seq JS.Name -> CaseTree goal -> Eff es (Seq JS.Statement)
compileCaseTree compileGoal scrutinees caseTree = go scrutinees caseTree
  where
    go scrutinees = \case
        Leaf goal -> compileGoal goal
        ConstructorCase{constructors, default_} -> do
            let (scrutinee, rest) = consume scrutinees
            cases <-
                fromList <$> for (Map.toList constructors) \(constructor, (parameterCount, continuation)) -> case parameterCount of
                    0 -> do
                        statements <- go rest continuation
                        pure (JS.compileName constructor, statements)
                    _ -> do
                        payloadVariables <- Seq.replicateM parameterCount (freshVar "p")
                        statements <- go (payloadVariables <> rest) continuation
                        pure
                            ( JS.compileName constructor
                            , JS.DestructureArray payloadVariables (JS.FieldAccess (JS.Var scrutinee) "payload")
                                :<| statements
                            )
            default_ <- traverse (go rest) default_
            pure
                [ JS.SwitchString
                    { scrutinee = JS.FieldAccess (JS.Var scrutinee) "tag"
                    , default_
                    , cases
                    }
                ]
        TupleCase count subTree -> do
            variables <- Seq.replicateA count (freshVar "t")
            let (scrutinee, rest) = consume scrutinees
            subTreeStatements <- go (variables <> rest) subTree
            pure $ JS.DestructureArray variables (JS.Var scrutinee) :<| subTreeStatements
        BindVar name _representation subTree -> do
            let (scrutinee, _) = consume scrutinees
            subTreeStatements <- go scrutinees subTree
            pure $ JS.Const (JS.compileLocalName name) (JS.Var scrutinee) :<| subTreeStatements
        Ignore subTree -> do
            let (_, rest) = consume scrutinees
            go rest subTree
    consume :: (HasCallStack) => Seq JS.Name -> (JS.Name, Seq JS.Name)
    consume Empty = panic "Consumed more scrutinees than were produced"
    consume (x :<| xs) = (x, xs)

binaryOperatorToJS :: BinaryOperator -> JS.BinaryOperator
binaryOperatorToJS = \case
    Add -> JS.Add
    Subtract -> JS.Subtract
    Multiply -> JS.Multiply
    Divide -> JS.Divide
    And -> JS.And
    Or -> JS.Or
    Less -> JS.Less
    LessEqual -> JS.LessEqual
    Equal -> JS.Equal
    NotEqual -> JS.NotEqual
    GreaterEqual -> JS.GreaterEqual
    Greater -> JS.Greater
