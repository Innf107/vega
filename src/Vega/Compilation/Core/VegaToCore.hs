module Vega.Compilation.Core.VegaToCore (compileDeclaration) where

import Effectful
import Relude hiding (NonEmpty, State, evalState, get, modify, put, runState, trace)
import Relude qualified

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
import Vega.Effect.Trace (Category (Patterns), Trace, trace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique, runNewUnique)
import Vega.Panic (panic)
import Vega.Pretty (align, indent, intercalateDoc, keyword, pretty, (<+>))
import Vega.Seq.NonEmpty (pattern NonEmpty)
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Syntax (Pass (..))
import Vega.Syntax qualified as Vega
import Vega.Util qualified as Util
import Witherable (wither)

type Compile es =
    ( GraphPersistence :> es
    , NewUnique :> es
    , Trace :> es
    )

compileDeclaration :: (GraphPersistence :> es, IOE :> es, Trace :> es) => Vega.Declaration Typed -> Eff es (Seq Core.Declaration)
compileDeclaration declaration = do
    declarations <- runNewUnique $ compileDeclarationSyntax declaration.syntax
    traverse coalesceVariables declarations

compileDeclarationSyntax :: (Compile es) => Vega.DeclarationSyntax Typed -> Eff es (Seq Core.Declaration)
compileDeclarationSyntax = \case
    Vega.DefineFunction{ext, name, typeSignature = _, declaredTypeParameters = _, parameters, body} -> do
        coreParameters <- for parameters \(pattern_) -> do
            local <- newLocal
            pure (local, undefined pattern_)

        let caseTree = PatternMatching.serializeSubPatterns (fmap fst parameters) ()

        trace Patterns $ "compileDeclarationSyntax(" <> Vega.prettyGlobal Vega.VarKind name <> "):" <+> pretty caseTree

        (caseStatements, caseExpr) <- compileCaseTree (\() -> compileExpr body) caseTree (fmap (\(local, _) -> Core.Var (Core.Local local)) coreParameters)

        returnRepresentation <- convertRepresentation ext.returnRepresentation
        pure
            [ Core.DefineFunction
                { name
                , parameters = coreParameters
                , returnRepresentation
                , statements = caseStatements
                , result = caseExpr
                }
            ]
    Vega.DefineVariantType{} -> pure []
    Vega.DefineExternalFunction{} -> pure []

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
        Vega.PartialApplication{loc = _, functionExpr, partialArguments} -> do
            (functionStatements, function) <- compileExprToValue functionExpr
            functionName <- case function of
                Core.Var name -> pure name
                value -> panic $ "function compiled to non-variable value: " <> pretty value <> ". this should have been a type error"
            (locals, argumentStatements, arguments) <-
                Util.unzip3Seq <$> for partialArguments \case
                    Nothing -> do
                        local <- newLocal
                        representation <- undefined
                        pure ([(local, representation)], [], Core.Var (Core.Local local))
                    Just vegaExpr -> do
                        (exprStatements, value) <- compileExprToValue vegaExpr
                        pure ([], exprStatements, value)
            pure (functionStatements <> fold argumentStatements, Core.Lambda (fold locals) [] (Core.Application functionName arguments))
        Vega.VisibleTypeApplication{} -> deferToValue
        Vega.Lambda{parameters, body} -> do
            let caseTree = PatternMatching.serializeSubPatterns parameters ()
            variables <- for parameters \_ -> do
                local <- newLocal
                representation <- undefined
                pure (local, representation)
            (bodyStatements, body) <- compileCaseTree (\() -> compileExpr body) caseTree (fmap (\(localName, _) -> Core.Var (Core.Local localName)) variables)
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
            representation <- undefined
            name <- newLocal
            pure (statements <> [Core.Let name representation expr], Core.Var (Core.Local name))
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
        Vega.PartialApplication{} -> deferToLet
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
        representation <- undefined expr
        (statements, coreExpr) <- compileExpr expr
        (restStatements, result) <- compileStatements rest
        pure (statements <> [Core.Let local representation coreExpr] <> restStatements, result)
    (Vega.Let _ pattern_ expr :<| rest) -> do
        (scrutineeStatements, scrutineeValue) <- compileExprToValue expr

        let caseTree = PatternMatching.serializeSubPatterns [pattern_] ()

        (statements, finalExpr) <- compileCaseTree (\() -> compileStatements rest) caseTree [scrutineeValue]
        pure (scrutineeStatements <> statements, finalExpr)
    (Vega.LetFunction{ext, name, parameters, typeSignature=_, body} :<| rest) -> do
        coreParameters <- for parameters \(_pattern, vegaRepresentation) -> do
            local <- newLocal
            representation <- convertRepresentation vegaRepresentation
            pure (local, representation)

        let caseTree = PatternMatching.serializeSubPatterns (fmap fst parameters) ()

        trace Patterns $ "LetFunction(" <> Vega.prettyLocal Vega.VarKind name <> "):" <+> pretty caseTree

        (caseStatements, caseExpr) <-
            compileCaseTree
                (\() -> compileExpr body)
                caseTree
                (fmap (\(local, _) -> Core.Var (Core.Local local)) coreParameters)

        returnRepresentation <- convertRepresentation ext.returnRepresentation

        (remainingStatements, finalExpr) <- compileStatements rest
        pure
            ( Core.LetFunction
                { name = Core.UserProvided name
                , parameters = coreParameters
                , returnRepresentation
                , statements = caseStatements
                , result = caseExpr
                }
                :<| remainingStatements
            , finalExpr
            )
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
                let accessStatements = Seq.mapWithIndex (\i local -> Core.Let local undefined (Core.TupleAccess scrutinee i)) locals

                (subTreeStatements, subTreeExpr) <- go (fmap (Core.Var . Core.Local) locals <> rest) boundValues subTree
                pure (accessStatements <> subTreeStatements, subTreeExpr)
            PatternMatching.BindVar name vegaRepresentation subTree -> do
                let (scrutinee, _) = consume scrutinees
                (subStatements, subExpr) <- go scrutinees (boundValues :|> Core.UserProvided name) subTree
                representation <- convertRepresentation vegaRepresentation
                pure ([Core.Let (Core.UserProvided name) representation (Core.Value scrutinee)] <> subStatements, subExpr)
            PatternMatching.Ignore subTree -> do
                let (_, rest) = consume scrutinees
                go rest boundValues subTree

    (caseStatements, caseExpr) <- go scrutinees [] caseTree

    let joinPointDefinitions = fromList $ map (\(_, statement) -> statement) (toList joinPoints)
    pure (joinPointDefinitions <> caseStatements, caseExpr)

boundVarsAndFrequencies :: forall goal. (Hashable goal) => CaseTree goal -> HashMap goal (Seq (Core.LocalCoreName, Core.Representation), Int)
boundVarsAndFrequencies tree = flip execState mempty $ do
    PatternMatching.traverseLeavesWithBoundVars tree \locals goal -> do
        Relude.modify $ flip alter goal \case
            Nothing -> do
                let localsWithRepresentations = fmap (\local -> (Core.UserProvided local, undefined)) locals
                Just (localsWithRepresentations, 1)
            Just (locals, count) -> Just (locals, count + 1)

newLocal :: (Compile es) => Eff es Core.LocalCoreName
newLocal = do
    unique <- newUnique
    pure (Core.Generated unique)

booleanConstructorName :: Bool -> Vega.Name
booleanConstructorName True = Vega.Global (Vega.internalName "True")
booleanConstructorName False = Vega.Global (Vega.internalName "False")

{- | Convert a representation represented as a vega type (of kind `Rep`) to a core representation.
This is mostly blind unwrapping and following meta variables, except for the case for unbound meta variables where
we give them representation `Unit` (which is like defaulting them to `()` but friendlier for error messages)
-}
convertRepresentation :: (Compile es) => Vega.Type -> Eff es Core.Representation
convertRepresentation type_ = do
    let invalidKind = panic $ "Invalid representation in conversion to Core: " <> pretty type_ <> "\n    This should have been caught in the type checker."
    case type_ of
        Vega.MetaVar{} -> pure $ Core.ProductRep []
        Vega.SumRep representations -> Core.SumRep <$> traverse convertRepresentation representations
        Vega.ProductRep representations -> Core.ProductRep <$> traverse convertRepresentation representations
        Vega.ArrayRep inner -> Core.ArrayRep <$> convertRepresentation inner
        Vega.PrimitiveRep rep -> pure $ Core.PrimitiveRep rep
        Vega.Skolem{} -> undefined
        Vega.TypeConstructor{} -> invalidKind
        Vega.TypeApplication{} -> invalidKind
        Vega.TypeVar{} -> undefined
        Vega.Forall{} -> invalidKind
        Vega.Exists{} -> invalidKind
        Vega.Function{} -> invalidKind
        Vega.Tuple{} -> invalidKind
        Vega.Pure{} -> invalidKind
        Vega.Rep{} -> invalidKind
        Vega.Type{} -> invalidKind
        Vega.Effect{} -> invalidKind
        Vega.Kind{} -> invalidKind

type Substitution = HashMap Core.LocalCoreName Core.Value

coalesceVariables :: Core.Declaration -> Eff es Core.Declaration
coalesceVariables = \case
    Core.DefineFunction name parameters returnRepresentation statements returnExpr -> do
        let substitution :: Substitution = mempty
        (substitution, makeStatements) <- coalesceStatements substitution statements
        (substitution, makeReturnExpr) <- coalesceExpr substitution returnExpr
        pure
            ( Core.DefineFunction
                name
                (fmap (first (getFinalName substitution)) parameters)
                returnRepresentation
                (makeStatements substitution)
                (makeReturnExpr substitution)
            )

coalesceStatements :: Substitution -> Seq Core.Statement -> Eff es (Substitution, Substitution -> Seq Core.Statement)
coalesceStatements substitution = \case
    Empty -> pure (substitution, \_ -> Empty)
    Core.Let name _representation (Core.Value value) :<| rest -> do
        substitution <- coalesceBinding name value substitution
        (substitution, makeRest) <- coalesceStatements substitution rest
        pure (substitution, makeRest)
    Core.Let name representation expr :<| rest -> do
        (substitution, makeExpr) <- coalesceExpr substitution expr
        (substitution, makeRest) <- coalesceStatements substitution rest
        pure
            ( substitution
            , \substitution -> do
                Core.Let (getFinalName substitution name) representation (makeExpr substitution) :<| makeRest substitution
            )
    Core.LetJoin name parameters statements returnExpr :<| rest -> do
        (substitution, makeStatements) <- coalesceStatements substitution statements
        (substitution, makeExpr) <- coalesceExpr substitution returnExpr
        (substitution, makeRest) <- coalesceStatements substitution rest
        pure
            ( substitution
            , \substitution -> do
                Core.LetJoin
                    name
                    (fmap (\(name, representation) -> (getFinalName substitution name, representation)) parameters)
                    (makeStatements substitution)
                    (makeExpr substitution)
                    :<| makeRest substitution
            )
    Core.LetFunction{name, parameters, returnRepresentation, statements, result} :<| rest -> do
        (substitution, makeStatements) <- coalesceStatements substitution statements
        (substitution, makeResult) <- coalesceExpr substitution result
        (substitution, makeRest) <- coalesceStatements substitution rest
        pure
            ( substitution
            , \substitution -> do
                Core.LetFunction
                    { name
                    , parameters = fmap (\(name, representation) -> (getFinalName substitution name, representation)) parameters
                    , returnRepresentation
                    , statements = makeStatements substitution
                    , result = makeResult substitution
                    }
                    :<| makeRest substitution
            )

coalesceExpr :: Substitution -> Core.Expr -> Eff es (Substitution, Substitution -> Core.Expr)
coalesceExpr substitution = \case
    Core.Value value -> pure (substitution, \substitution -> Core.Value (applySubst substitution value))
    Core.Application functionName argValues ->
        pure
            ( substitution
            , \substitution -> do
                let name = case functionName of
                        Core.Local localName -> Core.Local (getFinalName substitution localName)
                        Core.Global globalName -> Core.Global globalName
                Core.Application name (fmap (applySubst substitution) argValues)
            )
    Core.JumpJoin joinPoint arguments ->
        pure
            ( substitution
            , \substitution ->
                Core.JumpJoin joinPoint (fmap (applySubst substitution) arguments)
            )
    Core.Lambda parameters statements expr -> do
        (substitution, makeStatements) <- coalesceStatements substitution statements
        (substitution, makeExpr) <- coalesceExpr substitution expr
        pure
            ( substitution
            , \substitution ->
                Core.Lambda
                    (fmap (\(name, representation) -> (getFinalName substitution name, representation)) parameters)
                    (makeStatements substitution)
                    (makeExpr substitution)
            )
    Core.TupleAccess value index -> pure (substitution, \substitution -> Core.TupleAccess (applySubst substitution value) index)
    Core.ConstructorCase scrutinee cases -> do
        let coalesceCase substitution (parameters, statements, expr) = do
                (substitution, makeStatements) <- coalesceStatements substitution statements
                (substitution, makeExpr) <- coalesceExpr substitution expr
                pure
                    ( substitution
                    , \substitution ->
                        (fmap (getFinalName substitution) parameters, makeStatements substitution, makeExpr substitution)
                    )
        (substitution, makeCases) <- Util.mapAccumLM coalesceCase substitution cases
        pure
            ( substitution
            , \substitution ->
                Core.ConstructorCase (applySubst substitution scrutinee) (fmap ($ substitution) makeCases)
            )

applySubst :: Substitution -> Core.Value -> Core.Value
applySubst substitution = \case
    Core.Var (Core.Global globalName) -> Core.Var (Core.Global globalName)
    Core.Var (Core.Local localName) -> getFinalValue substitution localName
    Core.Literal literal -> Core.Literal literal
    Core.DataConstructorApplication constructor arguments ->
        Core.DataConstructorApplication constructor (fmap (applySubst substitution) arguments)

coalesceBinding :: (HasCallStack) => Core.LocalCoreName -> Core.Value -> Substitution -> Eff es Substitution
coalesceBinding name newValue substitution = case newValue of
    Core.Var (Core.Local localVar) -> case getFinalValue substitution localVar of
        Core.Var (Core.Local nextVar) -> do
            let chosenName = Core.Var (Core.Local (chooseName name nextVar))
            pure $ HashMap.insert name chosenName (HashMap.insert nextVar chosenName substitution)
        value -> pure $ (HashMap.insert name value substitution)
    _ -> pure (HashMap.insert name newValue substitution)

chooseName :: Core.LocalCoreName -> Core.LocalCoreName -> Core.LocalCoreName
chooseName _ (Core.UserProvided name) = Core.UserProvided name
chooseName (Core.UserProvided name) _ = Core.UserProvided name
chooseName _ name = name

getFinalValue :: (HasCallStack) => Substitution -> Core.LocalCoreName -> Core.Value
getFinalValue substitution var = case HashMap.lookup var substitution of
    Just (Core.Var (Core.Local nextLocal))
        | nextLocal == var -> Core.Var (Core.Local nextLocal)
        | otherwise -> getFinalValue substitution nextLocal
    Just value -> value
    Nothing -> (Core.Var (Core.Local var))

getFinalName :: (HasCallStack) => Substitution -> Core.LocalCoreName -> Core.LocalCoreName
getFinalName substitution name = case getFinalValue substitution name of
    Core.Var (Core.Local name) -> name
    value -> panic $ "supposed parameter " <> pretty name <> " was coalesced with a non-local value: " <> pretty value
