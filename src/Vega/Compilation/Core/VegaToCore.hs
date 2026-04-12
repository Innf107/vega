module Vega.Compilation.Core.VegaToCore (compileDeclaration) where

import Effectful (Eff, IOE, (:>))
import Relude hiding (
    NonEmpty,
    Reader,
    State,
    ask,
    evalState,
    get,
    local,
    modify,
    put,
    runReader,
    runState,
    trace,
 )
import Relude qualified

import Data.HashMap.Strict (alter)
import Data.HashMap.Strict qualified as HashMap
import Data.Map qualified as Map
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Effectful.Reader.Static (Reader, ask, runReader)
import Vega.Compilation.Core.Syntax (nameToCoreName, stringRepresentation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.PatternMatching (CaseTree)
import Vega.Compilation.PatternMatching qualified as PatternMatching
import Vega.Debruijn qualified as Debruijn
import Vega.Debug (showHeadConstructor)
import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Effect.Meta.Static (BindMeta, ReadMeta, followMetasWithoutPathCompression, runMeta)
import Vega.Effect.Meta.Static qualified as Meta
import Vega.Effect.Trace (Category (CoreRep, Patterns), Trace, trace, withTrace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique, runNewUnique)
import Vega.Panic (panic)
import Vega.Pretty (align, indent, intercalateDoc, keyword, pretty, (<+>))
import Vega.Seq.NonEmpty (pattern NonEmpty)
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Syntax (Pass (..))
import Vega.Syntax qualified as Vega
import Vega.Util (assert)
import Vega.Util qualified as Util
import Vega.VectorMap qualified as VectorMap
import Witherable (wither)

type Compile es =
    ( GraphPersistence :> es
    , NewUnique :> es
    , Trace :> es
    , Reader Env :> es
    , ReadMeta :> es
    )

newtype Env = MkEnv {monomorphizableRepresentationVariables :: HashMap Vega.LocalName Debruijn.Index}

envAndLimitFromRepresentationVariables :: Seq Vega.LocalName -> (Env, Debruijn.Limit)
envAndLimitFromRepresentationVariables variables = go Debruijn.initial HashMap.empty variables
  where
    go limit mapping Empty =
        ( MkEnv
            { monomorphizableRepresentationVariables = mapping
            }
        , limit
        )
    go oldLimit mapping (var :<| rest) = do
        let (newLimit, index) = Debruijn.new oldLimit
        go newLimit (HashMap.insert var index mapping) rest

compileDeclaration ::
    (GraphPersistence :> es, IOE :> es, Trace :> es) =>
    Vega.Declaration Typed ->
    Eff es (Seq Core.Declaration)
compileDeclaration declaration = do
    declarations <- runNewUnique $ runMeta $ compileDeclarationSyntax declaration.name declaration.syntax
    traverse coalesceVariables declarations

compileDeclarationSyntax ::
    (GraphPersistence :> es, Trace :> es, NewUnique :> es, ReadMeta :> es) =>
    Vega.DeclarationName ->
    Vega.DeclarationSyntax Typed ->
    Eff es (Seq Core.Declaration)
compileDeclarationSyntax _declarationName = \case
    Vega.DefineFunction{ext, name, typeSignature = _, declaredTypeParameters = _, parameters, body} -> do
        GraphPersistence.setGlobalRepresentation name GraphPersistence.GlobalClosure

        monomorphizableRepresentationVariables <- extractMonomorphizableRepresentationVariables ext.forallBinders
        let (env, representationParameters) = envAndLimitFromRepresentationVariables monomorphizableRepresentationVariables
        runReader env do
            coreParameters <- for parameters \(_pattern, vegaRepresentation) -> do
                representation <- convertRepresentation vegaRepresentation
                local <- newLocal
                pure (local, representation)

            let caseTree = PatternMatching.serializeSubPatterns (fmap fst parameters) ()

            trace Patterns $ "compileDeclarationSyntax(" <> Vega.prettyGlobal Vega.VarKind name <> "):" <+> pretty caseTree

            (caseStatements, caseExpr) <- compileCaseTree (\() -> compileExpr_ body) caseTree (fmap (\(local, _) -> Core.Var (Core.Local local)) coreParameters)

            returnRepresentation <- convertRepresentation ext.returnRepresentation
            pure
                [ Core.DefineFunction
                    { name
                    , parameters = coreParameters
                    , returnRepresentation
                    , statements = caseStatements
                    , result = caseExpr
                    , representationParameters = representationParameters
                    }
                ]
    Vega.DefineVariantType{constructors} -> pure []
    Vega.DefineExternalFunction{} -> pure []

-- | Like 'compileExpr' but discards the representation
compileExpr_ :: (Compile es) => Vega.Expr Typed -> Eff es (Seq Core.Statement, Core.Expr)
compileExpr_ expr = do
    (statements, returnExpr, _representation) <- compileExpr expr
    pure (statements, returnExpr)

compileExpr :: (Compile es) => Vega.Expr Typed -> Eff es (Seq Core.Statement, Core.Expr, Core.Representation)
compileExpr expr = do
    let deferToValue = do
            (statements, value, representation) <- compileExprToValue expr
            pure (statements, Core.Value value, representation)
    case expr of
        Vega.Var{} -> deferToValue
        Vega.DataConstructor{valueRepresentation, name} ->
            arityOfDataConstructor name >>= \case
                Nothing -> deferToValue
                Just arity -> do
                    -- TODO: We need more than the arity here. We actually need the *representations* of the arguments.
                    -- This is particularly annoying because we do have the *types* of the arguments but we don't have a
                    -- way of accessing their kinds from here
                    undefined
        Vega.Application _ _ (Vega.DataConstructor{}) _ -> deferToValue
        Vega.Application _ returnRepresentation functionExpr argExprs -> do
            (functionStatements, function) <- compileExprToValue_ functionExpr
            (argumentStatements, arguments) <-
                Seq.unzip <$> for argExprs \argument -> do
                    compileExprToValue_ argument
            functionVar <- case function of
                Core.Var name -> pure name
                value -> panic $ "function compiled to non-variable value: " <> pretty value <> ". this should have been a type error"

            returnRepresentation <- convertRepresentation returnRepresentation
            pure (functionStatements <> fold argumentStatements, Core.Application functionVar arguments returnRepresentation, returnRepresentation)
        Vega.PartialApplication{loc = _, functionExpr, partialArguments} -> do
            (functionStatements, function, _) <- compileExprToValue functionExpr
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
                        (exprStatements, value) <- compileExprToValue_ vegaExpr
                        pure ([], exprStatements, value)
            pure (functionStatements <> fold argumentStatements, Core.Lambda (fold locals) [] (Core.Application functionName arguments undefined), undefined)
        Vega.VisibleTypeApplication{} -> deferToValue
        Vega.Lambda{parameters, body} -> do
            let caseTree = PatternMatching.serializeSubPatterns parameters ()
            variables <- for parameters \_ -> do
                local <- newLocal
                representation <- undefined
                pure (local, representation)
            (bodyStatements, body) <- compileCaseTree (\() -> compileExpr_ body) caseTree (fmap (\(localName, _) -> Core.Var (Core.Local localName)) variables)
            pure ([], Core.Lambda variables bodyStatements body, Core.functionRepresentation)
        Vega.StringLiteral{} -> deferToValue
        Vega.IntLiteral{} -> deferToValue
        Vega.DoubleLiteral{} -> deferToValue
        Vega.TupleLiteral{} -> deferToValue
        Vega.RecordLiteral{} -> deferToValue
        Vega.BinaryOperator _loc left operator right -> case operator of
            -- Short-circuiting operators
            Vega.And
            Vega.Or -> do
                    (leftStatements, left, leftRepresentation) <- compileExprToValue left
                    assert (leftRepresentation == Core.boolRepresentation)

                    (rightStatements, right, rightRepresentation) <- compileExpr right
                    assert (rightRepresentation == Core.boolRepresentation)

                    let expr = case operator of
                            Vega.And ->
                                Core.ConstructorCase
                                    { scrutinee = left
                                    , scrutineeRepresentation = Core.boolRepresentation
                                    , cases =
                                        [ (0, ([], [], Core.Value Core.falseValue))
                                        , (1, ([], rightStatements, right))
                                        ]
                                    , default_ = Nothing
                                    }
                            Vega.Or ->
                                Core.ConstructorCase
                                    { scrutinee = left
                                    , scrutineeRepresentation = Core.boolRepresentation
                                    , cases = [(0, ([], rightStatements, right)), (1, ([], [], Core.Value Core.trueValue))]
                                    , default_ = Nothing
                                    }

                    pure (leftStatements, expr, Core.boolRepresentation)
            -- Regular operators
            _ -> do
                (leftStatements, leftExpr, leftRepresentation) <- compileExpr left
                (rightStatements, rightExpr, rightRepresentation) <- compileExpr right
                let asOperatorExpr representation expr = case expr of
                        Core.PureOperator operatorExpr -> pure ([], operatorExpr)
                        _ -> do
                            local <- newLocal
                            pure ([Core.Let local representation expr], Core.PureOperatorValue (Core.Var (Core.Local local)))
                (leftBindStatements, left) <- asOperatorExpr leftRepresentation leftExpr
                (rightBindStatements, right) <- asOperatorExpr rightRepresentation rightExpr
                let (pureOperator, representation) = case operator of
                        -- TODO: these only work on integers *for now*, but that will change in the future
                        Vega.Add -> (Core.Add left right, Core.PrimitiveRep Vega.IntRep)
                        Vega.Subtract -> (Core.Subtract left right, Core.PrimitiveRep Vega.IntRep)
                        Vega.Multiply -> (Core.Multiply left right, Core.PrimitiveRep Vega.IntRep)
                        Vega.Divide -> (Core.Divide left right, Core.PrimitiveRep Vega.IntRep)
                        Vega.Less -> (Core.Less left right, Core.boolRepresentation)
                        Vega.LessEqual -> (Core.LessEqual left right, Core.boolRepresentation)
                        Vega.Equal -> (Core.Equal left right, Core.boolRepresentation)
                        Vega.NotEqual -> (Core.NotEqual left right, Core.boolRepresentation)
                        Vega.GreaterEqual -> (Core.LessEqual right left, Core.boolRepresentation)
                        Vega.Greater -> (Core.Less right left, Core.boolRepresentation)
                pure (leftStatements <> leftBindStatements <> rightStatements <> rightBindStatements, Core.PureOperator pureOperator, representation)
        Vega.If{condition, thenBranch, elseBranch} -> do
            (conditionStatements, conditionValue) <- compileExprToValue_ condition
            (thenStatements, thenExpr, thenRepresentation) <- compileExpr thenBranch
            (elseStatements, elseExpr, elseRepresentation) <- compileExpr elseBranch
            assert (thenRepresentation == elseRepresentation)
            pure
                ( conditionStatements
                , Core.ConstructorCase
                    { scrutinee = conditionValue
                    , scrutineeRepresentation = Core.boolRepresentation
                    , cases =
                        [ (1, ([], thenStatements, thenExpr))
                        , (0, ([], elseStatements, elseExpr))
                        ]
                    , default_ = Nothing
                    }
                , thenRepresentation
                )
        Vega.SequenceBlock{statements} -> compileStatements statements
        Vega.Match{scrutinee, cases, returnRepresentation} -> do
            (statements, returnExpr) <- compilePatternMatch scrutinee (fmap (\Vega.MkMatchCase{pattern_, body} -> (pattern_, body)) cases)
            returnRepresentation <- convertRepresentation returnRepresentation
            pure (statements, returnExpr, returnRepresentation)

-- | Like 'compileExprToValue' but discards the representation
compileExprToValue_ :: (Compile es) => Vega.Expr Typed -> Eff es (Seq Core.Statement, Core.Value)
compileExprToValue_ expr = do
    (statements, value, _representation) <- compileExprToValue expr
    pure (statements, value)

compileExprToValue :: (Compile es) => Vega.Expr Typed -> Eff es (Seq Core.Statement, Core.Value, Core.Representation)
compileExprToValue expr = do
    let deferToLet = do
            (statements, expr, representation) <- compileExpr expr
            name <- newLocal
            pure (statements <> [Core.Let name representation expr], Core.Var (Core.Local name), representation)
    case expr of
        Vega.Var{loc = _, name, representation = vegaRepresentation} -> do
            representation <- convertRepresentation vegaRepresentation
            pure ([], Core.Var (nameToCoreName name), representation)
        Vega.DataConstructor _ vegaRepresentation name -> do
            representation <- convertRepresentation vegaRepresentation
            arityOfDataConstructor name >>= \case
                Nothing -> do
                    pure
                        ( []
                        , Core.DataConstructorApplication (Core.UserDefinedConstructor name) [] representation
                        , representation
                        )
                Just _ -> do
                    deferToLet
        Vega.Application _ returnRepresentation (Vega.DataConstructor _ _representation name) argumentExprs -> do
            (argumentStatements, arguments) <- Seq.unzip <$> for argumentExprs compileExprToValue_
            returnRepresentation <- convertRepresentation returnRepresentation
            (constructorStatements, constructorExpr) <- userDefinedDataConstructorApplication name arguments returnRepresentation
            pure
                ( fold argumentStatements <> constructorStatements
                , constructorExpr
                , returnRepresentation
                )
        Vega.Application{} -> deferToLet
        Vega.PartialApplication{} -> deferToLet
        -- We can erase type applications since Core is untyped
        Vega.VisibleTypeApplication{varName} -> pure ([], Core.Var (nameToCoreName varName), undefined)
        Vega.Lambda{} -> deferToLet
        Vega.StringLiteral _loc literal -> pure ([], Core.Literal (Core.StringLiteral literal), stringRepresentation)
        Vega.IntLiteral _loc literal -> pure ([], Core.Literal (Core.IntLiteral literal), Core.PrimitiveRep Vega.IntRep)
        Vega.DoubleLiteral _loc literal -> pure ([], Core.Literal (Core.DoubleLiteral literal), Core.PrimitiveRep Vega.DoubleRep)
        Vega.TupleLiteral _loc elements -> do
            (statements, elementValues, elementRepresentations) <- Util.unzip3Seq <$> for elements compileExprToValue
            let representation = Core.ProductRep elementRepresentations
            pure
                ( fold statements
                , Core.DataConstructorApplication (Core.TupleConstructor (length elementValues)) elementValues representation
                , representation
                )
        Vega.RecordLiteral _loc fields -> do
            let values = fmap snd $ sortBy (compare `on` fst) (toList fields)
            (statements, elementValues, elementRepresentations) <- unzip3 <$> for values compileExprToValue
            let representation = Core.ProductRep (fromList elementRepresentations)
            pure
                ( fold statements
                , Core.DataConstructorApplication (Core.TupleConstructor (length elementValues)) (fromList elementValues) representation
                , representation
                )
        Vega.BinaryOperator{} -> deferToLet
        Vega.If{} -> deferToLet
        Vega.SequenceBlock{} -> deferToLet
        Vega.Match{} -> deferToLet

-- | Compile a user-defined data constructor application, including auto-boxing
userDefinedDataConstructorApplication :: (Compile es) => Vega.Name -> Seq Core.Value -> Core.Representation -> Eff es (Seq Core.Statement, Core.Value)
userDefinedDataConstructorApplication name arguments representation = do
    autoBoxingFlags <- case name of
        Vega.Local{} -> undefined
        Vega.Global globalName -> GraphPersistence.getAutoBoxing globalName

    (statements, newArguments) <- Util.forAccumLM [] (Seq.zip arguments autoBoxingFlags) \statements (argument, shouldBeBoxed) -> do
        if shouldBeBoxed
            then do
                boxedVar <- newLocal
                pure
                    ( statements :|> Core.Let boxedVar (Core.PrimitiveRep Vega.BoxedRep) (Core.Box argument)
                    , Core.Var (Core.Local boxedVar)
                    )
            else
                pure (statements, argument)

    pure (statements, Core.DataConstructorApplication (Core.UserDefinedConstructor name) newArguments representation)

-- | Like 'compileStatements' but discards the representation
compileStatements_ ::
    (Compile es) =>
    Seq (Vega.Statement Typed) ->
    Eff es (Seq Core.Statement, Core.Expr)
compileStatements_ statements = do
    (statements, expr, _representation) <- compileStatements statements
    pure (statements, expr)

compileStatements ::
    (Compile es) =>
    Seq (Vega.Statement Typed) ->
    Eff es (Seq Core.Statement, Core.Expr, Core.Representation)
compileStatements = \case
    Empty -> pure ([], Core.Value unitLiteral, Core.ProductRep [])
    [Vega.Run _ expr] -> compileExpr expr
    (Vega.Run _ expr :<| rest) -> do
        local <- newLocal
        (statements, coreExpr, exprRepresentation) <- compileExpr expr
        (restStatements, result, finalRepresentation) <- compileStatements rest
        pure (statements <> [Core.Let local exprRepresentation coreExpr] <> restStatements, result, finalRepresentation)
    (Vega.Let _ pattern_ expr :<| rest) -> do
        (scrutineeStatements, scrutineeValue, varRepresentation) <- compileExprToValue expr

        let caseTree = PatternMatching.serializeSubPatterns [pattern_] ()

        (statements, finalExpr) <- compileCaseTree (\() -> compileStatements_ rest) caseTree [scrutineeValue]
        pure (scrutineeStatements <> statements, finalExpr, undefined)
    (Vega.LetFunction{ext, name, parameters, typeSignature = _, body} :<| rest) -> do
        coreParameters <- for parameters \(_pattern, vegaRepresentation) -> do
            local <- newLocal
            representation <- convertRepresentation vegaRepresentation
            pure (local, representation)

        let caseTree = PatternMatching.serializeSubPatterns (fmap fst parameters) ()

        trace Patterns $ "LetFunction(" <> Vega.prettyLocal Vega.VarKind name <> "):" <+> pretty caseTree

        (caseStatements, caseExpr) <-
            compileCaseTree
                (\() -> compileExpr_ body)
                caseTree
                (fmap (\(local, _) -> Core.Var (Core.Local local)) coreParameters)

        returnRepresentation <- convertRepresentation ext.returnRepresentation

        (remainingStatements, finalExpr, finalRepresentation) <- compileStatements rest
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
            , finalRepresentation
            )
    (Vega.Use{} :<| _) -> undefined

unitLiteral :: Core.Value
unitLiteral = Core.DataConstructorApplication (Core.TupleConstructor 0) [] (Core.ProductRep [])

compilePatternMatch :: (Compile es) => Vega.Expr Typed -> Seq (Vega.Pattern Typed, Vega.Expr Typed) -> Eff es (Seq Core.Statement, Core.Expr)
compilePatternMatch scrutinee = \case
    Empty -> undefined
    NonEmpty cases -> do
        (scrutineeStatements, scrutineeValue, _) <- compileExprToValue scrutinee

        let compileGoal goal =
                case (NonEmpty.toSeq) cases Seq.!? goal of
                    Nothing -> error "tried to access a match RHS that doesn't exist"
                    Just (_, body) -> compileExpr_ body
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
            PatternMatching.ConstructorCase{constructors, scrutineeRepresentation, default_} -> do
                let (scrutinee, rest) = consume scrutinees
                cases <-
                    fromList <$> for (Map.toList constructors) \(constructor, (argumentRepresentations, subTree)) -> do
                        locals <- for argumentRepresentations \representation -> do
                            local <- newLocal
                            pure (representation, local)
                        index <-
                            GraphPersistence.getDataConstructorIndex constructor >>= \case
                                GraphPersistence.OnlyConstructor -> undefined
                                GraphPersistence.MultiConstructor index -> pure index

                        autoBoxingFlags <- case constructor of
                            Vega.Global globalName -> GraphPersistence.getAutoBoxing globalName
                            Vega.Local{} -> undefined

                        assert (length locals == length autoBoxingFlags)

                        (possiblyBoxedLocals, boxingStatements) <-
                            Seq.unzip <$> for (Seq.zip locals autoBoxingFlags) \((vegaRepresentation, local), isAutoBoxed) -> do
                                if isAutoBoxed
                                    then do
                                        representation <- convertRepresentation vegaRepresentation
                                        boxedLocal <- newLocal
                                        pure
                                            ( boxedLocal
                                            ,
                                                [ Core.Let
                                                    local
                                                    representation
                                                    (Core.Unbox{value = Core.Var (Core.Local boxedLocal), innerRepresentation = representation})
                                                ]
                                            )
                                    else
                                        pure (local, [])

                        (subTreeStatements, subTreeExpr) <- go (fmap (Core.Var . Core.Local . snd) locals <> rest) boundValues subTree
                        pure (index, (possiblyBoxedLocals, fold boxingStatements <> subTreeStatements, subTreeExpr))
                default_ <- for default_ (go rest boundValues)

                scrutineeRepresentation <- convertRepresentation scrutineeRepresentation
                pure ([], Core.ConstructorCase{scrutinee, scrutineeRepresentation, cases, default_})
            PatternMatching.IntCase{cases, default_} -> do
                -- TODO: this currently drops the default
                let (scrutinee, rest) = consume scrutinees
                intCases <-
                    fromList <$> for (Map.toList cases) \(int, subTree) -> do
                        (subTreeStatements, subTreeExpr) <- go rest boundValues subTree
                        pure (int, (subTreeStatements, subTreeExpr))
                default_ <- for default_ (go rest boundValues)

                pure ([], Core.IntCase{scrutinee, intCases, default_})
            PatternMatching.TupleCase representations subTree -> do
                let (scrutinee, rest) = consume scrutinees
                localsWithReps <- for representations \representation -> do
                    local <- newLocal
                    rep <- convertRepresentation representation
                    pure (local, rep)
                let accessStatements = Seq.mapWithIndex (\i (local, rep) -> Core.Let local rep (Core.ProductAccess scrutinee i rep)) localsWithReps

                (subTreeStatements, subTreeExpr) <- go (fmap (Core.Var . Core.Local . fst) localsWithReps <> rest) boundValues subTree
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

arityOfDataConstructor :: (HasCallStack, Compile es) => Vega.Name -> Eff es (Maybe Int)
arityOfDataConstructor = \case
    Vega.Local _localName -> undefined
    Vega.Global globalName -> do
        cachedVegaType <- GraphPersistence.getGlobalType globalName
        case cachedVegaType of
            GraphPersistence.CachedTypeSyntax syntax -> arityOfTypeSyntax syntax
            GraphPersistence.CachedType type_ -> arityOfType type_
            GraphPersistence.RenamingFailed ->
                panic $ "Trying to look up arity of a data constructor where renaming failed: " <> Vega.prettyGlobal Vega.DataConstructorKind globalName
  where
    arityOfType type_ =
        followMetasWithoutPathCompression type_ >>= \case
            Vega.Forall _ rest -> arityOfType rest
            Vega.Function arguments _ _ -> pure (Just (length arguments))
            _ -> pure Nothing
    arityOfTypeSyntax syntax = case syntax of
        Vega.ForallS _ _ rest -> arityOfTypeSyntax rest
        Vega.FunctionS _ arguments _ _ -> pure (Just (length arguments))
        Vega.PureFunctionS _ arguments _ -> pure (Just (length arguments))
        _ -> pure Nothing

booleanConstructorName :: Bool -> Vega.Name
booleanConstructorName True = Vega.Global (Vega.internalName "True")
booleanConstructorName False = Vega.Global (Vega.internalName "False")

{- | Convert a representation represented as a vega type (of kind `Rep`) to a core representation.
This is mostly blind unwrapping and following meta variables, except for the case for unbound meta variables where
we give them representation `Unit` (which is like defaulting them to `()` but friendlier for error messages)
-}
convertRepresentation :: (HasCallStack, Compile es) => Vega.Type -> Eff es Core.Representation
convertRepresentation type_ = withTrace CoreRep ("convertRepresentation: " <> pretty type_) do
    let invalidKind = panic $ "Invalid representation in conversion to Core: " <> pretty type_ <> "\n    This should have been caught in the type checker."
    followMetasWithoutPathCompression type_ >>= \case
        Vega.MetaVar{} -> pure $ Core.ProductRep []
        Vega.SumRep representations -> Core.SumRep <$> traverse convertRepresentation representations
        Vega.ProductRep representations -> Core.ProductRep <$> traverse convertRepresentation representations
        Vega.ArrayRep inner -> Core.ArrayRep <$> convertRepresentation inner
        Vega.ClosureRep inner -> do
            innerRep <- convertRepresentation inner
            pure (Core.ProductRep [Core.FunctionPointerRep, innerRep])
        Vega.PrimitiveRep rep -> pure $ Core.PrimitiveRep rep
        Vega.Skolem skolem -> do
            env <- ask @Env
            case HashMap.lookup skolem.originalName env.monomorphizableRepresentationVariables of
                Nothing ->
                    panic $
                        "Skolem corresponding to a non-parameter representation type variable found while trying to convert representations to core. This should not have happened!\n"
                            <> "Skolem: "
                            <> pretty skolem
                Just index -> pure $ Core.ParameterRep index
        Vega.TypeConstructor{} -> invalidKind
        Vega.TypeApplication{} -> invalidKind
        Vega.TypeVar{} -> panic $ "Uninstantiated type variable found while trying to convert representations to core: " <> pretty type_
        Vega.Forall{} -> invalidKind
        Vega.Exists{} -> invalidKind
        Vega.Function{} -> invalidKind
        Vega.TypeFunction{} -> invalidKind
        Vega.Tuple{} -> invalidKind
        Vega.Record{} -> invalidKind
        Vega.Pure{} -> invalidKind
        Vega.Rep{} -> invalidKind
        Vega.Type{} -> invalidKind
        Vega.Effect{} -> invalidKind
        Vega.Kind{} -> invalidKind
        Vega.IntSum{} -> invalidKind
        Vega.Integer -> invalidKind

extractMonomorphizableRepresentationVariables :: (ReadMeta :> es) => Seq Vega.ForallBinder -> Eff es (Seq Vega.LocalName)
extractMonomorphizableRepresentationVariables binders = wither go binders
  where
    go Vega.MkForallBinder{varName, kind, visibility = _, monomorphization} = case monomorphization of
        Vega.Parametric -> pure Nothing
        Vega.Monomorphized -> do
            Meta.followMetasWithoutPathCompression kind >>= \case
                Vega.Rep -> pure (Just varName)
                _ -> panic "monomorphizable type variables are not implemented yet (we will need to do specialization during core generation here)"

type Substitution = HashMap Core.LocalCoreName Core.Value

coalesceVariables :: Core.Declaration -> Eff es Core.Declaration
coalesceVariables = \case
    Core.DefineFunction{name, parameters, returnRepresentation, statements, result, representationParameters} -> do
        let substitution :: Substitution = mempty
        (substitution, makeStatements) <- coalesceStatements substitution statements
        (substitution, makeResult) <- coalesceExpr substitution result
        pure
            ( Core.DefineFunction
                { name
                , parameters = (fmap (first (getFinalName substitution)) parameters)
                , returnRepresentation
                , statements = (makeStatements substitution)
                , result = (makeResult substitution)
                , representationParameters
                }
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
    Core.Application functionName argValues representation ->
        pure
            ( substitution
            , \substitution -> do
                let name = case functionName of
                        Core.Local localName -> Core.Local (getFinalName substitution localName)
                        Core.Global globalName -> Core.Global globalName
                Core.Application name (fmap (applySubst substitution) argValues) representation
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
    Core.ProductAccess{product, index, resultRepresentation} ->
        pure (substitution, \substitution -> Core.ProductAccess{product = applySubst substitution product, index, resultRepresentation})
    Core.Box value -> pure (substitution, \substitution -> Core.Box (applySubst substitution value))
    Core.Unbox{value, innerRepresentation} ->
        pure (substitution, \substitution -> Core.Unbox{value = applySubst substitution value, innerRepresentation})
    Core.PureOperator operatorExpr ->
        pure
            ( substitution
            , \substitution -> Core.PureOperator (applySubstInPureOperatorExpr substitution operatorExpr)
            )
    Core.ConstructorCase scrutinee scrutineeRepresentation cases default_ -> do
        let coalesceCase substitution (parameters, statements, expr) = do
                (substitution, makeStatements) <- coalesceStatements substitution statements
                (substitution, makeExpr) <- coalesceExpr substitution expr
                pure
                    ( substitution
                    , \substitution ->
                        (fmap (getFinalName substitution) parameters, makeStatements substitution, makeExpr substitution)
                    )
        (substitution, makeCases) <- Util.mapAccumLM coalesceCase substitution cases
        (substitution, makeDefault) <- case default_ of
            Nothing -> pure (substitution, \_ -> Nothing)
            Just body -> do
                (substitution, makeBody) <- coalesceBody substitution body
                pure (substitution, \substitution -> Just (makeBody substitution))

        pure
            ( substitution
            , \substitution ->
                Core.ConstructorCase
                    { scrutinee = applySubst substitution scrutinee
                    , scrutineeRepresentation
                    , cases = fmap ($ substitution) makeCases
                    , default_ = makeDefault substitution
                    }
            )
    Core.IntCase{scrutinee, intCases, default_} -> do
        (substitution, makeCases) <- Util.mapAccumLM coalesceBody substitution intCases

        (substitution, makeDefault) <- case default_ of
            Nothing -> pure (substitution, \_ -> Nothing)
            Just body -> do
                (substitution, makeBody) <- coalesceBody substitution body
                pure (substitution, \substitution -> Just (makeBody substitution))

        pure
            ( substitution
            , \substitution ->
                Core.IntCase
                    { scrutinee = applySubst substitution scrutinee
                    , intCases = fmap ($ substitution) makeCases
                    , default_ = makeDefault substitution
                    }
            )

coalesceBody :: Substitution -> (Seq Core.Statement, Core.Expr) -> Eff es (Substitution, Substitution -> (Seq Core.Statement, Core.Expr))
coalesceBody substitution (statements, expr) = do
    (substitution, makeStatements) <- coalesceStatements substitution statements
    (substitution, makeExpr) <- coalesceExpr substitution expr
    pure (substitution, \substitution -> (makeStatements substitution, makeExpr substitution))

applySubstInPureOperatorExpr :: Substitution -> Core.PureOperatorExpr -> Core.PureOperatorExpr
applySubstInPureOperatorExpr substitution = \case
    Core.PureOperatorValue value -> Core.PureOperatorValue (applySubst substitution value)
    Core.Add left right ->
        Core.Add
            (applySubstInPureOperatorExpr substitution left)
            (applySubstInPureOperatorExpr substitution right)
    Core.Subtract left right ->
        Core.Subtract
            (applySubstInPureOperatorExpr substitution left)
            (applySubstInPureOperatorExpr substitution right)
    Core.Multiply left right ->
        Core.Multiply
            (applySubstInPureOperatorExpr substitution left)
            (applySubstInPureOperatorExpr substitution right)
    Core.Divide left right ->
        Core.Divide
            (applySubstInPureOperatorExpr substitution left)
            (applySubstInPureOperatorExpr substitution right)
    Core.Less left right ->
        Core.Less
            (applySubstInPureOperatorExpr substitution left)
            (applySubstInPureOperatorExpr substitution right)
    Core.LessEqual left right ->
        Core.LessEqual
            (applySubstInPureOperatorExpr substitution left)
            (applySubstInPureOperatorExpr substitution right)
    Core.Equal left right ->
        Core.Equal
            (applySubstInPureOperatorExpr substitution left)
            (applySubstInPureOperatorExpr substitution right)
    Core.NotEqual left right ->
        Core.NotEqual
            (applySubstInPureOperatorExpr substitution left)
            (applySubstInPureOperatorExpr substitution right)

applySubst :: Substitution -> Core.Value -> Core.Value
applySubst substitution = \case
    Core.Var (Core.Global globalName) -> Core.Var (Core.Global globalName)
    Core.Var (Core.Local localName) -> getFinalValue substitution localName
    Core.Literal literal -> Core.Literal literal
    Core.DataConstructorApplication{constructor, arguments, resultRepresentation} ->
        Core.DataConstructorApplication
            { arguments = (fmap (applySubst substitution) arguments)
            , constructor
            , resultRepresentation
            }

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
