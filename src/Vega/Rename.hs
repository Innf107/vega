module Vega.Rename (rename) where

-- TODO: check imports (?)

import Relude hiding (Reader, State, ask, evalState, get, put, runReader)
import Relude.Extra

import Vega.Syntax

import Data.HashSet qualified as HashSet
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Effectful (Eff, (:>))
import Effectful.Reader.Static (Reader, ask, runReader)
import Effectful.State.Static.Local
import GHC.List (List)
import Vega.Builtins (builtinGlobals, defaultImportScope)
import Vega.Effect.GraphPersistence (DataConstructorIndex (..), GraphPersistence, findMatchingNames, getDefiningDeclaration, getModuleImportScope, setDataConstructorIndex)
import Vega.Effect.Output.Static.Local qualified as Output
import Vega.Effect.Output.Static.Local.HashSet qualified as Output.HashSet
import Vega.Error (RenameError (..), RenameErrorSet (..))
import Vega.Loc (Loc)
import Vega.Util (mapAccumLM)
import Vega.Util qualified as Util

type Rename es =
    ( GraphPersistence :> es
    , Reader DeclarationName :> es
    , Output.HashSet.Output DeclarationName :> es
    , Output.Output RenameError :> es
    , State LocalNameCounts :> es
    )
type LocalNameCounts = HashMap Text Int

registerDependency :: (Rename es) => DeclarationName -> Eff es ()
registerDependency dependency = do
    ownDeclaration <- ask
    if ownDeclaration == dependency
        then
            pure ()
        else
            Output.HashSet.output dependency

data Env = MkEnv
    { localVariables :: HashMap Text LocalName
    , localTypeVariables :: HashMap Text LocalName
    , localTypeConstructors :: HashMap Text LocalName
    , localDataConstructors :: HashMap Text LocalName
    }

emptyEnv :: Env
emptyEnv =
    MkEnv
        { localVariables = mempty
        , localTypeVariables = mempty
        , localTypeConstructors = mempty
        , localDataConstructors = mempty
        }

bindLocalVar :: (Rename es) => Text -> Eff es (LocalName, Env -> Env)
bindLocalVar text = do
    parent <- ask @DeclarationName
    count <- indexForNewLocal text
    let localName = MkLocalName{parent, name = text, count}
    pure (localName, \env -> env{localVariables = insert text localName env.localVariables})

bindTypeVariable :: (Rename es) => Text -> Eff es (LocalName, Env -> Env)
bindTypeVariable text = do
    parent <- ask @DeclarationName
    count <- indexForNewLocal text
    let localName = MkLocalName{parent, name = text, count}
    pure (localName, \env -> env{localTypeVariables = insert text localName env.localTypeVariables})

indexForNewLocal :: (Rename es) => Text -> Eff es Int
indexForNewLocal text = do
    countsSoFar <- get @LocalNameCounts
    let index = case lookup text countsSoFar of
            Nothing -> 0
            Just count -> count
    put (insert text (index + 1) countsSoFar)
    pure index

data GlobalVariableOccurance
    = Found GlobalName
    | NotFound
    | Ambiguous (HashSet GlobalName)
    | Inaccessible (HashSet GlobalName)

findGlobalUnregistered :: (Rename es) => NameKind -> Text -> Eff es GlobalVariableOccurance
findGlobalUnregistered nameKind name = do
    parent <- ask @DeclarationName

    -- We can assume that builtins are never going to cause name conflicts
    let builtinCandidates = case lookup (name, nameKind) builtinGlobals of
            Nothing -> []
            Just global -> [global]

    importScope <- (defaultImportScope <>) <$> getModuleImportScope parent.moduleName
    userDefinedCandidates <- findMatchingNames name nameKind

    let candidates = builtinCandidates <> toList userDefinedCandidates

    case filter (\name -> name.moduleName == parent.moduleName || isInScope name importScope) candidates of
        [] -> case candidates of
            [] -> pure NotFound
            _ -> pure $ Inaccessible (HashSet.fromList candidates)
        [var] -> pure $ Found var
        candidatesInScope -> pure $ Ambiguous (fromList candidatesInScope)

findGlobal :: (Rename es) => NameKind -> Text -> Eff es GlobalVariableOccurance
findGlobal nameKind name = do
    findGlobalUnregistered nameKind name >>= \case
        Found globalName -> do
            when (globalName.moduleName /= internalModuleName) do
                dependencyDeclarationName <-
                    getDefiningDeclaration globalName >>= \case
                        Nothing -> error $ "declaration of name not found: " <> show globalName
                        Just name -> pure name
                registerDependency dependencyDeclarationName

            pure (Found globalName)
        NotFound -> pure NotFound
        Inaccessible candidates -> pure $ Inaccessible candidates
        Ambiguous candidatesInScope -> pure $ Ambiguous candidatesInScope

findGlobalOrDummy :: (Rename es) => Loc -> NameKind -> Text -> Eff es Name
findGlobalOrDummy loc nameKind name =
    findGlobal nameKind name >>= \case
        Found globalName -> pure (Global globalName)
        NotFound -> do
            Output.output (NameNotFound{loc, name, nameKind})

            parent <- ask @DeclarationName
            pure (Local (dummyLocalName parent name))
        Ambiguous candidates -> do
            Output.output (AmbiguousGlobal{loc, name = name, nameKind, candidates})

            parent <- ask @DeclarationName
            pure (Local (dummyLocalName parent name))
        Inaccessible candidates -> do
            Output.output (InaccessibleGlobal{loc, name, nameKind, candidates})

            parent <- ask @DeclarationName
            pure (Local (dummyLocalName parent name))

isInScope :: GlobalName -> ImportScope -> Bool
isInScope name scope =
    case lookup name.moduleName scope.imports of
        Nothing -> False
        Just importedItems ->
            -- TODO: qualified
            HashSet.member name.name importedItems.unqualifiedItems

rename :: (GraphPersistence :> es) => Declaration Parsed -> Eff es (Declaration Renamed, RenameErrorSet, HashSet DeclarationName)
rename (MkDeclaration loc name syntax) = runReader name do
    ((syntax, errors), dependencies) <-
        Output.HashSet.runOutputHashSet $
            Output.runOutputSeq @RenameError $
                evalState @LocalNameCounts mempty $
                    renameDeclarationSyntax syntax
    pure (MkDeclaration loc name syntax, (MkRenameErrorSet errors), dependencies)

findVarName :: (Rename es) => Env -> Loc -> Text -> Eff es Name
findVarName env loc text = case lookup text env.localVariables of
    Just localName -> pure (Local localName)
    Nothing -> findGlobalOrDummy loc VarKind text

findTypeConstructorName :: (Rename es) => Env -> Loc -> Text -> Eff es Name
findTypeConstructorName env loc text = case lookup text env.localTypeConstructors of
    Just localName -> pure (Local localName)
    Nothing -> findGlobalOrDummy loc TypeConstructorKind text

findDataConstructorName :: (Rename es) => Env -> Loc -> Text -> Eff es Name
findDataConstructorName env loc text = case lookup text env.localDataConstructors of
    Just localName -> pure (Local localName)
    Nothing -> findGlobalOrDummy loc DataConstructorKind text

{- | This is returned if we cannot find a local name during renaming.

This condition is an error, but we don't want to abort renaming just yet since we might find more
errors in the same declaration.
Instead, we return a new dummy name that is technically wrong and could cause issues if it got through to type checking,
but since we already threw an error when using this function, the type checker is not going to run on
the current declaration anyway and will not cause any issues.
-}
dummyLocalName :: DeclarationName -> Text -> LocalName
dummyLocalName parent name = MkLocalName{parent, name, count = -1}

findTypeVariable :: (Rename es) => Env -> Loc -> Text -> Eff es LocalName
findTypeVariable env loc name = case lookup name env.localTypeVariables of
    Just localName -> pure localName
    Nothing -> do
        Output.output (TypeVariableNotFound{loc, name})

        parent <- ask
        pure (dummyLocalName parent name)

renameDeclarationSyntax :: (Rename es) => DeclarationSyntax Parsed -> Eff es (DeclarationSyntax Renamed)
renameDeclarationSyntax = \case
    DefineFunction{ext, name, typeSignature, declaredTypeParameters, parameters, body} -> do
        let env = emptyEnv
        typeSignature <- renameTypeSyntax env typeSignature

        (declaredTypeParameters, envTransformers) <-
            Seq.unzip <$> for declaredTypeParameters \(loc, name) -> do
                (name, envTrans) <- bindTypeVariable name
                pure ((loc, name), envTrans)
        env <- pure (Util.compose envTransformers env)

        (parameters, transformers) <-
            Seq.unzip <$> for parameters \(pattern_, ()) -> do
                (pattern_, transformer) <- renamePattern env pattern_
                pure ((pattern_, ()), transformer)
        body <- renameExpr (Util.compose transformers env) body
        pure (DefineFunction{ext, name, typeSignature, declaredTypeParameters, parameters, body})
    DefineVariantType{name, typeParameters, constructors} -> do
        let env = emptyEnv
        (env, typeParameters) <- renameTypeVarBinders env typeParameters
        constructors <- for (Util.indexed constructors) \(index, (loc, dataConstructorName, parameters)) -> do
            parameters <- traverse (renameTypeSyntax env) parameters
            let constructorIndex =
                    if length constructors == 1
                        then OnlyConstructor
                        else MultiConstructor index
            setDataConstructorIndex (Global dataConstructorName) constructorIndex

            pure (loc, dataConstructorName, parameters)
        pure (DefineVariantType{name, typeParameters, constructors})
    DefineExternalFunction{name, type_} -> do
        type_ <- renameTypeSyntax emptyEnv type_
        pure (DefineExternalFunction{name, type_})

renameTypeSyntax :: (Rename es) => Env -> TypeSyntax Parsed -> Eff es (TypeSyntax Renamed)
renameTypeSyntax env = \case
    TypeConstructorS loc name -> do
        name <- findTypeConstructorName env loc name
        pure (TypeConstructorS loc name)
    TypeApplicationS loc funType arguments -> do
        funType <- renameTypeSyntax env funType
        arguments <- traverse (renameTypeSyntax env) arguments
        pure (TypeApplicationS loc funType arguments)
    TypeVarS loc name -> do
        name <- findTypeVariable env loc name
        pure (TypeVarS loc name)
    ForallS loc typeVarBinders body -> do
        (env, typeVarBinders) <- renameTypeVarBinders env typeVarBinders
        body <- renameTypeSyntax env body
        pure (ForallS loc typeVarBinders body)
    ExistsS loc binders body -> do
        let renameExistentialBinder env (name, kind) = do
                (name, envTrans) <- bindTypeVariable name
                kind <- renameKindSyntax env kind
                pure (envTrans env, (name, kind))
        (env, binders) <- mapAccumLM renameExistentialBinder env binders
        body <- renameTypeSyntax env body
        pure (ExistsS loc binders body)
    PureFunctionS loc parameters resultType -> do
        parameters <- traverse (renameTypeSyntax env) parameters
        resultType <- renameTypeSyntax env resultType
        pure (PureFunctionS loc parameters resultType)
    FunctionS loc parameters effect resultType -> do
        parameters <- traverse (renameTypeSyntax env) parameters
        effect <- renameTypeSyntax env effect
        resultType <- renameTypeSyntax env resultType
        pure (FunctionS loc parameters effect resultType)
    TypeFunctionS loc parameters result -> do
        parameters <- traverse (renameTypeSyntax env) parameters
        result <- renameTypeSyntax env result
        pure (TypeFunctionS loc parameters result)
    TupleS loc elements -> do
        elements <- traverse (renameTypeSyntax env) elements
        pure (TupleS loc elements)
    RecordS loc fields -> do
        fields <- for fields \(name, type_) -> do
            type_ <- renameTypeSyntax env type_
            pure (name, type_)
        pure (RecordS loc fields)
    RepS loc -> pure (RepS loc)
    TypeS loc repKind -> do
        repKind <- renameKindSyntax env repKind
        pure (TypeS loc repKind)
    EffectS loc -> pure (EffectS loc)
    SumRepS loc elements -> do
        elements <- traverse (renameTypeSyntax env) elements
        pure (SumRepS loc elements)
    ProductRepS loc elements -> do
        elements <- traverse (renameTypeSyntax env) elements
        pure (ProductRepS loc elements)
    ArrayRepS loc inner -> do
        inner <- renameTypeSyntax env inner
        pure (ArrayRepS loc inner)
    PrimitiveRepS loc rep -> pure (PrimitiveRepS loc rep)
    KindS loc -> pure (KindS loc)

renameKindSyntax :: (Rename es) => Env -> KindSyntax Parsed -> Eff es (KindSyntax Renamed)
renameKindSyntax = renameTypeSyntax

renameTypeVarBinders :: (Traversable t, Rename es) => Env -> t (ForallBinderS Parsed) -> Eff es (Env, t (ForallBinderS Renamed))
renameTypeVarBinders env binders = mapAccumLM renameForallBinder env binders

renameForallBinder :: (Rename es) => Env -> ForallBinderS Parsed -> Eff es (Env, ForallBinderS Renamed)
renameForallBinder env = \case
    UnspecifiedBinderS{loc, monomorphization, varName} -> do
        (varName, envTrans) <- bindTypeVariable varName
        pure (envTrans env, UnspecifiedBinderS{loc, monomorphization, varName})
    TypeVarBinderS{loc, visibility, monomorphization, varName, kind} -> do
        kind <- renameKindSyntax env kind
        (varName, envTrans) <- bindTypeVariable varName
        pure (envTrans env, TypeVarBinderS{loc, visibility, monomorphization, varName, kind})

renamePattern :: (Rename es) => Env -> Pattern Parsed -> Eff es (Pattern Renamed, Env -> Env)
renamePattern env = \case
    WildcardPattern loc -> pure (WildcardPattern loc, id)
    VarPattern{loc, ext = (), name, isShadowed} -> do
        (localName, envTrans) <- bindLocalVar name
        pure (VarPattern{loc, ext = (), name = localName, isShadowed}, envTrans)
    AsPattern loc () innerPattern name -> do
        (innerPattern, innerTrans) <- renamePattern env innerPattern
        (localName, envTrans) <- bindLocalVar name
        pure (AsPattern loc () innerPattern localName, envTrans . innerTrans)
    ConstructorPattern{loc, constructor, constructorExt, subPatterns} -> do
        constructor <- findDataConstructorName env loc constructor
        (subPatterns, envTransformers) <- Seq.unzip <$> for subPatterns (renamePattern env)
        pure (ConstructorPattern{loc, constructor, constructorExt, subPatterns}, Util.compose envTransformers)
    TuplePattern loc subPatterns -> do
        (subPatterns, transformers) <- Seq.unzip <$> traverse (renamePattern env) subPatterns
        pure (TuplePattern loc subPatterns, Util.compose transformers)
    TypePattern loc innerPattern type_ -> do
        (innerPattern, innerTrans) <- renamePattern env innerPattern
        type_ <- renameTypeSyntax env type_
        pure (TypePattern loc innerPattern type_, innerTrans)
    OrPattern{} -> undefined

renameExpr :: (Rename es) => Env -> Expr Parsed -> Eff es (Expr Renamed)
renameExpr env = \case
    Var loc name -> do
        name <- findVarName env loc name
        pure (Var loc name)
    DataConstructor loc () name -> do
        name <- findDataConstructorName env loc name
        pure (DataConstructor loc () name)
    Application{loc, representation, functionExpr, arguments} -> do
        functionExpr <- renameExpr env functionExpr
        arguments <- traverse (renameExpr env) arguments
        pure (Application{loc, representation, functionExpr, arguments})
    PartialApplication{loc, functionExpr, partialArguments} -> do
        functionExpr <- renameExpr env functionExpr
        partialArguments <- traverse (traverse (renameExpr env)) partialArguments
        pure (PartialApplication{loc, functionExpr, partialArguments})
    VisibleTypeApplication{loc, varName, typeArguments} -> do
        varName <- findVarName env loc varName
        typeArguments <- traverse (renameTypeSyntax env) typeArguments
        pure (VisibleTypeApplication{loc, varName, typeArguments})
    Lambda loc boundTypeParameters parameters body -> do
        (boundTypeParameters, typeParamTransformers) <-
            Seq.unzip <$> for boundTypeParameters \(loc, name) -> do
                (name, envTrans) <- bindTypeVariable name
                pure ((loc, name), envTrans)
        -- It's important that we apply the type parameter transformers *before* renaming the
        -- regular parameters since they might use the type variables bound here
        env <- pure (Util.compose typeParamTransformers env)

        (parameters, transformers) <- Seq.unzip <$> traverse (renamePattern env) parameters
        body <- renameExpr (Util.compose transformers env) body
        pure (Lambda loc boundTypeParameters parameters body)
    StringLiteral loc literal -> pure (StringLiteral loc literal)
    IntLiteral loc literal -> pure (IntLiteral loc literal)
    DoubleLiteral loc literal -> pure (DoubleLiteral loc literal)
    TupleLiteral loc elements -> do
        elements <- traverse (renameExpr env) elements
        pure (TupleLiteral loc elements)
    RecordLiteral loc elements -> do
        elements <- for elements \(name, expr) -> do
            expr <- renameExpr env expr
            pure (name, expr)
        pure (RecordLiteral loc elements)
    BinaryOperator loc arg1 operator arg2 -> do
        arg1 <- renameExpr env arg1
        arg2 <- renameExpr env arg2
        pure (BinaryOperator loc arg1 operator arg2)
    If{loc, condition, thenBranch, elseBranch} -> do
        condition <- renameExpr env condition
        thenBranch <- renameExpr env thenBranch
        elseBranch <- renameExpr env elseBranch
        pure (If{loc, condition, thenBranch, elseBranch})
    SequenceBlock{loc, statements} -> do
        (_, statements) <-
            Util.mapAccumLM
                ( \env statement -> do
                    (statement, envTrans) <- renameStatement env statement
                    pure (envTrans env, statement)
                )
                env
                statements
        pure (SequenceBlock{loc, statements})
    Match{loc, scrutinee, cases} -> do
        scrutinee <- renameExpr env scrutinee
        cases <- traverse (renameMatchCase env) cases
        pure (Match{loc, scrutinee, cases})

renameStatement :: (Rename es) => Env -> Statement Parsed -> Eff es (Statement Renamed, Env -> Env)
renameStatement env = \case
    Run loc expr -> do
        expr <- renameExpr env expr
        pure (Run loc expr, id)
    Let loc pattern_ body -> do
        (pattern_, envTrans) <- renamePattern env pattern_
        -- Regular lets are non-recursive so we don't use the env transformer here just yet
        body <- renameExpr env body
        pure (Let loc pattern_ body, envTrans)
    LetFunction{ext = (), loc, name, typeSignature, parameters, body} -> do
        (name, envTrans) <- bindLocalVar name
        typeSignature <- traverse (renameTypeSyntax env) typeSignature
        (parameters, innerTransformers) <-
            Seq.unzip <$> for parameters \(pattern_, ()) -> do
                (pattern_, envTransformer) <- renamePattern env pattern_
                pure ((pattern_, ()), envTransformer)
        -- Function let bindings are recursive so we apply the functions own transformer first
        -- before binding any parameters
        body <- renameExpr (Util.compose innerTransformers (envTrans env)) body
        pure (LetFunction{ext = (), loc, name, typeSignature, parameters, body}, envTrans)
    Use{} -> undefined

renameMatchCase :: (Rename es) => Env -> MatchCase Parsed -> Eff es (MatchCase Renamed)
renameMatchCase env (MkMatchCase{loc, pattern_, body}) = do
    (pattern_, envTrans) <- renamePattern env pattern_
    body <- renameExpr (envTrans env) body
    pure (MkMatchCase{loc, pattern_, body})
