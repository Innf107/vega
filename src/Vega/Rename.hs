module Vega.Rename (rename) where

import Relude hiding (Reader, ask, runReader)
import Relude.Extra

import Vega.Syntax

import Data.HashSet qualified as HashSet
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Effectful (Eff, (:>))
import Effectful.Reader.Static (Reader, ask, runReader)
import Vega.Effect.GraphPersistence (GraphPersistence, findMatchingNames, getModuleImportScope)
import Vega.Util qualified as Util

type Rename es = (GraphPersistence :> es, Reader GlobalName :> es)

data Env = MkEnv
    { localVariables :: Map Text LocalName
    , localTypeVariables :: Map Text LocalName
    }

emptyEnv :: Env
emptyEnv =
    MkEnv
        { localVariables = mempty
        , localTypeVariables = mempty
        }

bindLocalVar :: (Rename es) => Text -> Eff es (LocalName, Env -> Env)
bindLocalVar text = do
    parent <- ask @GlobalName
    let count = 0
    let localName = MkLocalName{parent, name = text, count}
    pure (localName, \env -> env{localVariables = insert text localName env.localVariables})

bindTypeVariable :: (Rename es) => Text -> Eff es (LocalName, Env -> Env)
bindTypeVariable text = do
    parent <- ask @GlobalName
    let count = 0 -- TODO
    let localName = MkLocalName{parent, name = text, count}
    pure (localName, \env -> env{localTypeVariables = insert text localName env.localTypeVariables})

data GlobalVariableOccurance
    = Found GlobalName
    | NotFound
    | Ambiguous (Seq GlobalName)
    | Inaccessible (Seq GlobalName)

findGlobalVariable :: (Rename es) => Text -> Eff es GlobalVariableOccurance
findGlobalVariable var = do
    parent <- ask @GlobalName

    importScope <- getModuleImportScope parent.moduleName
    candidates <- findMatchingNames var

    case Seq.filter (\name -> isInScope name importScope) candidates of
        [] -> case candidates of
            [] -> pure NotFound
            _ -> pure $ Inaccessible candidates
        [var] -> pure $ Found var
        candidatesInScope -> pure $ Ambiguous candidatesInScope

isInScope :: GlobalName -> ImportScope -> Bool
isInScope name scope = do
    case lookup name.moduleName scope.imports of
        Nothing -> False
        Just importedItems ->
            -- TODO: qualified
            HashSet.member name.name importedItems.unqualifiedItems

rename :: (GraphPersistence :> es) => Declaration Parsed -> Eff es (Declaration Renamed, Seq GlobalName)
rename (MkDeclaration loc name syntax) = runReader name do
    -- TODO: graph stuff
    syntax <- renameDeclarationSyntax name syntax
    pure (MkDeclaration loc name syntax, undefined)

findVarName :: (Rename es) => Env -> Text -> Eff es Name
findVarName env text = case lookup text env.localVariables of
    Just localName -> pure (Local localName)
    Nothing ->
        findGlobalVariable text >>= \case
            Found globalName -> pure (Global globalName)
            NotFound ->
                -- TODO: error message. Ideally we don't want this to abort everything but that means we need to return some kind of
                -- partial name standin and (somehow) propagate that to the next stage?
                -- Since this runs per declaration, maybe failing wouldn't be *terrible* but it would still be nice to have x + y show two errors
                undefined
            Ambiguous names -> undefined
            Inaccessible names -> undefined

findTypeVariable :: Env -> Text -> Eff es LocalName
findTypeVariable env text = case lookup text env.localTypeVariables of
    Just localName -> pure localName
    Nothing -> undefined

renameDeclarationSyntax :: (Rename es) => GlobalName -> DeclarationSyntax Parsed -> Eff es (DeclarationSyntax Renamed)
renameDeclarationSyntax name = \case
    DefineFunction{typeSignature, parameters, body} -> do
        let env = emptyEnv
        typeSignature <- renameTypeSyntax env typeSignature
        (parameters, transformers) <- Seq.unzip <$> traverse (renamePattern env) parameters
        body <- renameExpr (Util.compose transformers env) body
        pure (DefineFunction{typeSignature, parameters, body})
    DefineVariantType{typeParameters, constructors} -> do
        undefined

renameTypeSyntax :: (Rename es) => Env -> TypeSyntax Parsed -> Eff es (TypeSyntax Renamed)
renameTypeSyntax env = \case
    TypeConstructorS{} -> undefined
    TypeApplicationS loc funType arguments -> do
        funType <- renameTypeSyntax env funType
        arguments <- traverse (renameTypeSyntax env) arguments
        pure (TypeApplicationS loc funType arguments)
    TypeVarS loc name -> do
        name <- findTypeVariable env name
        pure (TypeVarS loc name)
    ForallS loc typeVarBinders body -> do
        (typeVarBinders, env) <- renameTypeVarBinders env typeVarBinders
        body <- renameTypeSyntax env body
        pure (ForallS loc typeVarBinders body)
    PureFunctionS loc parameters resultType -> do
        parameters <- traverse (renameTypeSyntax env) parameters
        resultType <- renameTypeSyntax env resultType
        pure (PureFunctionS loc parameters resultType)
    FunctionS loc parameters effect resultType -> do
        parameters <- traverse (renameTypeSyntax env) parameters
        effect <- renameTypeSyntax env effect
        resultType <- renameTypeSyntax env resultType
        pure (FunctionS loc parameters effect resultType)
    TupleS loc elements -> do
        elements <- traverse (renameTypeSyntax env) elements
        pure (TupleS loc elements)

renameTypeVarBinders :: (Rename es) => Env -> Seq (TypeVarBinderS Parsed) -> Eff es (Seq (TypeVarBinderS Renamed), Env)
renameTypeVarBinders env = \case
    Empty -> pure (Empty, env)
    (MkTypeVarBinderS{loc, varName, kind} :<| rest) -> do
        (varName, envTrans) <- bindTypeVariable varName
        -- The kind is not allowed to depend on the variable being defined so we don't use the env transformer yet
        kind <- traverse (renameKindSyntax env) kind

        (rest, finalEnv) <- renameTypeVarBinders (envTrans env) rest

        pure (MkTypeVarBinderS{loc, varName, kind} :<| rest, finalEnv)

renameKindSyntax :: (Rename es) => Env -> KindSyntax Parsed -> Eff es (KindSyntax Renamed)
renameKindSyntax env = \case
    TypeS loc -> pure (TypeS loc)
    EffectS loc -> pure (EffectS loc)
    ArrowKindS loc parameters result -> do
        parameters <- traverse (renameKindSyntax env) parameters
        result <- renameKindSyntax env result
        pure (ArrowKindS loc parameters result)

renamePattern :: (Rename es) => Env -> Pattern Parsed -> Eff es (Pattern Renamed, Env -> Env)
renamePattern env = \case
    WildcardPattern loc -> pure (WildcardPattern loc, id)
    VarPattern loc name -> do
        (localName, envTrans) <- bindLocalVar name
        pure (VarPattern loc localName, envTrans)
    AsPattern loc innerPattern name -> do
        (innerPattern, innerTrans) <- renamePattern env innerPattern
        (localName, envTrans) <- bindLocalVar name
        pure (AsPattern loc innerPattern localName, envTrans . innerTrans)
    ConstructorPattern{} -> undefined
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
        name <- findVarName env name
        pure (Var loc name)
    DataConstructor{} -> undefined
    Application{loc, functionExpr, arguments} -> do
        functionExpr <- renameExpr env functionExpr
        arguments <- traverse (renameExpr env) arguments
        pure (Application{loc, functionExpr, arguments})
    PartialApplication{loc, functionExpr, partialArguments} -> do
        functionExpr <- renameExpr env functionExpr
        partialArguments <- traverse (traverse (renameExpr env)) partialArguments
        pure (PartialApplication{loc, functionExpr, partialArguments})
    VisibleTypeApplication{loc, expr, typeArguments} -> do
        expr <- renameExpr env expr
        typeArguments <- traverse (renameTypeSyntax env) typeArguments
        pure (VisibleTypeApplication{loc, expr, typeArguments})
    Lambda loc parameters body -> do
        (parameters, transformers) <- Seq.unzip <$> traverse (renamePattern env) parameters
        body <- renameExpr (Util.compose transformers env) body
        pure (Lambda loc parameters body)
    StringLiteral loc literal -> pure (StringLiteral loc literal)
    IntLiteral loc literal -> pure (IntLiteral loc literal)
    DoubleLiteral loc literal -> pure (DoubleLiteral loc literal)
    TupleLiteral loc elements -> do
        elements <- traverse (renameExpr env) elements
        pure (TupleLiteral loc elements)
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
    LetFunction{loc, name, typeSignature, parameters, body} -> do
        (name, envTrans) <- bindLocalVar name
        typeSignature <- traverse (renameTypeSyntax env) typeSignature
        (parameters, innerTransformers) <- Seq.unzip <$> traverse (renamePattern env) parameters
        -- Function let bindings are recursive so we apply the functions own transformer first
        -- before binding any parameters
        body <- renameExpr (Util.compose innerTransformers (envTrans env)) body
        pure (LetFunction{loc, name, typeSignature, parameters, body}, envTrans)
    Use{} -> undefined

renameMatchCase :: (Rename es) => Env -> MatchCase Parsed -> Eff es (MatchCase Renamed)
renameMatchCase env (MkMatchCase{loc, pattern_, body}) = do
    (pattern_, envTrans) <- renamePattern env pattern_
    body <- renameExpr (envTrans env) body
    pure (MkMatchCase{loc, pattern_, body})
