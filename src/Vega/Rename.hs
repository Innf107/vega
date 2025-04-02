module Vega.Rename (rename) where

import Relude
import Relude.Extra

import Vega.Syntax

import Data.Kind (Constraint)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Effectful (Eff)
import Vega.Util qualified as Util

type Rename es = (() :: Constraint)

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

bindLocalVar :: Text -> Eff es (LocalName, Env -> Env)
bindLocalVar text = do
    localName <- undefined text
    pure (localName, \env -> env{localVariables = insert text localName env.localVariables})

bindTypeVariable :: Text -> Eff es (LocalName, Env -> Env)
bindTypeVariable text = do
    localName <- undefined text
    pure (localName, \env -> env{localTypeVariables = insert text localName env.localTypeVariables})

findGlobalVariable :: (Rename es) => Text -> Eff es (Maybe GlobalName)
findGlobalVariable = undefined

globalizeName :: (Rename es) => Text -> Eff es GlobalName
globalizeName = undefined

rename :: (Rename es) => Declaration Parsed -> Eff es (Declaration Renamed)
rename = undefined

findVarName :: Env -> Text -> Eff es Name
findVarName env text = case lookup text env.localVariables of
    Just localName -> pure (Local localName)
    Nothing ->
        findGlobalVariable text >>= \case
            Just globalName -> pure (Global globalName)
            Nothing ->
                -- TODO: error message. Ideally we don't want this to abort everything but that means we need to return some kind of
                -- partial name standin and (somehow) propagate that to the next stage?
                -- Since this runs per declaration, maybe failing wouldn't be *terrible* but it would still be nice to have x + y show two errors
                undefined

findTypeVariable :: Env -> Text -> Eff es LocalName
findTypeVariable env text = case lookup text env.localTypeVariables of
    Just localName -> pure localName
    Nothing -> undefined

renameDeclarationSyntax :: (Rename es) => DeclarationSyntax Parsed -> Eff es (DeclarationSyntax Renamed)
renameDeclarationSyntax = \case
    DefineFunction{typeSignature, name, parameters, body} -> do
        let env = emptyEnv
        typeSignature <- renameTypeSyntax env typeSignature
        name <- globalizeName name
        (parameters, transformers) <- Seq.unzip <$> traverse (renamePattern env) parameters
        body <- renameExpr (Util.compose transformers env) body
        pure (DefineFunction{typeSignature, name, parameters, body})
    DefineVariantType{name, typeParameters, constructors} -> do
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
    VarPattern name -> do
        (localName, envTrans) <- bindLocalVar name
        pure (VarPattern localName, envTrans)
    AsPattern innerPattern name -> do
        (innerPattern, innerTrans) <- renamePattern env innerPattern
        (localName, envTrans) <- bindLocalVar name
        pure (AsPattern innerPattern localName, envTrans . innerTrans)
    ConstructorPattern{} -> undefined
    TypePattern innerPattern type_ -> do
        (innerPattern, innerTrans) <- renamePattern env innerPattern
        type_ <- renameTypeSyntax env type_
        pure (TypePattern innerPattern type_, innerTrans)
    OrPattern{} -> undefined

renameExpr :: (Rename es) => Env -> Expr Parsed -> Eff es (Expr Renamed)
renameExpr env = \case
    Var name -> do
        name <- findVarName env name
        pure (Var name)
    DataConstructor{} -> undefined
    Application{functionExpr, arguments} -> do
        functionExpr <- renameExpr env functionExpr
        arguments <- traverse (renameExpr env) arguments
        pure (Application functionExpr arguments)
    VisibleTypeApplication{expr, typeArguments} -> do
        expr <- renameExpr env expr
        typeArguments <- traverse (renameTypeSyntax env) typeArguments
        pure (VisibleTypeApplication{expr, typeArguments})
    Lambda parameters body -> do
        (parameters, transformers) <- Seq.unzip <$> traverse (renamePattern env) parameters
        body <- renameExpr (Util.compose transformers env) body
        pure (Lambda parameters body)
    StringLiteral literal -> pure (StringLiteral literal)
    IntLiteral literal -> pure (IntLiteral literal)
    DoubleLiteral literal -> pure (DoubleLiteral literal)
    BinaryOperator arg1 operator arg2 -> do
        arg1 <- renameExpr env arg1
        arg2 <- renameExpr env arg2
        pure (BinaryOperator arg1 operator arg2)
    If{condition, thenBranch, elseBranch} -> do
        condition <- renameExpr env condition
        thenBranch <- renameExpr env thenBranch
        elseBranch <- renameExpr env elseBranch
        pure (If{condition, thenBranch, elseBranch})
    SequenceBlock{statements} -> do
        (_, statements) <-
            Util.mapAccumLM
                ( \env statement -> do
                    (statement, envTrans) <- renameStatement env statement
                    pure (envTrans env, statement)
                )
                env
                statements
        pure (SequenceBlock{statements})
    Match{scrutinee, cases} -> do
        scrutinee <- renameExpr env scrutinee
        cases <- traverse (renameMatchCase env) cases
        pure (Match{scrutinee, cases})

renameStatement :: (Rename es) => Env -> Statement Parsed -> Eff es (Statement Renamed, Env -> Env)
renameStatement env = \case
    Run expr -> do
        expr <- renameExpr env expr
        pure (Run expr, id)
    Let pattern_ body -> do
        (pattern_, envTrans) <- renamePattern env pattern_
        -- Regular lets are non-recursive so we don't use the env transformer here just yet
        body <- renameExpr env body
        pure (Let pattern_ body, envTrans)
    LetFunction{name, typeSignature, parameters, body} -> do
        (name, envTrans) <- bindLocalVar name
        typeSignature <- traverse (renameTypeSyntax env) typeSignature
        (parameters, innerTransformers) <- Seq.unzip <$> traverse (renamePattern env) parameters
        -- Function let bindings are recursive so we apply the functions own transformer first
        -- before binding any parameters
        body <- renameExpr (Util.compose innerTransformers (envTrans env)) body
        pure (LetFunction{name, typeSignature, parameters, body}, envTrans)

renameMatchCase :: (Rename es) => Env -> MatchCase Parsed -> Eff es (MatchCase Renamed)
renameMatchCase env (MkMatchCase{pattern_, body}) = do
    (pattern_, envTrans) <- renamePattern env pattern_
    body <- renameExpr (envTrans env) body
    pure (MkMatchCase{pattern_, body})
