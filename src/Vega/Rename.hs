module Vega.Rename (rename, RenameError (..)) where

import Vega.Prelude
import Vega.Syntax

import Vega.Loc (HasLoc)
import Vega.Name qualified as Name

import Vega.Primop

import Vega.Pretty

data RenameError
    = UnboundVariable Loc Text
    deriving (Generic)
instance HasLoc RenameError

instance Pretty RenameError where
    pretty (UnboundVariable _ varname) =
        "Unbound variable: " <> identText varname

data Scope = MkScope
    { variables :: Map Text Name
    }

emptyScope :: Scope
emptyScope =
    MkScope
        { variables = mempty
        }

newtype Rename a = MkRename (ReaderT (IORef (Seq RenameError)) IO a)
    deriving newtype (Functor, Applicative, Monad)

runRename :: Rename a -> IO (Either (Seq RenameError) a)
runRename (MkRename readerTIO) = do
    ref <- newIORef []
    result <- runReaderT readerTIO ref
    errors <- readIORef ref
    case errors of
        [] -> pure $ Right result
        _ -> pure $ Left errors

emitError :: RenameError -> Rename ()
emitError error = MkRename $ do
    ref <- ask
    modifyIORef' ref (:|> error)

-- We sometimes need to create dummy names when a variable is not found.
-- These are technically incorrect but allow the renamer to carry on and
-- report *all* errors. In case of errors, we throw away the renamed AST
-- so these shouldn't cause issues
dummyName :: Text -> Name
dummyName = Name.internal

freshName :: Text -> Rename Name
freshName text = MkRename (liftIO (Name.freshNameIO text))

addVariable :: Text -> Name -> Scope -> Scope
addVariable text name scope = scope{variables = insert text name scope.variables}

addFreshVariable :: Text -> Scope -> Rename (Name, Scope)
addFreshVariable text scope = do
    name <- freshName text
    pure (name, addVariable text name scope)

findVariable :: Text -> Scope -> Maybe Name
findVariable text scope = lookup text scope.variables

rename :: Vector (Declaration Parsed) -> IO (Either (Seq RenameError) (Vector (Declaration Renamed)))
rename declarations = runRename $ fmap snd $ mapAccumLM renameDeclaration emptyScope declarations

renameDeclaration :: Scope -> Declaration Parsed -> Rename (Scope, Declaration Renamed)
renameDeclaration scope = \case
    DefineFunction loc name type_ patterns body -> do
        (name, scopeWithFunction) <- addFreshVariable name scope
        type_ <- renameExpr scope type_

        (patterns, scopeTransformers) <- munzip <$> traverse (renamePattern scope) patterns

        -- Function declarations are recursive so we use the extended scope when renaming the body
        body <- renameExpr (compose scopeTransformers scopeWithFunction) body
        pure (scopeWithFunction, DefineFunction loc name type_ patterns body)
    DefineGADT loc name kind constructors -> do
        kind <- renameExpr scope kind
        (name, scope) <- addFreshVariable name scope

        let renameConstructor scope (name, type_) = do
                (name, scopeWithConstructor) <- addFreshVariable name scope
                type_ <- renameExpr scope type_
                pure (scopeWithConstructor, (name, type_))

        (scope, constructors) <- mapAccumLM renameConstructor scope constructors

        pure (scope, DefineGADT loc name kind constructors)

renameExpr :: Scope -> Expr Parsed -> Rename (Expr Renamed)
renameExpr scope = \case
    Var loc text -> case findVariable text scope of
        Nothing -> do
            -- We fall back to replacing variables with built in types with proper syntax
            -- This still makes it possible to shadow them as if they were regular types/variables.
            -- In the future it might make sense to move to these actually just being regular constructors
            -- rather than special, magical language syntax
            case text of
                "Int" -> pure $ Literal loc IntTypeLit
                "String" -> pure $ Literal loc StringTypeLit
                "Type" -> pure $ Literal loc TypeLit
                "Unit" -> pure $ ETupleType loc []
                text | Just (primop, _, _) <- primopFromName text -> pure $ Primop loc primop
                _ -> do
                    emitError (UnboundVariable loc text)
                    pure $ Var loc (dummyName text)
        Just name -> pure $ Var loc name
    App loc funExpr argExpr -> do
        funExpr <- renameExpr scope funExpr
        argExpr <- renameExpr scope argExpr
        pure (App loc funExpr argExpr)
    Lambda loc pattern_ body -> do
        (pattern_, scopeTrans) <- renamePattern scope pattern_
        body <- renameExpr (scopeTrans scope) body
        pure (Lambda loc pattern_ body)
    Case loc scrutinee branches -> do
        scrutinee <- renameExpr scope scrutinee
        branches <- traverse renameBranch branches
        pure (Case loc scrutinee branches)
      where
        renameBranch (pattern_, body) = do
            (pattern_, scopeTrans) <- renamePattern scope pattern_
            body <- renameExpr (scopeTrans scope) body
            pure (pattern_, body)
    TupleLiteral loc arguments -> do
        arguments <- traverse (renameExpr scope) arguments
        pure (TupleLiteral loc arguments)
    Literal loc literal -> pure $ Literal loc literal
    Sequence loc statements -> do
        (_finalScope, statements) <- mapAccumLM renameStatement scope statements
        pure (Sequence loc statements)
    Ascription loc expr type_ -> do
        expr <- renameExpr scope expr
        type_ <- renameExpr scope type_
        pure (Ascription loc expr type_)
    Primop loc primop -> pure $ Primop loc primop
    EPi loc maybeText inputType outputType -> do
        inputType <- renameExpr scope inputType
        (name, boundScope) <- case maybeText of
            Just text -> first Just <$> addFreshVariable text scope
            Nothing -> pure (Nothing, scope)

        outputType <- renameExpr boundScope outputType
        pure (EPi loc name inputType outputType)
    EForall loc text inputType outputType -> do
        inputType <- renameExpr scope inputType
        (name, boundScope) <- addFreshVariable text scope
        outputType <- renameExpr boundScope outputType
        pure (EForall loc name inputType outputType)
    ETupleType loc arguments -> do
        arguments <- traverse (renameExpr scope) arguments
        pure (ETupleType loc arguments)

renameStatement :: Scope -> Statement Parsed -> Rename (Scope, Statement Renamed)
renameStatement scope = \case
    Let loc pattern_ body -> do
        (pattern_, scopeTrans) <- renamePattern scope pattern_

        -- Let's are *non*recursive so we use the unaltered environment here
        body <- renameExpr scope body
        pure (scopeTrans scope, Let loc pattern_ body)
    LetFunction loc text maybeTypeExpr patterns body -> do
        maybeTypeExpr <- traverse (renameExpr scope) maybeTypeExpr
        (patterns, scopeTransformers) <- munzip <$> traverse (renamePattern scope) patterns

        (name, renamedScope) <- addFreshVariable text scope

        -- LetFunction's *are* recursive so we need renamedScope
        body <- renameExpr (compose scopeTransformers renamedScope) body
        pure (renamedScope, LetFunction loc name maybeTypeExpr patterns body)
    RunExpr loc expr -> do
        expr <- renameExpr scope expr
        pure (scope, RunExpr loc expr)

renamePattern :: Scope -> Pattern Parsed -> Rename (Pattern Renamed, Scope -> Scope)
renamePattern scope = \case
    VarPat loc text -> do
        name <- freshName text
        pure (VarPat loc name, addVariable text name)
    ConstructorPat loc name subPatterns -> undefined loc name subPatterns
    IntPat loc value -> pure (IntPat loc value, id)
    StringPat loc value -> pure (StringPat loc value, id)
    TuplePat loc subpatterns -> do
        (subpatterns, transformers) <- munzip <$> traverse (renamePattern scope) subpatterns
        pure (TuplePat loc subpatterns, compose transformers)
    OrPat _loc _left _right -> undefined
    TypePat loc pattern_ type_ -> do
        (pattern_, patternScopeTrans) <- renamePattern scope pattern_
        type_ <- renameExpr scope type_
        pure (TypePat loc pattern_ type_, patternScopeTrans)
