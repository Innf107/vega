module Vega.CoreLint (lint, LintError (..)) where

import Control.Monad.Writer (MonadWriter (tell), WriterT (runWriterT))
import Data.Foldable (foldrM)
import Data.Set qualified as Set
import Vega.Difflist
import Vega.Eval (CoreDeclaration, CoreExpr, Value)
import Vega.Name (ident)
import Vega.Prelude
import Vega.Pretty
import Vega.Syntax
import Vega.Util (viaList)

data LintError
    = UnboundVariable Name
    deriving (Show)

lintPrefix :: Doc Ann
lintPrefix = warning "[CORE LINT ERROR]: "

instance Pretty LintError where
    pretty error =
        lintPrefix <> case error of
            UnboundVariable name -> "Unbound variable: " <> ident name

newtype Lint a = MkLint (WriterT (Difflist LintError) IO a)
    deriving (Functor, Applicative, Monad)

data Env = MkEnv
    { definedVariables :: Set Name
    }

emptyEnv :: Env
emptyEnv = MkEnv{definedVariables = []}

lintError :: LintError -> Lint ()
lintError error = MkLint $ tell [error]

defineVar :: Name -> Env -> Env
defineVar name env = env{definedVariables = Set.insert name env.definedVariables}

checkVar :: Env -> Name -> Lint ()
checkVar env name = do
    case lookup name env.definedVariables of
        Just _ -> pure ()
        Nothing -> lintError (UnboundVariable name)

runLint :: Lint a -> IO (a, Seq LintError)
runLint (MkLint writerT) = fmap (second viaList) $ runWriterT writerT

lint :: Vector CoreDeclaration -> IO (Seq LintError)
lint declarations =
    fmap snd
        $ runLint
        $ flip evalStateT emptyEnv
        $ traverse_ (\decl -> StateT (\env -> (env,) <$> lintDeclaration env decl)) declarations

lintDeclaration :: Env -> CoreDeclaration -> Lint Env
lintDeclaration env (CDefineVar name expr) = do
    -- TODO: top level definitions should only be recursive if they bind functions i think?
    env <- pure $ defineVar name env
    lintExpr env expr
    pure env

lintExpr :: Env -> CoreExpr -> Lint ()
lintExpr env = \case
    CVar name -> checkVar env name
    CApp funExpr argExpr -> do
        lintExpr env funExpr
        lintExpr env argExpr
    CLambda name expr -> do
        lintExpr (defineVar name env) expr
    CCase scrutinee cases -> do
        lintExpr env scrutinee
        forM_ cases \(pattern, body) -> do
            env <- lintPattern env pattern
            lintExpr env body
    CLiteral _ -> pure ()
    CTupleLiteral exprs ->
        traverse_ (lintExpr env) exprs
    CLet name body rest -> do
        lintExpr env body
        lintExpr (defineVar name env) rest
    CPrimop _ -> pure ()
    CPi Nothing domain codomain -> do
        lintExpr env domain
        lintExpr env codomain
    CPi (Just name) domain codomain -> do
        lintExpr env domain
        lintExpr (defineVar name env) codomain
    CForall name domain codomain -> do
        lintExpr env domain
        lintExpr (defineVar name env) codomain
    CMeta _meta -> undefined
    CTupleType args ->
        traverse_ (lintExpr env) args
    CQuote _value -> undefined

lintPattern :: Env -> CorePattern Name -> Lint Env
lintPattern env = \case
    CVarPat name -> pure $ defineVar name env
    CWildcardPat -> pure env
    CIntPat _ -> pure env
    CStringPat _ -> pure env
    CTuplePat boundNames ->
        pure (foldr defineVar env boundNames)
