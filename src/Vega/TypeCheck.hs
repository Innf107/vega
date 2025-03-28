module Vega.TypeCheck where

import Vega.Effect.Dependency
import Vega.Effect.GlobalTypes
import Vega.Syntax

import Effectful hiding (Effect)
import Effectful.Writer.Static.Local (Writer, tell)
import Relude hiding (Type)
import Relude.Extra

import Vega.Util (compose, unzip3Seq, zipWithSeqM)

import Data.Sequence qualified as Seq

data TypeError
    = FunctionDefinedWithIncorrectNumberOfArguments
        { functionName :: GlobalName
        , expectedType :: Type
        , expectedNumberOfArguments :: Int
        , numberOfDefinedParameters :: Int
        }
    | LambdaDefinedWithIncorrectNumberOfArguments
        { expectedType :: Type
        , expected :: Int
        , actual :: Int
        }
    | FunctionAppliedToIncorrectNumberOfArgs
        { functionType :: Type
        , expected :: Int
        , actual :: Int
        }

newtype Env = MkEnv
    { localTypes :: HashMap LocalName Type
    }

emptyEnv :: Env
emptyEnv = MkEnv mempty

bindVarType :: LocalName -> Type -> Env -> Env
bindVarType name type_ env@MkEnv{localTypes} = env{localTypes = insert name type_ localTypes}

type TypeCheck es = (GlobalTypes :> es, Writer (Seq TypeError) :> es)

checkDeclaration :: (GlobalTypes :> es) => Declaration Renamed -> Eff es (Declaration Typed)
checkDeclaration = undefined

typeError :: (Writer (Seq TypeError) :> es) => TypeError -> Eff es ()
typeError error = tell @(Seq _) [error]

checkDeclarationSyntax :: (TypeCheck es) => DeclarationSyntax Renamed -> Eff es (DeclarationSyntax Typed)
checkDeclarationSyntax = \case
    DefineFunction{typeSignature, name, parameters, body} -> do
        (functionType, typeSignature) <- evaluateType typeSignature
        (parameterTypes, effect, returnType) <- splitFunctionType functionType
        when (length parameters /= length parameterTypes) $ do
            typeError
                ( FunctionDefinedWithIncorrectNumberOfArguments
                    { functionName = name
                    , expectedType = functionType
                    , expectedNumberOfArguments = length parameterTypes
                    , numberOfDefinedParameters = length parameters
                    }
                )

        let checkParameter pattern_ type_ = do
                checkPattern type_ pattern_

        (parameters, transformers) <- Seq.unzip <$> zipWithSeqM checkParameter parameters parameterTypes
        let env = compose transformers emptyEnv

        (body, bodyEffect) <- check env returnType body
        subsumesEffect bodyEffect effect

        pure DefineFunction{typeSignature, name, parameters, body}
    DefineVariantType{} -> undefined

checkPattern :: (TypeCheck es) => Type -> Pattern Renamed -> Eff es (Pattern Typed, Env -> Env)
checkPattern expectedType = \case
    VarPattern var -> pure (VarPattern var, bindVarType var expectedType)
    AsPattern pattern_ name -> do
        (pattern_, innerTrans) <- checkPattern expectedType pattern_
        pure (AsPattern pattern_ name, bindVarType name expectedType . innerTrans)
    ConstructorPattern{} -> undefined
    TypePattern innerPattern innerTypeSyntax -> do
        (innerType, innerTypeSyntax) <- evaluateType innerTypeSyntax
        (innerPattern, innerTrans) <- checkPattern innerType innerPattern
        subsumes innerType expectedType
        pure (TypePattern innerPattern innerTypeSyntax, innerTrans)
    OrPattern{} -> undefined

inferPattern :: (TypeCheck es) => Pattern Renamed -> Eff es (Pattern Typed, Type, Env -> Env)
inferPattern = \case
    VarPattern varName -> do
        meta <- freshMeta (varName.name)
        let type_ = MetaVar meta
        pure (VarPattern varName, type_, bindVarType varName type_)
    AsPattern innerPattern name -> do
        (innerPattern, innerType, innerTrans) <-inferPattern innerPattern
        pure (AsPattern innerPattern name, innerType, bindVarType name innerType . innerTrans)

check :: (TypeCheck es) => Env -> Type -> Expr Renamed -> Eff es (Expr Typed, Effect)
check env expectedType expr = do
    let deferToInference = do
            (actualType, expr, effect) <- infer env expr
            subsumes actualType expectedType
            pure (expr, effect)
    case expr of
        Var{} -> deferToInference
        DataConstructor{} -> undefined
        Application{} -> deferToInference
        VisibleTypeApplication{} -> undefined
        Lambda parameters body -> do
            (parameterTypes, expectedEffect, returnType) <- splitFunctionType expectedType
            when (length parameters /= length parameterTypes) do
                typeError
                    ( LambdaDefinedWithIncorrectNumberOfArguments
                        { expectedType
                        , expected = length parameterTypes
                        , actual = length parameters
                        }
                    )

            let checkParameter parameter parameterType = do
                    checkPattern parameterType parameter
            (parameters, envTransformers) <- Seq.unzip <$> zipWithSeqM checkParameter parameters parameterTypes
            (body, bodyEffect) <- check (compose envTransformers env) returnType body
            subsumesEffect bodyEffect expectedEffect
            pure (Lambda parameters body, Pure)
        StringLiteral{} -> deferToInference
        IntLiteral{} -> deferToInference
        DoubleLiteral{} -> deferToInference
        If{condition, thenBranch, elseBranch} -> do
            (condition, conditionEffect) <- check env boolType condition
            (thenBranch, thenEffect) <- check env expectedType thenBranch
            (elseBranch, elseEffect) <- check env expectedType elseBranch

            effect <- unionAll [conditionEffect, thenEffect, elseEffect]
            pure (If{condition, thenBranch, elseBranch}, effect)
        SequenceBlock{statements} -> do
            undefined

infer :: (TypeCheck es) => Env -> Expr Renamed -> Eff es (Type, Expr Typed, Effect)
infer env = \case
    Var name -> case name of
        Global globalName -> do
            type_ <- getGlobalType globalName
            pure (type_, Var name, Pure)
        Local localName -> do
            undefined
    Application{functionExpr, arguments} -> do
        (functionType, functionExpr, functionExprEffect) <- infer env functionExpr
        (argumentTypes, functionEffect, returnType) <- splitFunctionType functionType
        when (length argumentTypes /= length arguments) do
            typeError
                $ FunctionAppliedToIncorrectNumberOfArgs
                    { expected = length argumentTypes
                    , actual = length arguments
                    , functionType
                    }
        let checkArguments argumentExpr argumentType = do
                check env argumentType argumentExpr
        (arguments, argumentEffects) <- Seq.unzip <$> zipWithSeqM checkArguments arguments argumentTypes
        finalEffect <- pure functionExprEffect `unionM` unionAll argumentEffects `unionM` pure functionEffect
        pure (returnType, Application{functionExpr, arguments}, finalEffect)
    VisibleTypeApplication{} ->
        undefined
    Lambda parameters body -> do
        (parameters, parameterTypes, envTransformers) <- unzip3Seq <$> traverse inferPattern parameters

        (bodyType, body, bodyEffect) <- infer (compose envTransformers env) body

        pure (Function parameterTypes bodyEffect bodyType, Lambda parameters body, Pure)
    StringLiteral literal -> pure (stringType, StringLiteral literal, Pure)
    IntLiteral literal -> pure (intType, IntLiteral literal, Pure)
    DoubleLiteral literal -> pure (doubleType, DoubleLiteral literal, Pure)
    BinaryOperator{} -> undefined
    If{condition, thenBranch, elseBranch} -> do
        (condition, conditionEffect) <- check env boolType condition
        (thenType, thenBranch, thenEffect) <- infer env thenBranch
        (elseType, elseBranch, elseEffect) <- infer env elseBranch
        subsumes thenType elseType
        subsumes elseType thenType
        effect <- unionAll [thenEffect, elseEffect]
        pure (thenType, If{condition, thenBranch, elseBranch}, effect)

stringType :: Type
stringType = TypeConstructor (Global (internalName "String"))

intType :: Type
intType = TypeConstructor (Global (internalName "Int"))

doubleType :: Type
doubleType = TypeConstructor (Global (internalName "Double"))

boolType :: Type
boolType = TypeConstructor (Global (internalName "Bool"))

evaluateType :: (TypeCheck es) => TypeSyntax Renamed -> Eff es (Type, TypeSyntax Typed)
evaluateType = undefined

splitFunctionType :: (TypeCheck es) => Type -> Eff es (Seq Type, Effect, Type)
splitFunctionType = undefined

subsumes :: (TypeCheck es) => Type -> Type -> Eff es ()
subsumes = undefined

subsumesEffect :: (TypeCheck es) => Effect -> Effect -> Eff es ()
subsumesEffect = undefined

union :: (TypeCheck es) => Effect -> Effect -> Eff es Effect
union = undefined

unionM :: (TypeCheck es) => Eff es Effect -> Eff es Effect -> Eff es Effect
unionM eff1M eff2M = do
    eff1 <- eff1M
    eff2 <- eff2M
    eff1 `union` eff2

unionAll :: (TypeCheck es) => Seq Effect -> Eff es Effect
unionAll = undefined

freshMeta :: (TypeCheck es) => Text -> Eff es MetaVar
freshMeta = undefined
