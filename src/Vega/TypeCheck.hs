module Vega.TypeCheck where

import Vega.Syntax

import Effectful hiding (Effect)
import Effectful.Writer.Static.Local (Writer, tell)
import Relude hiding (Type)
import Relude.Extra

import Vega.Util (compose, unzip3Seq, zipWithSeqM)
import Vega.Error (TypeError(..))

import Vega.Effect.GraphPersistence (GraphPersistence)
import Vega.Effect.GraphPersistence qualified as GraphPersistence

import Data.Sequence qualified as Seq
import Vega.Loc (HasLoc, Loc)


newtype Env = MkEnv
    { localTypes :: HashMap LocalName Type
    }

emptyEnv :: Env
emptyEnv = MkEnv mempty

bindVarType :: LocalName -> Type -> Env -> Env
bindVarType name type_ env@MkEnv{localTypes} = env{localTypes = insert name type_ localTypes}

type TypeCheck es = (GraphPersistence :> es, Writer (Seq TypeError) :> es)

checkDeclaration :: (GraphPersistence :> es) => Declaration Renamed -> Eff es (Declaration Typed)
checkDeclaration = undefined

typeError :: (Writer (Seq TypeError) :> es) => TypeError -> Eff es ()
typeError error = tell @(Seq _) [error]

checkDeclarationSyntax :: (TypeCheck es) => Loc -> GlobalName -> DeclarationSyntax Renamed -> Eff es (DeclarationSyntax Typed)
checkDeclarationSyntax loc name = \case
    DefineFunction{typeSignature, parameters, body} -> do
        (functionType, typeSignature) <- checkType Type typeSignature
        (parameterTypes, effect, returnType) <- splitFunctionType functionType
        when (length parameters /= length parameterTypes) $ do
            typeError
                ( FunctionDefinedWithIncorrectNumberOfArguments
                    { loc
                    , functionName = name
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

        pure DefineFunction{typeSignature, parameters, body}
    DefineVariantType{} -> undefined

checkPattern :: (TypeCheck es) => Type -> Pattern Renamed -> Eff es (Pattern Typed, Env -> Env)
checkPattern expectedType = \case
    VarPattern loc var -> pure (VarPattern loc var, bindVarType var expectedType)
    AsPattern loc pattern_ name -> do
        (pattern_, innerTrans) <- checkPattern expectedType pattern_
        pure (AsPattern loc pattern_ name, bindVarType name expectedType . innerTrans)
    ConstructorPattern{} -> undefined
    TypePattern loc innerPattern innerTypeSyntax -> do
        (innerType, innerTypeSyntax) <- checkType Type innerTypeSyntax
        (innerPattern, innerTrans) <- checkPattern innerType innerPattern
        subsumes innerType expectedType
        pure (TypePattern loc innerPattern innerTypeSyntax, innerTrans)
    OrPattern{} -> undefined
    _ -> undefined

inferPattern :: (TypeCheck es) => Pattern Renamed -> Eff es (Pattern Typed, Type, Env -> Env)
inferPattern = \case
    VarPattern loc varName -> do
        meta <- freshMeta (varName.name)
        let type_ = MetaVar meta
        pure (VarPattern loc varName, type_, bindVarType varName type_)
    AsPattern loc innerPattern name -> do
        (innerPattern, innerType, innerTrans) <- inferPattern innerPattern
        pure (AsPattern loc innerPattern name, innerType, bindVarType name innerType . innerTrans)
    _ -> undefined

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
        Lambda loc parameters body -> do
            (parameterTypes, expectedEffect, returnType) <- splitFunctionType expectedType
            when (length parameters /= length parameterTypes) do
                typeError
                    ( LambdaDefinedWithIncorrectNumberOfArguments
                        { loc
                        , expectedType
                        , expected = length parameterTypes
                        , actual = length parameters
                        }
                    )

            let checkParameter parameter parameterType = do
                    checkPattern parameterType parameter
            (parameters, envTransformers) <- Seq.unzip <$> zipWithSeqM checkParameter parameters parameterTypes
            (body, bodyEffect) <- check (compose envTransformers env) returnType body
            subsumesEffect bodyEffect expectedEffect
            pure (Lambda loc parameters body, Pure)
        StringLiteral{} -> deferToInference
        IntLiteral{} -> deferToInference
        DoubleLiteral{} -> deferToInference
        If{loc, condition, thenBranch, elseBranch} -> do
            (condition, conditionEffect) <- check env boolType condition
            (thenBranch, thenEffect) <- check env expectedType thenBranch
            (elseBranch, elseEffect) <- check env expectedType elseBranch

            effect <- unionAll [conditionEffect, thenEffect, elseEffect]
            pure (If{loc, condition, thenBranch, elseBranch}, effect)
        SequenceBlock{loc, statements} -> do
            undefined
        _ -> undefined

infer :: (TypeCheck es) => Env -> Expr Renamed -> Eff es (Type, Expr Typed, Effect)
infer env = \case
    Var loc name -> case name of
        Global globalName -> do
            type_ <- GraphPersistence.getGlobalType globalName
            case type_ of
                Nothing -> error $ "infer: reference to unknown global declaration: " <> show name
                Just type_ -> pure (type_, Var loc name, Pure)
        Local localName -> do
            undefined
    Application{loc, functionExpr, arguments} -> do
        (functionType, functionExpr, functionExprEffect) <- infer env functionExpr
        (argumentTypes, functionEffect, returnType) <- splitFunctionType functionType
        when (length argumentTypes /= length arguments) do
            typeError
                $ FunctionAppliedToIncorrectNumberOfArgs
                    { loc
                    , expected = length argumentTypes
                    , actual = length arguments
                    , functionType
                    }
        let checkArguments argumentExpr argumentType = do
                check env argumentType argumentExpr
        (arguments, argumentEffects) <- Seq.unzip <$> zipWithSeqM checkArguments arguments argumentTypes
        finalEffect <- pure functionExprEffect `unionM` unionAll argumentEffects `unionM` pure functionEffect
        pure (returnType, Application{loc, functionExpr, arguments}, finalEffect)
    VisibleTypeApplication{} ->
        undefined
    Lambda loc parameters body -> do
        (parameters, parameterTypes, envTransformers) <- unzip3Seq <$> traverse inferPattern parameters

        (bodyType, body, bodyEffect) <- infer (compose envTransformers env) body

        pure (Function parameterTypes bodyEffect bodyType, Lambda loc parameters body, Pure)
    StringLiteral loc literal -> pure (stringType, StringLiteral loc literal, Pure)
    IntLiteral loc literal -> pure (intType, IntLiteral loc literal, Pure)
    DoubleLiteral loc literal -> pure (doubleType, DoubleLiteral loc literal, Pure)
    BinaryOperator{} -> undefined
    If{loc, condition, thenBranch, elseBranch} -> do
        (condition, conditionEffect) <- check env boolType condition
        (thenType, thenBranch, thenEffect) <- infer env thenBranch
        (elseType, elseBranch, elseEffect) <- infer env elseBranch
        subsumes thenType elseType
        subsumes elseType thenType
        effect <- unionAll [conditionEffect, thenEffect, elseEffect]
        pure (thenType, If{loc, condition, thenBranch, elseBranch}, effect)
    _ -> undefined

stringType :: Type
stringType = TypeConstructor (Global (internalName "String"))

intType :: Type
intType = TypeConstructor (Global (internalName "Int"))

doubleType :: Type
doubleType = TypeConstructor (Global (internalName "Double"))

boolType :: Type
boolType = TypeConstructor (Global (internalName "Bool"))

checkType :: (TypeCheck es) => Kind -> TypeSyntax Renamed -> Eff es (Type, TypeSyntax Typed)
checkType = undefined

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
