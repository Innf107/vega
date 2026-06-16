module Vega.Compilation.MIR.CoreToMIR (compileDeclaration) where

import Effectful
import Relude hiding (State, execState, get, modify, put, runState, trace)

import Effectful.State.Static.Local (State, execState, get, modify, put, runState)

import Control.Exception qualified as Assert
import Control.Monad (when)
import Control.Monad.ST.Strict (runST)
import Data.Foldable (Foldable (foldl', foldr'), foldlM, foldrM, for_)
import Data.Foldable qualified as Foldable
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.STRef.Strict (modifySTRef', newSTRef, readSTRef)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Data.Unique qualified as Unique
import Data.Vector.Generic qualified as Vector
import Data.Vector.Strict (Vector)
import Vega.Builtins qualified as Builtins
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName, Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.MIR.Syntax (Phis (..), Terminator (..))
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Debruijn qualified as DeBruijn
import Vega.Effect.GraphPersistence
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Effect.Trace (Category (..), Trace, trace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique)
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Pretty qualified as Pretty
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Syntax qualified as Vega
import Vega.Util (assert, forFoldLM, forIndexed, forIndexed_, indexed, mapAccumLM)
import Vega.Util qualified as Util

type Compile es =
    ( GraphPersistence :> es
    , Trace :> es
    , NewUnique :> es
    , State CurrentDeclarationState :> es
    , IOE :> es
    , ?currentDeclarationName :: Vega.GlobalName
    , ?currentRepresentationParameters :: DeBruijn.Limit
    )

data CurrentDeclarationState = MkDeclarationState
    { blocks :: HashMap MIR.BlockDescriptor MIR.Block
    , joinPoints :: HashMap LocalCoreName JoinPointInfo
    , additionalDeclarations :: Seq MIR.Declaration
    , -- TOOD: preserve the order or something?
      locals :: HashMap LocalCoreName (MIR.Variable, Representation)
    , varCount :: Int
    }

data JoinPointInfo = MkJoinPointInfo
    { block :: MIR.BlockDescriptor
    , phis :: IORef Phis
    , parameters :: Vector (MIR.Variable, Representation)
    }

getLocal :: (HasCallStack, Compile es) => LocalCoreName -> Eff es (MIR.Variable, Representation)
getLocal localName = do
    MkDeclarationState{locals} <- get
    case HashMap.lookup localName locals of
        Just (var, representation) -> pure (var, representation)
        Nothing -> panic $ "Core local not found during MIR generation: " <> pretty localName

initialDeclarationState :: CurrentDeclarationState
initialDeclarationState =
    MkDeclarationState
        { blocks = mempty
        , joinPoints = mempty
        , additionalDeclarations = []
        , locals = mempty
        , varCount = 0
        }

registerVariable :: (Compile es) => LocalCoreName -> MIR.Variable -> Representation -> Eff es ()
registerVariable local variable representation = do
    modify (\state -> state{locals = HashMap.insert local (variable, representation) state.locals})

registerAdditionalDeclarations :: (Compile es) => Seq MIR.Declaration -> Eff es ()
registerAdditionalDeclarations declarations = modify (\state -> state{additionalDeclarations = state.additionalDeclarations <> declarations})

{-# SCC compileDeclaration #-}
compileDeclaration :: (GraphPersistence :> es, IOE :> es, Trace :> es, NewUnique :> es) => Core.Declaration -> Eff es (Seq MIR.Declaration)
compileDeclaration = \case
    Core.DefineFunction{name, representationParameters, parameters, returnRepresentation, statements, result} -> do
        trace CoreToMIR $ "compileDeclaration " <> Vega.prettyGlobal Vega.VarKind name
        let ?currentRepresentationParameters = representationParameters
        compileFunction name parameters returnRepresentation statements result []
    Core.DefineExternalFunction{name, externalName, parameterRepresentations, returnRepresentation} -> do
        pure [MIR.DefineExternalFunction{name, externalName, parameterRepresentations, returnRepresentation}]

data ClosureEntry
    = ClosedVariableEntry
        { variableName :: LocalCoreName
        , variableRepresentation :: Representation
        , closureParameter :: LocalCoreName
        , unboxedClosureRepresentation :: Representation
        , closureIndex :: Int
        }
    | ClosedFunctionEntry
        { variableName :: LocalCoreName
        , globalFunctionName :: Vega.GlobalName
        , closureParameter :: LocalCoreName
        }

compileFunction ::
    ( GraphPersistence :> es
    , IOE :> es
    , Trace :> es
    , NewUnique :> es
    , ?currentRepresentationParameters :: DeBruijn.Limit
    ) =>
    Vega.GlobalName ->
    Seq (LocalCoreName, Core.Representation) ->
    Core.Representation ->
    Seq Core.Statement ->
    Core.Expr ->
    Seq ClosureEntry ->
    Eff es (Seq MIR.Declaration)
compileFunction functionName parameters returnRepresentation statements returnExpr closureEntries = do
    let ?currentDeclarationName = functionName
    ((initDescriptor, mirParameters), finalDeclarationState) <- runState initialDeclarationState $ do
        mirParameters <- for parameters \(parameterName, representation) -> do
            var <- newVarFromName parameterName
            registerVariable parameterName var representation
            pure (var, representation)

        initialBlock <- newBlock
        block <- compileClosureAccesses initialBlock closureEntries
        compileBody block statements returnExpr
        pure (initialBlock.descriptor, mirParameters)
    let declaration =
            MIR.DefineFunction
                { name = functionName
                , parameters = mirParameters
                , returnRepresentation
                , blocks = finalDeclarationState.blocks
                , init = initDescriptor
                }
    pure $ [declaration] <> finalDeclarationState.additionalDeclarations

compileClosureAccesses :: (Compile es) => BlockBuilder -> Seq ClosureEntry -> Eff es BlockBuilder
compileClosureAccesses block entries = go mempty block entries
  where
    go (unboxedClosuresSoFar :: HashMap LocalCoreName MIR.Variable) block = \case
        Empty -> pure block
        ( ClosedVariableEntry
                { variableName
                , variableRepresentation
                , closureParameter
                , unboxedClosureRepresentation
                , closureIndex
                }
                :<| rest
            ) -> do
                var <- newVarFromName variableName
                registerVariable variableName var variableRepresentation

                (closure, block) <- case HashMap.lookup closureParameter unboxedClosuresSoFar of
                    Just closure -> pure (closure, block)
                    Nothing -> do
                        (boxedClosure, _) <- getLocal closureParameter
                        closure <- newVar "closure"
                        block <- addInstruction block (MIR.Unbox closure boxedClosure unboxedClosureRepresentation)
                        pure (closure, block)
                block <-
                    addInstruction
                        block
                        ( MIR.AccessField
                            { var
                            , target = closure
                            , path = [MIR.ProductFieldPath closureIndex]
                            , fieldRepresentation = variableRepresentation
                            }
                        )
                go (HashMap.insert closureParameter closure unboxedClosuresSoFar) block rest
        ClosedFunctionEntry{variableName, globalFunctionName, closureParameter} :<| rest -> do
            (closure, closureRep) <- getLocal closureParameter
            functionPointer <- newVar "fp"
            let representationArguments = fmap Core.ParameterRep (DeBruijn.all ?currentRepresentationParameters)
            block <- addInstruction block (MIR.LoadFunctionPointer functionPointer globalFunctionName representationArguments)
            var <- newVarFromName variableName

            let varRepresentation = Core.ProductRep [Core.PrimitiveRep Vega.PointerRep, closureRep]
            registerVariable variableName var varRepresentation
            block <-
                addInstruction
                    block
                    ( MIR.ProductConstructor
                        var
                        [functionPointer, closure]
                        varRepresentation
                    )
            go unboxedClosuresSoFar block rest

compileBody :: (Compile es) => BlockBuilder -> Seq Core.Statement -> Core.Expr -> Eff es ()
compileBody block statements returnExpr = compileBodyWith compileReturn block statements returnExpr

compileBodyWith :: (Compile es) => (BlockBuilder -> Core.Expr -> Eff es a) -> BlockBuilder -> Seq Core.Statement -> Core.Expr -> Eff es a
compileBodyWith onReturn block statements returnExpr = case statements of
    Empty -> onReturn block returnExpr
    Core.Let name representation expr :<| rest -> do
        var <- newVarFromName name
        registerVariable name var representation
        block <- compileLet block var representation expr
        compileBodyWith onReturn block rest returnExpr
    Core.LetJoin name parameters joinPointStatements joinPointReturnExpr :<| rest -> do
        joinPointBlock <- newBlock

        parameters <-
            Vector.fromList <$> for (toList parameters) \(name, representation) -> do
                mirVariable <- newVarFromName name
                registerVariable name mirVariable representation
                pure (mirVariable, representation)

        addJoinPoint name joinPointBlock.descriptor joinPointBlock.phis parameters

        compileBody joinPointBlock joinPointStatements joinPointReturnExpr

        compileBodyWith onReturn block rest returnExpr
    Core.LetFunction{name, parameters, returnRepresentation, statements, result} :<| rest -> do
        var <- newVarFromName name
        block <- compileLocalFunction block (Just name) var parameters returnRepresentation statements result
        registerVariable name var Core.functionRepresentation
        compileBodyWith onReturn block rest returnExpr

compileLet :: (Compile es) => BlockBuilder -> MIR.Variable -> Representation -> Core.Expr -> Eff es BlockBuilder
compileLet block local representation = \case
    Core.Value value -> do
        (block, target) <- compileValue block value
        addInstruction block (MIR.Identity local target)
    Core.Unreachable -> do
        finish block MIR.Unreachable
        -- TODO: this is kind of silly. Ideally we would stop execution after this but that's not how compileLet currently works
        dummyNextBlock <- newBlock
        pure dummyNextBlock
    Core.Application functionName representationArguments arguments returnRepresentation -> case functionName of
        Core.Local localName -> do
            (closure, _) <- getLocal localName
            (block, arguments) <- compileValues block arguments
            addInstruction block (MIR.CallClosure{var = local, closure, arguments, returnRepresentation})
        Core.Global functionName
            | Vega.isInternalName functionName -> do
                -- We can assume that all internal functions are real functions and not
                -- variables that happen to be closures
                (block, arguments) <- compileValues block arguments
                addInstruction block (MIR.CallDirect{var = local, representationArguments, functionName, arguments, returnRepresentation})
            | otherwise -> do
                GraphPersistence.getGlobalRepresentation functionName >>= \case
                    GlobalVar representation -> do
                        closure <- newVar "closure"
                        block <- addInstruction block (MIR.LoadGlobal{var = closure, representationArguments, globalName = functionName, representation})
                        (block, arguments) <- compileValues block arguments
                        addInstruction block (MIR.CallClosure{var = local, closure, arguments, returnRepresentation})
                    GlobalClosure -> do
                        (block, arguments) <- compileValues block arguments
                        addInstruction block (MIR.CallDirect{var = local, representationArguments, functionName, arguments, returnRepresentation})
    Core.JumpJoin joinPoint _arguments -> do
        panic $ "JumpJoin for join point " <> pretty joinPoint <> " in non-tail position"
    Core.Lambda parameters statements returnExpr returnRepresentation -> do
        compileLocalFunction block Nothing local parameters returnRepresentation statements returnExpr
    Core.ProductAccess{product, index, resultRepresentation} -> do
        (block, product) <- compileValue block product
        addInstruction block $
            MIR.AccessField
                { var = local
                , path = [MIR.ProductFieldPath index]
                , target = product
                , fieldRepresentation = resultRepresentation
                }
    Core.Box value -> do
        (block, mirValue) <- compileValue block value
        block <- addInstruction block (MIR.Box{var = local, target = mirValue})
        pure block
    Core.Unbox{value, innerRepresentation} -> do
        (block, mirValue) <- compileValue block value
        block <- addInstruction block (MIR.Unbox{var = local, boxedTarget = mirValue, representation = innerRepresentation})
        pure block
    Core.PureOperator pureOperator -> do
        (block, _) <- compilePureOperator block (Just local) pureOperator
        pure block
    Core.ConstructorCase{scrutinee, scrutineeRepresentation, cases, default_} -> do
        (block, scrutinee) <- compileValue block scrutinee

        continuationBlock <- newBlock
        let continuationDescriptor = continuationBlock.descriptor

        cases <- for (HashMap.toList cases) \(index, (parameters, bodyStatements, bodyExpr)) -> do
            targetBlockBuilder <- newBlock
            let targetBlockDescriptor = targetBlockBuilder.descriptor
            targetBlockBuilder <- execState targetBlockBuilder $ forIndexed_ parameters \name productIndex -> do
                targetBlockBuilder <- get
                parameterVariable <- newVarFromName name

                let path = [MIR.SumConstructorPath index, MIR.ProductFieldPath productIndex]
                let fieldRepresentation = MIR.representationAtPath scrutineeRepresentation path
                registerVariable name parameterVariable fieldRepresentation
                targetBlockBuilder <-
                    addInstruction
                        targetBlockBuilder
                        ( MIR.AccessField
                            { var = parameterVariable
                            , path
                            , target = scrutinee
                            , fieldRepresentation
                            }
                        )
                put targetBlockBuilder

            joinVar <- newVar "join"
            targetBlockBuilder <- compileBodyWith (\block expr -> compileLet block joinVar representation expr) targetBlockBuilder bodyStatements bodyExpr

            finish targetBlockBuilder (MIR.Jump continuationDescriptor)

            pure (index, targetBlockDescriptor, joinVar)

        default_ <- case default_ of
            Nothing -> pure Nothing
            Just (statements, expr) -> do
                targetBlockBuilder <- newBlock
                let targetBlockDescriptor = targetBlockBuilder.descriptor
                joinVar <- newVar "join"
                targetBlockBuilder <- compileBodyWith (\block expr -> compileLet block joinVar representation expr) targetBlockBuilder statements expr

                finish targetBlockBuilder (MIR.Jump continuationDescriptor)
                pure $ Just (targetBlockDescriptor, joinVar)

        tagVar <- newVar "tag"
        block <- addInstruction block (MIR.LoadSumTag{var = tagVar, sum = scrutinee})
        finish
            block
            ( MIR.SwitchInt
                tagVar
                (fromList (fmap (\(index, block, _) -> (index, block)) cases))
                (fmap fst default_)
            )

        let phis = MkPhis [(local, (representation, fromList (fmap (\(_index, block, joinVar) -> (block, joinVar)) cases)))]
        addPhis phis continuationBlock
    Core.IntCase{} -> undefined

compileReturn :: (Compile es) => BlockBuilder -> Core.Expr -> Eff es ()
compileReturn block expr = do
    let deferToReturn representation = do
            var <- newVar "ret"
            block <- compileLet block var representation expr
            finish block (MIR.Return var)
    case expr of
        Core.Value value -> do
            (block, value) <- compileValue block value
            finish block (MIR.Return value)
        Core.Unreachable -> do
            finish block MIR.Unreachable
        Core.Application functionName representationArguments arguments returnRepresentation -> case functionName of
            Core.Local localName -> do
                (closure, _) <- getLocal localName
                (block, arguments) <- compileValues block arguments
                finish block (MIR.TailCallClosure{closure, arguments, returnRepresentation})
            Core.Global functionName
                | Vega.isInternalName functionName -> do
                    -- We can assume that all internal functions are real functions and not
                    -- variables that happen to be closures
                    (block, arguments) <- compileValues block arguments
                    finish block (TailCallDirect{functionName, representationArguments, arguments, returnRepresentation})
                | otherwise ->
                    GraphPersistence.getGlobalRepresentation functionName >>= \case
                        GlobalVar representation -> do
                            assert (representationArguments == [])
                            closure <- newVar "closure"
                            block <- addInstruction block (MIR.LoadGlobal{var = closure, representationArguments, globalName = functionName, representation})
                            (block, arguments) <- compileValues block arguments
                            finish block (TailCallClosure{closure, arguments, returnRepresentation})
                        GlobalClosure -> do
                            (block, arguments) <- compileValues block arguments
                            finish block (TailCallDirect{functionName, representationArguments, arguments, returnRepresentation})
        Core.JumpJoin joinPointName arguments -> do
            (block, arguments) <- compileValues block arguments

            joinPoint <- joinPointFor joinPointName

            let newPhis =
                    MkPhis $
                        HashMap.fromList $
                            indexed (toList arguments) & fmap \(index, argument) -> do
                                let (target, representation) = joinPoint.parameters Vector.! index
                                (target, (representation, [(block.descriptor, argument)]))

            modifyIORef' joinPoint.phis (`mergePhis` newPhis)

            finish block (MIR.Jump joinPoint.block)
        Core.ProductAccess{resultRepresentation} -> deferToReturn resultRepresentation
        Core.Box{} -> deferToReturn (Core.PrimitiveRep Vega.BoxedRep)
        Core.Unbox{innerRepresentation} -> deferToReturn innerRepresentation
        Core.ConstructorCase scrutinee scrutineeRepresentation cases default_ -> do
            (block, scrutinee) <- compileValue block scrutinee
            tag <- newVar "tag"
            block <- addInstruction block (MIR.LoadSumTag tag scrutinee)

            targetBlocks <- for (HashMap.toList cases) \(index, (parameters, bodyStatements, bodyExpr)) -> do
                targetBlockBuilder <- newBlock
                let targetBlockDescriptor = targetBlockBuilder.descriptor

                targetBlockBuilder <- execState targetBlockBuilder $ forIndexed_ parameters \name productIndex -> do
                    targetBlockBuilder <- get
                    parameterVariable <- newVarFromName name

                    let path = case parameters of
                            -- If the constructor only has a single parameter, we don't have an internal product
                            [_] -> [MIR.SumConstructorPath index]
                            _ -> [MIR.SumConstructorPath index, MIR.ProductFieldPath productIndex]
                    let fieldRepresentation = MIR.representationAtPath scrutineeRepresentation path
                    registerVariable name parameterVariable fieldRepresentation
                    targetBlockBuilder <-
                        addInstruction
                            targetBlockBuilder
                            ( MIR.AccessField
                                { var = parameterVariable
                                , path
                                , target = scrutinee
                                , fieldRepresentation
                                }
                            )
                    put targetBlockBuilder

                compileBody targetBlockBuilder bodyStatements bodyExpr

                pure (index, targetBlockDescriptor)

            defaultBlock <- for default_ \(defaultStatements, defaultExpr) -> do
                defaultBlockBuilder <- newBlock
                let defaultBlockDescriptor = defaultBlockBuilder.descriptor
                compileBody defaultBlockBuilder defaultStatements defaultExpr
                pure defaultBlockDescriptor

            finish block (MIR.SwitchInt{var = tag, cases = fromList targetBlocks, default_ = defaultBlock})
        Core.IntCase{scrutinee, intCases, default_} -> do
            (block, scrutinee) <- compileValue block scrutinee
            targets <- for (HashMap.toList intCases) \(int, (statements, expr)) -> do
                targetBlockBuilder <- newBlock
                let targetBlockDescriptor = targetBlockBuilder.descriptor
                compileBody targetBlockBuilder statements expr
                pure (int, targetBlockDescriptor)
            defaultBlock <- for default_ \(defaultStatements, defaultExpr) -> do
                defaultBlockBuilder <- newBlock
                let defaultBlockDescriptor = defaultBlockBuilder.descriptor
                compileBody defaultBlockBuilder defaultStatements defaultExpr
                pure defaultBlockDescriptor
            finish block (MIR.SwitchInt{var = scrutinee, cases = fromList targets, default_ = defaultBlock})
        Core.Lambda parameters statements returnExpr returnRepresentation -> do
            closure <- newVar "closure"
            block <-
                compileLocalFunction
                    block
                    Nothing
                    closure
                    parameters
                    returnRepresentation
                    statements
                    returnExpr
            finish block (MIR.Return closure)
        Core.PureOperator pureOperator -> do
            (block, var) <- compilePureOperator block Nothing pureOperator
            finish block (MIR.Return var)

compilePureOperator :: (Compile es) => BlockBuilder -> Maybe MIR.Variable -> Core.PureOperatorExpr -> Eff es (BlockBuilder, MIR.Variable)
compilePureOperator block var = \case
    Core.PureOperatorValue value -> do
        (block, target) <- compileValue block value
        case var of
            Nothing -> pure (block, target)
            Just var -> do
                block <- addInstruction block (MIR.Identity var target)
                pure (block, var)
    Core.Add left right -> asArithmeticOperator MIR.Add left right
    Core.Subtract left right -> asArithmeticOperator MIR.Subtract left right
    Core.Multiply left right -> asArithmeticOperator MIR.Multiply left right
    Core.Divide left right -> asArithmeticOperator MIR.Divide left right
    Core.Less left right -> asArithmeticOperator MIR.Less left right
    Core.LessEqual left right -> asArithmeticOperator MIR.LessEqual left right
    Core.Equal left right -> asArithmeticOperator MIR.Equal left right
    Core.NotEqual left right -> asArithmeticOperator MIR.NotEqual left right
  where
    asArithmeticOperator operator left right = do
        var <- targetVar
        (block, left) <- compilePureOperator block Nothing left
        (block, right) <- compilePureOperator block Nothing right
        block <- addInstruction block (MIR.ArithmeticOperator var (operator left right))
        pure (block, var)
    targetVar = case var of
        Nothing -> newVar ""
        Just var -> pure var

compileValues :: (Compile es) => BlockBuilder -> Seq Core.Value -> Eff es (BlockBuilder, Seq MIR.Variable)
compileValues block values = mapAccumLM compileValue block values

compileVarInstantiation :: (Compile es) => BlockBuilder -> CoreName -> Seq Core.Representation -> Eff es (BlockBuilder, MIR.Variable)
compileVarInstantiation block var representationArguments = do
    case var of
        Core.Local name -> do
            (var, _) <- getLocal name
            pure (block, var)
        Core.Global globalName
            | Just _ <- Builtins.asPrimop globalName -> do
                undefined
            | otherwise -> do
                var <- newVar globalName.name
                GraphPersistence.getGlobalRepresentation globalName >>= \case
                    GlobalVar representation -> do
                        block <- addInstruction block (MIR.LoadGlobal{var, representationArguments, globalName, representation})
                        pure (block, var)
                    GlobalClosure -> do
                        block <- addInstruction block (MIR.LoadGlobalClosure{var, representationArguments, functionName = globalName})
                        pure (block, var)

compileValue :: (Compile es) => BlockBuilder -> Core.Value -> Eff es (BlockBuilder, MIR.Variable)
compileValue block = \case
    Core.Var var -> compileVarInstantiation block var []
    Core.Instantiation var representationArguments -> compileVarInstantiation block var (NonEmpty.toSeq representationArguments)
    Core.Literal literal -> do
        var <- newVar ""
        case literal of
            Core.IntLiteral value sizeInBits -> do
                -- TODO: check the size properly etc.
                block <- addInstruction block (MIR.LoadIntLiteral var (fromIntegral value) sizeInBits)
                pure (block, var)
            Core.DoubleLiteral{} -> undefined
            Core.StringLiteral text -> do
                let bytes = encodeUtf8 text
                bytesVar <- newVar "bytes"
                block <- addInstruction block (MIR.LoadByteArrayLiteral bytesVar bytes)
                block <-
                    addInstruction
                        block
                        ( MIR.CallDirect
                            { var
                            , functionName = Builtins.stringFromByteArrayFunction
                            , representationArguments = []
                            , arguments = [bytesVar]
                            , returnRepresentation = Builtins.stringRepresentation
                            }
                        )
                pure (block, var)
    Core.ProductConstructor arguments representation -> do
        (block, arguments) <- compileValues block arguments
        var <- newVar ""
        block <- addInstruction block (MIR.ProductConstructor{var, values = arguments, representation})
        pure (block, var)
    Core.SumConstructor constructorIndex payload resultRepresentation -> do
        var <- newVar ""
        (block, payload) <- compileValue block payload

        block <- addInstruction block (MIR.SumConstructor{var, tag = constructorIndex, payload, representation = resultRepresentation})
        pure (block, var)

compileLocalFunction ::
    (Compile es) =>
    BlockBuilder ->
    Maybe LocalCoreName ->
    MIR.Variable ->
    Seq (LocalCoreName, Core.Representation) ->
    Core.Representation ->
    Seq Core.Statement ->
    Core.Expr ->
    Eff es BlockBuilder
compileLocalFunction block functionName var parameters returnRepresentation statements returnExpr = do
    lambdaUnique <- newUnique
    -- TODO: make this more structured than this string manipulation
    let lambdaName = case functionName of
            Just (Core.UserProvided localName) -> Vega.MkGlobalName{moduleName = localName.parent.moduleName, name = localName.parent.name <> "$" <> localName.name <> show localName.count}
            Just (Core.Generated _)
            Nothing -> Vega.MkGlobalName{moduleName = ?currentDeclarationName.moduleName, name = ?currentDeclarationName.name <> "$lambda$" <> show (Unique.hashUnique lambdaUnique)}

    closureParameterIndex <- newUnique
    let closureParameter = Core.Generated closureParameterIndex

    let initialBoundVariables = Util.viaList (fmap fst (toList parameters) <> Foldable.toList functionName)
    let freeLocals :: Seq LocalCoreName = Util.viaList $ freeLocalVariables initialBoundVariables statements returnExpr

    localsWithRepresentations <- for freeLocals \local -> do
        if local == closureParameter
            then
                pure (local, Core.PrimitiveRep Vega.BoxedRep)
            else do
                (_, representation) <- getLocal local
                pure (local, representation)

    let payloadRepresentation = Core.ProductRep (fmap snd localsWithRepresentations)

    variableClosureEntries <- forIndexed localsWithRepresentations \(local, variableRepresentation) closureIndex -> do
        pure
            ClosedVariableEntry
                { variableName = local
                , variableRepresentation
                , closureParameter
                , unboxedClosureRepresentation = payloadRepresentation
                , closureIndex
                }
    let recursiveEntry = case functionName of
            Nothing -> []
            Just functionName ->
                [ ClosedFunctionEntry
                    { variableName = functionName
                    , globalFunctionName = lambdaName
                    , closureParameter
                    }
                ]

    lambdaDeclarations <-
        compileFunction
            lambdaName
            (parameters <> [(closureParameter, Core.PrimitiveRep Vega.BoxedRep)])
            returnRepresentation
            statements
            returnExpr
            (variableClosureEntries <> recursiveEntry)
    registerAdditionalDeclarations lambdaDeclarations

    closedOverMIRVars <- for freeLocals \local -> do
        (mirVar, _) <- getLocal local
        pure mirVar

    payloadVar <- newVar "payload"
    block <- addInstruction block (MIR.ProductConstructor payloadVar closedOverMIRVars payloadRepresentation)

    boxedPayloadVar <- newVar "boxedPayload"
    block <- addInstruction block (MIR.Box boxedPayloadVar payloadVar)

    functionPointerVar <- newVar "function"
    block <-
        addInstruction
            block
            ( MIR.LoadFunctionPointer
                { var = functionPointerVar
                , functionName = lambdaName
                , representationArguments = (fmap Core.ParameterRep $ DeBruijn.all ?currentRepresentationParameters)
                }
            )

    block <- addInstruction block (MIR.ProductConstructor var [functionPointerVar, boxedPayloadVar] Core.functionRepresentation)
    pure block

freeLocalVariables :: HashSet LocalCoreName -> Seq Core.Statement -> Core.Expr -> HashSet LocalCoreName
freeLocalVariables initialBound statements expr = runST do
    found <- newSTRef HashSet.empty

    let tryAdd bound variable = do
            when (not (HashSet.member variable bound)) do
                modifySTRef' found (HashSet.insert variable)

    let goValue bound = \case
            Core.Var (Core.Global{}) -> pure ()
            Core.Var (Core.Local local) -> tryAdd bound local
            Core.Instantiation (Core.Global{}) _ -> pure ()
            Core.Instantiation (Core.Local local) _ -> tryAdd bound local
            Core.Literal{} -> pure ()
            Core.ProductConstructor{arguments, resultRepresentation = _} -> do
                for_ arguments $ goValue bound
            Core.SumConstructor{constructorIndex = _, payload, resultRepresentation = _} -> do
                goValue bound payload

        goExpr bound = \case
            Core.Value value -> goValue bound value
            Core.Unreachable -> pure ()
            Core.Application{function, representationArguments = _, arguments, resultRepresentation = _} -> do
                case function of
                    Core.Local localName -> tryAdd bound localName
                    Core.Global{} -> pure ()
                for_ arguments (goValue bound)
            Core.JumpJoin joinPointName arguments -> do
                tryAdd bound joinPointName
                for_ arguments (goValue bound)
            Core.Lambda{parameters, statements, returnExpr, returnRepresentation = _} -> do
                let boundInner = foldr' (HashSet.insert . fst) bound parameters
                goBody boundInner statements returnExpr
            Core.ProductAccess{product, index = _, resultRepresentation = _} -> goValue bound product
            Core.Box value -> goValue bound value
            Core.Unbox{value, innerRepresentation = _} -> goValue bound value
            Core.PureOperator pureOperatorExpr -> goPureOperatorExpr bound pureOperatorExpr
            Core.ConstructorCase
                { scrutinee
                , scrutineeRepresentation = _
                , cases
                , default_
                } -> do
                    goValue bound scrutinee
                    for_ cases \(parameters, statements, expr) -> do
                        let boundInner = foldr' HashSet.insert bound parameters
                        goBody boundInner statements expr
                    for_ default_ \(statements, expr) -> goBody bound statements expr
            Core.IntCase
                { scrutinee
                , intCases
                , default_
                } -> do
                    goValue bound scrutinee
                    for_ intCases \(statements, expr) -> goBody bound statements expr
                    for_ default_ \(statements, expr) -> goBody bound statements expr

        goPureOperatorExpr bound = \case
            Core.PureOperatorValue value -> goValue bound value
            Core.Add left right -> do
                goPureOperatorExpr bound left
                goPureOperatorExpr bound right
            Core.Subtract left right -> do
                goPureOperatorExpr bound left
                goPureOperatorExpr bound right
            Core.Multiply left right -> do
                goPureOperatorExpr bound left
                goPureOperatorExpr bound right
            Core.Divide left right -> do
                goPureOperatorExpr bound left
                goPureOperatorExpr bound right
            Core.Less left right -> do
                goPureOperatorExpr bound left
                goPureOperatorExpr bound right
            Core.LessEqual left right -> do
                goPureOperatorExpr bound left
                goPureOperatorExpr bound right
            Core.Equal left right -> do
                goPureOperatorExpr bound left
                goPureOperatorExpr bound right
            Core.NotEqual left right -> do
                goPureOperatorExpr bound left
                goPureOperatorExpr bound right

        goStatement (bound :: HashSet LocalCoreName) = \case
            Core.Let boundName _ expr -> do
                -- Lets are non-recursive
                goExpr bound expr
                pure (HashSet.insert boundName bound)
            Core.LetFunction
                { name
                , parameters
                , returnRepresentation = _
                , statements
                , result
                } -> do
                    let boundByFunction = HashSet.insert name bound
                    let boundInner = foldr' (HashSet.insert . fst) boundByFunction parameters
                    -- We do need to recurse on the body here.
                    -- These variables won't actually be part of our outer function, but we still need to
                    -- keep them around to be able to build up a closure for the inner function
                    -- at this point.
                    goBody boundInner statements result
                    pure boundByFunction
            Core.LetJoin
                { name
                , parameters
                , statements
                , result
                } -> do
                    let boundByFunction = HashSet.insert name bound
                    let boundInner = foldr' (HashSet.insert . fst) boundByFunction parameters

                    goBody boundInner statements result
                    pure boundByFunction
        goBody bound statements expr = do
            boundByStatements <- foldlM goStatement bound statements
            goExpr boundByStatements expr
    goBody initialBound statements expr
    readSTRef found

addJoinPoint :: (Compile es) => LocalCoreName -> MIR.BlockDescriptor -> IORef Phis -> Vector (MIR.Variable, Representation) -> Eff es ()
addJoinPoint name blockDescriptor phis parameters = do
    let info =
            MkJoinPointInfo
                { block = blockDescriptor
                , parameters
                , phis
                }
    modify (\state -> state{joinPoints = HashMap.insert name info state.joinPoints})

joinPointFor :: (Compile es) => LocalCoreName -> Eff es JoinPointInfo
joinPointFor name = do
    MkDeclarationState{joinPoints} <- get
    case HashMap.lookup name joinPoints of
        Nothing -> panic $ "JumpJoin to join point without a block descriptor: " <> pretty name
        Just info -> pure info

newVar :: (Compile es) => Text -> Eff es MIR.Variable
newVar text = do
    state <- get
    let variable = MIR.MkVariable text state.varCount
    put (state{varCount = state.varCount + 1})
    pure variable

newVarFromName :: (Compile es) => LocalCoreName -> Eff es MIR.Variable
newVarFromName = \case
    Core.UserProvided localName -> newVar localName.name
    Core.Generated i -> newVar ("x" <> show (Unique.hashUnique i))

data BlockBuilder = MkBlockBuilder
    { descriptor :: MIR.BlockDescriptor
    , instructions :: Seq MIR.Instruction
    , phis :: IORef MIR.Phis
    }

newBlock :: (Compile es) => Eff es BlockBuilder
newBlock = do
    descriptor <- MIR.MkBlockDescriptor <$> newUnique
    phis <- newIORef (MkPhis mempty)
    pure MkBlockBuilder{descriptor, instructions = [], phis}

addPhis :: (Compile es) => MIR.Phis -> BlockBuilder -> Eff es BlockBuilder
addPhis phis block = do
    modifyIORef block.phis (`mergePhis` phis)
    pure block

mergePhis :: MIR.Phis -> MIR.Phis -> MIR.Phis
mergePhis (MkPhis left) (MkPhis right) = do
    let combineVars var blockDescriptor value1 value2
            | value1 == value2 = value1
            | otherwise = panic $ "Conflicting phi definitons for " <> pretty var <> " from " <> pretty blockDescriptor <> ". " <> pretty value1 <> " vs " <> pretty value2
    let combineBlocks var (rep1, map1) (rep2, map2) = Assert.assert (rep1 == rep2) do
            let map = HashMap.unionWithKey (combineVars var) map1 map2
            (rep1, map)
    MkPhis $ HashMap.unionWithKey combineBlocks left right

-- The f only exists to allow shadowing the builder.
-- If you need this in a pure context, just instantiate it with Identity
addInstruction :: (Applicative f) => BlockBuilder -> MIR.Instruction -> f BlockBuilder
addInstruction builder newInstruction = pure $ builder{instructions = builder.instructions <> [newInstruction]}

finish :: (Compile es) => BlockBuilder -> MIR.Terminator -> Eff es ()
finish (MkBlockBuilder{descriptor, instructions, phis}) terminator = do
    let finishedBlock = MIR.MkBlock{instructions, terminator, phis}
    modify (\state -> state{blocks = HashMap.insert descriptor finishedBlock state.blocks})
