module Vega.Compilation.MIR.CoreToMIR (compileDeclaration) where

import Effectful
import Relude hiding (State, execState, get, modify, put, runState)

import Effectful.State.Static.Local (State, execState, get, modify, put, runState)

import Control.Exception qualified as Assert
import Data.Foldable (foldrM)
import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Data.Unique qualified as Unique
import Data.Vector.Generic qualified as Vector
import Vega.Compilation.Core.Syntax (CoreName, LocalCoreName, Representation)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.MIR.Syntax (Phis (..), Terminator (..))
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Effect.GraphPersistence
import Vega.Effect.GraphPersistence qualified as GraphPersistence
import Vega.Effect.Trace (Trace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique)
import Vega.Panic (panic)
import Vega.Pretty (pretty)
import Vega.Pretty qualified as Pretty
import Vega.Seq.NonEmpty qualified as NonEmpty
import Vega.Syntax qualified as Vega
import Vega.Util (assert, forFoldLM, forIndexed_, indexed, mapAccumLM)

type Compile es = (GraphPersistence :> es, Trace :> es, NewUnique :> es, State CurrentDeclarationState :> es)

data CurrentDeclarationState = MkDeclarationState
    { blocks :: HashMap MIR.BlockDescriptor MIR.Block
    , joinPoints :: HashMap LocalCoreName MIR.BlockDescriptor
    , additionalDeclarations :: Seq MIR.Declaration
    , -- TOOD: preserve the order or something?
      locals :: HashMap LocalCoreName (MIR.Variable, Representation)
    , varCount :: Int
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

compileDeclaration :: (GraphPersistence :> es, Trace :> es, NewUnique :> es) => Core.Declaration -> Eff es (Seq MIR.Declaration)
compileDeclaration = \case
    Core.DefineFunction{name, representationParameters = _, parameters, returnRepresentation, statements, result} -> do
        compileFunction (Core.Global name) parameters returnRepresentation statements result

compileFunction ::
    (GraphPersistence :> es, Trace :> es, NewUnique :> es) =>
    CoreName ->
    Seq (LocalCoreName, Core.Representation) ->
    Core.Representation ->
    Seq Core.Statement ->
    Core.Expr ->
    Eff es (Seq MIR.Declaration)
compileFunction functionName parameters returnRepresentation statements returnExpr = do
    ((initDescriptor, mirParameters), finalDeclarationState) <- runState initialDeclarationState $ do
        mirParameters <- for parameters \(parameterName, representation) -> do
            var <- newVarFromName parameterName
            registerVariable parameterName var representation
            pure (var, representation)

        initialBlock <- newBlock
        compileBody initialBlock statements returnExpr
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
    Core.LetJoin name parameters statements returnExpr :<| rest -> do
        undefined
    {-
    parameterVariables <- for parameters \(parameter, representation) -> do
        variable <- newVar
        registerVariable parameter variable representation
        pure variable
    joinPointBlock <- newBlock parameterVariables
    compileBody joinPointBlock statements returnExpr
    addJoinPoint name joinPointBlock.descriptor
    compileBody block rest returnExpr
    -}
    Core.LetFunction{} :<| rest -> undefined

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
    Core.Lambda parameters statements returnExpr -> do
        let returnRepresentation = undefined returnExpr
        compileLambda block local parameters returnRepresentation statements returnExpr
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
        Core.JumpJoin joinPoint arguments -> do
            (block, arguments) <- compileValues block arguments

            joinPointBlock <- joinPointBlockFor joinPoint
            undefined
        -- finish block (MIR.Jump joinPointBlock arguments)
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
        Core.Lambda parameters statements returnExpr -> do
            lambdaName <- undefined
            let returnRepresentation = undefined returnExpr
            lambdaDeclarations <- compileFunction lambdaName parameters returnRepresentation statements returnExpr
            registerAdditionalDeclarations lambdaDeclarations
            let value = undefined
            finish block (MIR.Return value)
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
        Core.Global globalName -> do
            -- TODO: detect if name is a function and return MIR.LoadGlobalClosure in that case instead
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
            Core.IntLiteral value -> do
                -- TODO: check the size properly etc.
                block <- addInstruction block (MIR.LoadIntLiteral var (fromIntegral value))
                pure (block, var)
            _ -> undefined
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

compileLambda :: (Compile es) => BlockBuilder -> MIR.Variable -> Seq (LocalCoreName, Core.Representation) -> Core.Representation -> Seq Core.Statement -> Core.Expr -> Eff es BlockBuilder
compileLambda block local parameters returnRepresentation statements returnExpr = do
    lambdaName <- undefined

    lambdaDeclarations <- compileFunction lambdaName parameters returnRepresentation statements returnExpr
    registerAdditionalDeclarations lambdaDeclarations
    -- TODO: do this properly with the right layout
    let locals = undefined
    -- addInstruction block (MIR.AllocateClosure local lambdaName locals)
    undefined

addJoinPoint :: (Compile es) => LocalCoreName -> MIR.BlockDescriptor -> Eff es ()
addJoinPoint name blockDescriptor = do
    modify (\state -> state{joinPoints = HashMap.insert name blockDescriptor state.joinPoints})

joinPointBlockFor :: (Compile es) => LocalCoreName -> Eff es MIR.BlockDescriptor
joinPointBlockFor name = do
    MkDeclarationState{joinPoints} <- get
    case HashMap.lookup name joinPoints of
        Nothing -> panic $ "JumpJoin to join point without a block descriptor: " <> pretty name
        Just descriptor -> pure descriptor

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
    , phis :: MIR.Phis
    }

newBlock :: (Compile es) => Eff es BlockBuilder
newBlock = do
    descriptor <- MIR.MkBlockDescriptor <$> newUnique
    pure MkBlockBuilder{descriptor, instructions = [], phis = MkPhis mempty}

addPhis :: (Compile es) => MIR.Phis -> BlockBuilder -> Eff es BlockBuilder
addPhis phis block = do
    pure $ block{phis = mergePhis block.phis phis}

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
