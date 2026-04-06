module Vega.Compilation.MIR.Verify (verify) where

import Effectful
import Relude hiding (Reader, State, ask, evalState, get, modify, put, runReader, runState)

import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import Data.Traversable (for)
import Effectful.Reader.Static (Reader, ask, runReader)
import Effectful.State.Static.Local (State, evalState, get, put, runState)
import Vega.Compilation.Core.Syntax (CoreName, Representation (..))
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Effect.Output.Static.Local (Output, output, runOutputSeq)
import Vega.Panic (panic)
import Vega.Pretty (Ann, Doc, keyword, number, pretty, (<+>))
import Vega.Syntax (PrimitiveRep (..))
import Vega.Syntax qualified as Vega

type FunctionSignatures = HashMap CoreName (Seq Representation, Representation)

data VerifyState = MkVerifyState
    { representations :: HashMap MIR.Variable Representation
    , returnRepresentation :: Representation
    , outstandingExpectedPhiSources :: HashMap MIR.BlockDescriptor (HashMap MIR.Variable (HashMap MIR.BlockDescriptor MIR.Variable))
    , knownPredecessors :: HashMap MIR.BlockDescriptor (HashSet MIR.BlockDescriptor)
    }

type Verify es =
    ( IOE :> es
    , Output (Doc Ann) :> es
    , Reader FunctionSignatures :> es
    , State VerifyState :> es
    , Reader MIR.BlockDescriptor :> es
    )

verify :: (IOE :> es) => MIR.Program -> Eff es (Seq (Doc Ann))
verify program = do
    let functionSignatures = computeFunctionSignatures program
    errorMessages <-
        for program.declarations verifyDeclaration
            & runReader functionSignatures
            & runOutputSeq
            & fmap snd
    pure errorMessages

verifyDeclaration :: (Reader FunctionSignatures :> es, Output (Doc Ann) :> es, IOE :> es) => MIR.Declaration -> Eff es ()
verifyDeclaration = \case
    MIR.DefineFunction{parameters, returnRepresentation, init, blocks} -> do
        let state =
                MkVerifyState
                    { representations = HashMap.fromList (toList parameters)
                    , returnRepresentation
                    , outstandingExpectedPhiSources = mempty
                    , knownPredecessors = mempty
                    }

        ((), finalState) <- runState state do
            for_ (HashMap.toList blocks) \(descriptor, block) -> do
                runReader descriptor (verifyBlock block)

        for_ (HashMap.toList finalState.outstandingExpectedPhiSources) \(targetBlock, sources) -> do
            for_ (HashMap.toList sources) \(targetVariable, sourceBlocks) -> do
                for_ (HashMap.toList sourceBlocks) \(sourceBlock, sourceVariable) -> do
                    verificationError
                        ( "Phi node for variable "
                            <> pretty targetVariable
                            <> " in block "
                            <> pretty targetBlock
                            <> " mentions non-predecessor block "
                            <> pretty sourceBlock
                            <> " with variable "
                            <> pretty sourceVariable
                        )

addExpectedPhiSource :: (Verify es) => MIR.Variable -> MIR.BlockDescriptor -> MIR.Variable -> Eff es ()
addExpectedPhiSource target sourceBlock sourceVar = do
    state@MkVerifyState{knownPredecessors, outstandingExpectedPhiSources} <- get
    currentBlock <- ask @MIR.BlockDescriptor
    case HashMap.lookup currentBlock knownPredecessors of
        Just sources
            | HashSet.member sourceBlock sources -> do
                -- We definitely know the representation of the source variable at this point
                -- (if it exists)
                assertSameRep target sourceVar
        _ -> do
            let newOutstandingExpectedPhiSources =
                    outstandingExpectedPhiSources
                        & ( modifyDefault currentBlock $
                                modifyDefault target $
                                    HashMap.insert sourceBlock sourceVar
                          )
            put (state{outstandingExpectedPhiSources = newOutstandingExpectedPhiSources})

modifyDefault ::
    (Hashable key, Monoid value) =>
    key ->
    (value -> value) ->
    HashMap key value ->
    HashMap key value
modifyDefault key f map = HashMap.alter (\case Nothing -> Just (f mempty); Just value -> Just (f value)) key map

addPredecessor :: (Verify es) => MIR.BlockDescriptor -> MIR.BlockDescriptor -> Eff es ()
addPredecessor target sourceBlock = do
    state@MkVerifyState{knownPredecessors, outstandingExpectedPhiSources} <- get

    currentBlock <- ask @MIR.BlockDescriptor
    let insertPredecessor = \case
            Just sources
                | HashSet.member sourceBlock sources -> do
                    verificationError $ "Duplicate predecessor for block " <> pretty target <> ": " <> pretty sourceBlock
                    pure (Just sources)
                | otherwise -> pure (Just (HashSet.insert sourceBlock sources))
            Nothing -> pure (Just (HashSet.singleton sourceBlock))
    newKnownPredecessors <- HashMap.alterF insertPredecessor target knownPredecessors

    case HashMap.lookup target outstandingExpectedPhiSources of
        Nothing -> put (state{knownPredecessors = newKnownPredecessors})
        Just sources -> do
            newSources <- flip HashMap.traverseWithKey sources \targetVariable sourceVars -> do
                HashMap.alterF
                    ( \case
                        Nothing -> pure Nothing
                        Just sourceVariable -> do
                            assertSameRep targetVariable sourceVariable
                            pure Nothing
                    )
                    currentBlock
                    sourceVars
            put (state{knownPredecessors = newKnownPredecessors, outstandingExpectedPhiSources = HashMap.insert target newSources outstandingExpectedPhiSources})

repOf :: (Verify es) => MIR.Variable -> Eff es (Maybe Representation)
repOf var = do
    MkVerifyState{representations} <- get
    case HashMap.lookup var representations of
        Just rep -> pure (Just rep)
        Nothing -> do
            verificationError $ "No recorded representation for variable " <> pretty var
            pure Nothing

assertSameRep :: (Verify es) => MIR.Variable -> MIR.Variable -> Eff es ()
assertSameRep var1 var2 = do
    rep1 <- repOf var1
    rep2 <- repOf var2
    case (rep1, rep2) of
        (Just rep1, Just rep2)
            | rep1 == rep2 -> pure ()
            | otherwise ->
                verificationError $
                    "Representation mismatch between"
                        <+> pretty var1
                        <+> keyword ":"
                        <+> pretty rep1
                        <+> "and"
                        <+> pretty var2
                        <+> keyword ":"
                        <+> pretty rep2
        -- We already emitted an error message in this case
        _ -> pure ()

verifyBlock :: (Verify es) => MIR.Block -> Eff es ()
verifyBlock block = do
    let MIR.MkPhis phis = block.phis
    for_ (HashMap.toList phis) \(targetVar, sources) -> do
        for_ (HashMap.toList sources) \(sourceBlock, sourceVar) -> do
            addExpectedPhiSource targetVar sourceBlock sourceVar

    for_ block.instructions verifyInstruction
    verifyTerminator block.terminator

verifyInstruction :: (Verify es) => MIR.Instruction -> Eff es ()
verifyInstruction = \case
    MIR.Add var arg1 arg2 -> do
        checkVarRepresentation arg1 (PrimitiveRep IntRep) var
        checkVarRepresentation arg2 (PrimitiveRep IntRep) var
        insertVarRepresentation var (PrimitiveRep IntRep)
    MIR.AccessField{var, path, target, fieldRepresentation} -> do
        targetRepresentation <- varRepresentation target
        verifyValidPath var targetRepresentation path fieldRepresentation
        insertVarRepresentation var fieldRepresentation
    MIR.Box{var, target = _} -> do
        insertVarRepresentation var (PrimitiveRep BoxedRep)
    MIR.Unbox{var, boxedTarget, representation} -> do
        checkVarRepresentation boxedTarget (PrimitiveRep BoxedRep) var
        insertVarRepresentation var representation
    MIR.ProductConstructor{var, values, representation} -> do
        insertVarRepresentation var representation
        case representation of
            ProductRep fields
                | length fields /= length values ->
                    verificationError $
                        "Invalid number of arguments to ProductConstructor\n  Expected: "
                            <> pretty (length fields)
                            <> "\n    Actual: "
                            <> pretty (length values)
                | otherwise -> do
                    for_ (zip (toList values) (toList fields)) \(value, expectedRepresentation) -> do
                        checkVarRepresentation value expectedRepresentation var
            _ -> verificationError $ "Invalid non-product representation for ProductConstructor: " <> pretty representation
    MIR.SumConstructor{var, tag, payload, representation} -> do
        insertVarRepresentation var representation
        case representation of
            SumRep constructors -> case Seq.lookup tag constructors of
                Nothing -> verificationError $ "SumConstructor tag" <+> pretty tag <+> "is out of bounds for representation" <+> pretty representation
                Just expectedRepresentation -> checkVarRepresentation payload expectedRepresentation var
            _ -> verificationError $ "Invalid non-sum representation for SumConstructor: " <> pretty representation
    MIR.AllocClosure{var, closedValues, representation} -> do
        undefined
    MIR.LoadGlobalClosure{var, functionName = _} -> do
        -- TODO: check that functionName exists
        insertVarRepresentation var Core.functionRepresentation
    MIR.LoadGlobal{var, globalName, representation} -> do
        -- TODO: check that the global has the correct representation
        insertVarRepresentation var representation
    MIR.LoadIntLiteral{var, literal = _} -> do
        insertVarRepresentation var (PrimitiveRep IntRep)
    MIR.LoadSumTag{var, sum} -> do
        -- TODO: what is the representation of var now?
        -- IntRep isn't actually correct (might be close enough for now though, the LLVM backend will do something more sensible)
        -- it should be int8/int16/... depending on the number of constructors but we don't actually have that in MIR yet
        insertVarRepresentation var (PrimitiveRep IntRep)
    MIR.CallDirect{var, functionName, arguments, returnRepresentation} -> do
        functionSignatures <- ask @FunctionSignatures
        let (expectedArgumentRepresentations, expectedReturnRepresentation) = case HashMap.lookup (Core.Global functionName) functionSignatures of
                Nothing -> panic $ "Missing signature for function" <+> pretty (Core.Global functionName)
                Just signature -> signature

        when (length arguments /= length expectedArgumentRepresentations) do
            verificationError $
                "Invalid number of arguments in call to "
                    <> pretty (Core.Global functionName)
                    <> "\n  Expected: "
                    <> number (length expectedArgumentRepresentations)
                    <> "\n    Actual: "
                    <> number (length arguments)
        for_ (Seq.zip arguments expectedArgumentRepresentations) \(argument, representation) -> do
            checkVarRepresentation argument representation var

        when (returnRepresentation /= expectedReturnRepresentation) do
            verificationError $
                "Invalid return representation expected from call to "
                    <> pretty (Core.Global functionName)
                    <> "  Called as: "
                    <> pretty returnRepresentation
                    <> "  Function defined as returning "
                    <> pretty expectedReturnRepresentation
        insertVarRepresentation var returnRepresentation
    MIR.CallClosure{var, closure, arguments = _, returnRepresentation} -> do
        -- We can't actually verify that the arguments are correct here
        checkVarRepresentation closure Core.functionRepresentation var
        insertVarRepresentation var returnRepresentation

verifyValidPath :: (Verify es) => MIR.Variable -> Representation -> MIR.Path -> Representation -> Eff es ()
verifyValidPath var fullInputRep path expectedRep = go fullInputRep path
  where
    go representation = \case
        Empty
            | representation /= expectedRep -> do
                verificationError $ "Mismatched representation in path access for " <> pretty var <> ".\n  Expected:" <+> pretty expectedRep <> "\n    Actual:" <+> pretty representation <> "\n  In path access " <> MIR.prettyPath path <> " on " <> pretty fullInputRep
            | otherwise -> pure ()
        (MIR.ProductFieldPath index :<| rest) -> case representation of
            ProductRep fields -> case Seq.lookup index fields of
                Just innerRep -> go innerRep rest
                Nothing -> verificationError $ "Out-of-bounds product field access" <+> number index <+> "for representation" <+> pretty representation <> "\n  In path access for " <> pretty var <> " accessing " <> MIR.prettyPath path <> " on " <> pretty fullInputRep
            _ -> verificationError $ "Trying to access non-product representation " <> pretty representation <> " with a ProductConstructorPath.\n  In path access for " <> pretty var <> " accessing " <> MIR.prettyPath path <> " on " <> pretty fullInputRep
        (MIR.SumConstructorPath index :<| rest) -> case representation of
            SumRep constructors -> case Seq.lookup index constructors of
                Just innerRep -> go innerRep rest
                Nothing -> verificationError $ "Out-of-bounds sum constructor access" <+> number index <+> "for representation" <+> pretty representation <> "\n  In path access for " <> pretty var <> " accessing " <> MIR.prettyPath path <> " on " <> pretty fullInputRep
            _ -> verificationError $ "Trying to access non-sum representation " <> pretty representation <> " with a SumConstructorPath.\n  In path access for " <> pretty var <> " accessing " <> MIR.prettyPath path <> " on " <> pretty fullInputRep

checkVarRepresentation :: (Verify es) => MIR.Variable -> Representation -> MIR.Variable -> Eff es ()
checkVarRepresentation variable expectedRepresentation definitionVar = do
    actualRepresentation <- varRepresentation variable
    when (actualRepresentation /= expectedRepresentation) do
        verificationError
            ( pretty definitionVar
                <> ": Mismatched representation for "
                <> pretty variable
                <> ".\n    Expected: "
                <> pretty expectedRepresentation
                <> "\n      Actual: "
                <> pretty actualRepresentation
            )

insertVarRepresentation :: (Verify es) => MIR.Variable -> Representation -> Eff es ()
insertVarRepresentation variable representation = do
    state@MkVerifyState{representations} <- get
    case HashMap.lookup variable representations of
        Just previous -> verificationError ("Duplicate representations recorded for " <> pretty variable <> ": " <> pretty previous <+> "and" <+> pretty representation)
        Nothing -> pure ()
    put state{representations = HashMap.insert variable representation representations}

varRepresentation :: (Verify es) => MIR.Variable -> Eff es Representation
varRepresentation variable = do
    MkVerifyState{representations} <- get
    case HashMap.lookup variable representations of
        Just representation -> pure representation
        Nothing -> panic $ "No recorded representation for variable" <+> pretty variable

verifyTerminator :: (Verify es) => MIR.Terminator -> Eff es ()
verifyTerminator = \case
    MIR.Return var -> do
        MkVerifyState{returnRepresentation} <- get
        checkVarRepresentation var returnRepresentation var
    MIR.Jump block -> undefined
    MIR.SwitchInt{var, cases = _} -> do
        -- TODO: this also needs to work for other, smaller int representations
        checkVarRepresentation var (PrimitiveRep IntRep) var
    -- TODO: verify that the targets actually exist
    MIR.TailCallDirect{functionName, arguments = _, returnRepresentation} -> do
        -- TODO: verify that the function exists and the arguments are correct
        MkVerifyState{returnRepresentation = ownReturnRepresentation} <- get
        when (ownReturnRepresentation /= returnRepresentation) do
            verificationError $ "Tail call into" <+> Vega.prettyGlobal Vega.VarKind functionName <+> "returns different representation.\n  Expected:" <+> pretty ownReturnRepresentation <+> "\n    Actual:" <+> pretty returnRepresentation
    MIR.TailCallClosure{closure, arguments = _, returnRepresentation} -> do
        MkVerifyState{returnRepresentation = ownReturnRepresentation} <- get
        when (ownReturnRepresentation /= returnRepresentation) do
            verificationError $ "Tail call into closure" <+> pretty closure <+> "returns different representation.\n  Expected:" <+> pretty ownReturnRepresentation <+> "\n    Actual:" <+> pretty returnRepresentation

verificationError :: (Output (Doc Ann) :> es) => Doc Ann -> Eff es ()
verificationError message = output message

computeFunctionSignatures :: MIR.Program -> HashMap CoreName (Seq Representation, Representation)
computeFunctionSignatures program = do
    let toSignature = \case
            MIR.DefineFunction{name, parameters, returnRepresentation} -> Just (name, (fmap snd parameters, returnRepresentation))
    fromList (mapMaybe toSignature (toList program.declarations))
