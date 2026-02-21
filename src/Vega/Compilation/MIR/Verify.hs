module Vega.Compilation.MIR.Verify (verify) where

import Effectful
import Relude hiding (Reader, State, ask, evalState, get, modify, put, runReader, runState)

import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Traversable (for)
import Effectful.Reader.Static (Reader, ask, runReader)
import Effectful.State.Static.Local (State, evalState, get, put, runState)
import Vega.Compilation.Core.Syntax (CoreName, Representation)
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Effect.Output.Static.Local (Output, output, runOutputSeq)
import Vega.Pretty (Ann, Doc, keyword, pretty, (<+>))

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
    MIR.Add target var1 var2 -> undefined
    MIR.AccessField target path source -> undefined
    MIR.Box{} -> undefined
    MIR.Unbox{} -> undefined
    MIR.ProductConstructor{} -> undefined
    MIR.SumConstructor{} -> undefined
    MIR.AllocClosure{} -> undefined
    MIR.LoadGlobalClosure{} -> undefined
    MIR.LoadGlobal{} -> undefined
    MIR.LoadIntLiteral{} -> undefined
    MIR.LoadSumTag{} -> undefined
    MIR.CallDirect{} -> undefined
    MIR.CallClosure{} -> undefined

verifyTerminator :: (Verify es) => MIR.Terminator -> Eff es ()
verifyTerminator = undefined

verificationError :: (Output (Doc Ann) :> es) => Doc Ann -> Eff es ()
verificationError message = output message

computeFunctionSignatures :: MIR.Program -> HashMap CoreName (Seq Representation, Representation)
computeFunctionSignatures program = do
    let toSignature = \case
            MIR.DefineFunction{name, parameters, returnRepresentation} -> Just (name, (fmap snd parameters, returnRepresentation))
    fromList (mapMaybe toSignature (toList program.declarations))
