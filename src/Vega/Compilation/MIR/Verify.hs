module Vega.Compilation.MIR.Verify (verify) where

import Effectful
import Relude hiding (Reader, State, ask, evalState, get, modify, put, runReader, runState)

import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Effectful.Reader.Static (Reader, ask, runReader)
import Effectful.State.Static.Local (State, evalState, get, put)
import Vega.Compilation.Core.Syntax (CoreName, Representation)
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Pretty (Ann, Doc, keyword, pretty, (<+>))

type FunctionSignatures = HashMap CoreName (Seq Representation, Representation)

data VerifyState = MkVerifyState
    { representations :: HashMap MIR.Variable Representation
    , returnRepresentation :: Representation
    , outstandingExpectedPhiSources :: HashMap MIR.Variable (HashMap MIR.BlockDescriptor MIR.Variable)
    , knownPredecessors :: HashMap MIR.BlockDescriptor (HashSet MIR.BlockDescriptor)
    }

type Verify es = (IOE :> es, Reader FunctionSignatures :> es, State VerifyState :> es, Reader MIR.BlockDescriptor :> es)

verify :: (IOE :> es) => MIR.Program -> Eff es (Seq (Doc Ann))
verify program = do
    let functionSignatures = computeFunctionSignatures program
    for_ program.declarations verifyDeclaration
        & runReader functionSignatures
    undefined

verifyDeclaration :: (Reader FunctionSignatures :> es, IOE :> es) => MIR.Declaration -> Eff es ()
verifyDeclaration = \case
    MIR.DefineFunction{parameters, returnRepresentation, init, blocks} -> do
        let state =
                MkVerifyState
                    { representations = HashMap.fromList (toList parameters)
                    , returnRepresentation
                    , outstandingExpectedPhiSources = mempty
                    , knownPredecessors = mempty
                    }

        evalState state do
            for_ (HashMap.toList blocks) \(descriptor, block) -> do
                runReader descriptor (verifyBlock block)

addExpectedPhiSource :: (Verify es) => MIR.Variable -> MIR.BlockDescriptor -> MIR.Variable -> Eff es ()
addExpectedPhiSource target sourceBlock sourceVar = do
    state@MkVerifyState{knownPredecessors, outstandingExpectedPhiSources} <- get
    currentBlock <- ask
    case HashMap.lookup currentBlock knownPredecessors of
        Just sources
            | HashSet.member sourceBlock sources -> do
                -- We definitely know the representation of the source variable at this point
                -- (if it exists)
                assertSameRep target sourceVar
        _ -> do
            let updateSource = \case
                    Just sources -> case HashMap.lookup sourceBlock sources of
                        Just previousVar -> do
                            verificationError ("Duplicate phi sources for variable " <> pretty target <> " at source block " <> pretty sourceBlock <> ": " <> pretty target <+> "vs" <+> pretty previousVar)
                            pure (Just sources)
                        Nothing -> pure (Just (HashMap.insert sourceBlock sourceVar sources))
                    Nothing -> pure (Just (HashMap.singleton sourceBlock sourceVar))

            newOutstandingExpectedPhiSources <- HashMap.alterF updateSource target outstandingExpectedPhiSources

            put (state{outstandingExpectedPhiSources = newOutstandingExpectedPhiSources})

addPredecessor :: (Verify es) => MIR.BlockDescriptor -> MIR.BlockDescriptor -> Eff es ()
addPredecessor target sourceBlock = do
    state@MkVerifyState{knownPredecessors, outstandingExpectedPhiSources} <- get

    currentBlock <- ask
    let insertPredecessor = \case
            Just sources
                | HashSet.member sourceBlock sources -> do
                    verificationError $ "Duplicate predecessor for block " <> pretty target <> ": " <> pretty sourceBlock
                    pure (Just sources)
                | otherwise -> pure (Just (HashSet.insert sourceBlock sources))
            Nothing -> pure (Just (HashSet.singleton sourceBlock))
    newKnownPredecessors <- HashMap.alterF insertPredecessor target knownPredecessors

    case HashMap.lookup target outstandingExpectedPhiSources of


assertSameRep :: (Verify es) => MIR.Variable -> MIR.Variable -> Eff es ()
assertSameRep var1 var2 = do
    undefined

verifyBlock :: (Verify es) => MIR.Block -> Eff es ()
verifyBlock block = do
    let MIR.MkPhis phis = block.phis
    for_ (HashMap.toList phis) \(targetVar, sources) -> do
        for_ (HashMap.toList sources) \(sourceBlock, sourceVar) -> do
            addExpectedPhiSource targetVar sourceBlock sourceVar
    undefined
    

verificationError :: Doc Ann -> Eff es ()
verificationError = undefined

computeFunctionSignatures :: MIR.Program -> HashMap CoreName (Seq Representation, Representation)
computeFunctionSignatures program = do
    let toSignature = \case
            MIR.DefineFunction{name, parameters, returnRepresentation} -> Just (name, (fmap snd parameters, returnRepresentation))
    fromList (mapMaybe toSignature (toList program.declarations))
