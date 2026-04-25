module Vega.Compilation.MIR.Monomorphize (monomorphize) where

import Relude hiding (State, evalState, execState, get, modify, put, runState, state)

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Text qualified as Text
import Data.Traversable (for)
import Effectful (Eff, (:>))
import Effectful.State.Static.Local (State, execState, get, modify)
import TextBuilder qualified
import Vega.Compilation.Core.Syntax (CoreName, Representation (..))
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Compilation.MIR.Syntax qualified as MIR
import Vega.Debruijn qualified as DeBruijn
import Vega.Effect.Trace (Category (Monomorphization), Trace, trace, withTrace)
import Vega.Panic (panic)
import Vega.Pretty (intercalateDoc, lparen, pretty, rparen)
import Vega.Pretty qualified as Pretty
import Vega.Syntax qualified as Vega

type Monomorphize es =
    ( ?program :: MIR.Program
    , ?arguments :: Seq Representation
    , State MonomorphizedDefinitions :> es
    , Trace :> es
    )

-- We split MonomorphizedDefinitions up into the names of definitions we monomorphized and their actual
-- contents (with all parameters substituted).
-- We do this for two reasons:
--  1) If we monomorphize a recursive function, we may look it up again before we are done monomorphizing so
--      we must not recursively try to monomorphize ourselves. In this case, monomorphizedSoFar will be filled in
--      but not declarations
--  2) We can use (CoreName, Seq Representation) keys to skip generating the monomorphized names when looking up a declaration
--      but we still keep monomorphized names for the actual declaration and skip needing to traverse them all again at the end
data MonomorphizedDefinitions = MkMonomorphizedDeclarations
    { monomorphizedSoFar :: HashMap (Vega.GlobalName, Seq Representation) Vega.GlobalName
    , declarations :: HashMap CoreName MIR.Declaration
    }

monomorphize :: (Trace :> es) => MIR.Program -> Vega.GlobalName -> Eff es MIR.Program
monomorphize program entryPoint = do
    let ?program = program

    let initialState =
            MkMonomorphizedDeclarations
                { monomorphizedSoFar = []
                , declarations = []
                }

    MkMonomorphizedDeclarations{declarations} <- execState initialState $ do
        monomorphizeDeclaration entryPoint []
    pure (MIR.MkProgram{declarations})

monomorphizeDeclaration :: (State MonomorphizedDefinitions :> es, ?program :: MIR.Program, Trace :> es) => Vega.GlobalName -> Seq Representation -> Eff es Vega.GlobalName
monomorphizeDeclaration name argumentRepresentations
    | Vega.isInternalName name = pure name
    | otherwise = withTrace Monomorphization ("monomorphizeDeclaration " <> Vega.prettyGlobal Vega.VarKind name <> lparen "[" <> intercalateDoc ", " (fmap pretty argumentRepresentations) <> rparen "]") do
        MkMonomorphizedDeclarations{monomorphizedSoFar} <- get
        case HashMap.lookup (name, argumentRepresentations) monomorphizedSoFar of
            Just instantiationName -> pure instantiationName
            Nothing -> do
                let instantiationName = monomorphizedName name argumentRepresentations
                modify (\state -> state{monomorphizedSoFar = HashMap.insert (name, argumentRepresentations) instantiationName monomorphizedSoFar})

                let preMonoDeclaration = case HashMap.lookup (Core.Global name) ?program.declarations of
                        Just declaration -> declaration
                        Nothing -> panic $ "Declaration not found: " <> Vega.prettyGlobal Vega.VarKind name
                declaration <- substituteMonomorphizedDeclaration instantiationName preMonoDeclaration argumentRepresentations
                modify (\state -> state{declarations = HashMap.insert (Core.Global instantiationName) declaration state.declarations})
                pure instantiationName

substituteMonomorphizedDeclaration ::
    ( State MonomorphizedDefinitions :> es
    , Trace :> es
    , ?program :: MIR.Program
    ) =>
    Vega.GlobalName ->
    MIR.Declaration ->
    Seq Representation ->
    Eff es MIR.Declaration
substituteMonomorphizedDeclaration instantiationName declaration arguments = do
    let ?arguments = arguments
    case declaration of
        MIR.DefineFunction{name = _uninstantiatedName, parameters, returnRepresentation, init, blocks} -> do
            parameters <- for parameters \(name, rep) -> pure (name, substituteRepresentation rep)

            returnRepresentation <- pure $ substituteRepresentation returnRepresentation

            blocks <- for blocks monomorphizeBlock

            pure (MIR.DefineFunction{name = Core.Global instantiationName, parameters, returnRepresentation, init, blocks})

monomorphizeBlock :: (Monomorphize es) => MIR.Block -> Eff es MIR.Block
monomorphizeBlock block = do
    phis <- monomorphizePhis block.phis
    instructions <- for block.instructions monomorphizeInstruction
    terminator <- monomorphizeTerminator block.terminator
    pure MIR.MkBlock{phis, instructions, terminator}

monomorphizePhis :: (Monomorphize es) => MIR.Phis -> Eff es MIR.Phis
monomorphizePhis (MIR.MkPhis phiMap) = do
    phiMap <- for phiMap \(representation, sourceVariables) ->
        pure (substituteRepresentation representation, sourceVariables)
    pure (MIR.MkPhis phiMap)

monomorphizeInstruction :: (Monomorphize es) => MIR.Instruction -> Eff es MIR.Instruction
monomorphizeInstruction instruction = case instruction of
    MIR.Identity _ _
    MIR.ArithmeticOperator _ _
    MIR.Box _ _
    MIR.LoadIntLiteral _ _
    MIR.LoadSumTag _ _ -> pure instruction
    MIR.AccessField{var, path, target, fieldRepresentation} ->
        pure (MIR.AccessField{var, path, target, fieldRepresentation = substituteRepresentation fieldRepresentation})
    MIR.Unbox{var, boxedTarget, representation} ->
        pure (MIR.Unbox{var, boxedTarget, representation = substituteRepresentation representation})
    MIR.ProductConstructor{var, values, representation} ->
        pure (MIR.ProductConstructor{var, values, representation = substituteRepresentation representation})
    MIR.SumConstructor{var, tag, payload, representation} ->
        pure (MIR.SumConstructor{var, tag, payload, representation = substituteRepresentation representation})
    MIR.AllocClosure{var, closedValues, representation} ->
        pure (MIR.AllocClosure{var, closedValues, representation = substituteRepresentation representation})
    MIR.LoadGlobal{var, globalName, representationArguments, representation} -> do
        monomorphizedGlobalName <- monomorphizeDeclaration globalName (fmap substituteRepresentation representationArguments)
        pure
            ( MIR.LoadGlobal
                { var
                , globalName = monomorphizedGlobalName
                , representationArguments = []
                , representation = substituteRepresentation representation
                }
            )
    MIR.LoadGlobalClosure{var, functionName, representationArguments} -> do
        monomorphizedFunctionName <- monomorphizeDeclaration functionName (fmap substituteRepresentation representationArguments)
        pure (MIR.LoadGlobalClosure{var, functionName = monomorphizedFunctionName, representationArguments = []})
    MIR.CallDirect{var, functionName, representationArguments, arguments, returnRepresentation} -> do
        monomorphizedFunctionName <- monomorphizeDeclaration functionName (fmap substituteRepresentation representationArguments)
        pure
            ( MIR.CallDirect
                { var
                , functionName = monomorphizedFunctionName
                , representationArguments = []
                , arguments
                , returnRepresentation = substituteRepresentation returnRepresentation
                }
            )
    MIR.CallClosure{var, closure, arguments, returnRepresentation} -> do
        pure (MIR.CallClosure{var, closure, arguments, returnRepresentation = substituteRepresentation returnRepresentation})

monomorphizeTerminator :: (Monomorphize es) => MIR.Terminator -> Eff es MIR.Terminator
monomorphizeTerminator terminator = case terminator of
    MIR.Return _
    MIR.Unreachable
    MIR.Jump _
    MIR.SwitchInt _ _ _ -> pure terminator
    MIR.TailCallClosure{closure, arguments, returnRepresentation} -> do
        pure (MIR.TailCallClosure{closure, arguments, returnRepresentation = substituteRepresentation returnRepresentation})
    MIR.TailCallDirect
        { functionName
        , representationArguments
        , arguments
        , returnRepresentation
        } -> do
            monomorphizedFunctionName <- monomorphizeDeclaration functionName (fmap substituteRepresentation representationArguments)
            pure
                ( MIR.TailCallDirect
                    { functionName = monomorphizedFunctionName
                    , representationArguments = []
                    , arguments
                    , returnRepresentation = substituteRepresentation returnRepresentation
                    }
                )

substituteRepresentation :: (HasCallStack, ?arguments :: Seq Representation) => Representation -> Representation
substituteRepresentation = \case
    ParameterRep index -> case DeBruijn.lookup index ?arguments of
        Just substitution -> substitution
        Nothing -> panic $ "Parameter representation " <> pretty (ParameterRep index) <> " out of range for arguments [" <> Pretty.intercalateDoc ", " (fmap pretty ?arguments) <> "]"
    ProductRep inner -> ProductRep (fmap substituteRepresentation inner)
    SumRep inner -> SumRep (fmap substituteRepresentation inner)
    ArrayRep inner -> ArrayRep (substituteRepresentation inner)
    FunctionPointerRep -> FunctionPointerRep
    PrimitiveRep primitive -> PrimitiveRep primitive

-- TODO: maybe don't use naive text representations like this
monomorphizedName :: Vega.GlobalName -> Seq Representation -> Vega.GlobalName
monomorphizedName globalName = \case
    Empty -> globalName
    representations -> globalName{Vega.name = globalName.name <> "[" <> Text.intercalate "," (fmap renderRepresentation (toList representations)) <> "]"}

renderRepresentation :: Representation -> Text
renderRepresentation representation = TextBuilder.toText $ go representation
  where
    go = \case
        ProductRep inner -> "P(" <> TextBuilder.intercalateMap "," go inner <> ")"
        SumRep inner -> "S(" <> TextBuilder.intercalateMap "," go inner <> ")"
        ArrayRep inner -> "A(" <> go inner <> ")"
        FunctionPointerRep -> "FP"
        PrimitiveRep prim -> case prim of
            Vega.BoxedRep -> "B"
            Vega.IntRep -> "I"
            Vega.DoubleRep -> "D"
        ParameterRep index -> panic $ "Trying to render non-monomorphized parameter representation " <> pretty (ParameterRep index)
