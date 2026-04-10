module Vega.Compilation.LLVM.AttributeFunctionType (
    AttributeFunctionType,
    attributeFunctionType,
    rawFunctionType,
    addFunctionWithAttributes,
    buildCallWithAttributes,
    parametersWithAttributes,
    returnTypeWithAttributes,
) where

import Relude

import Data.Vector.Storable qualified as Storable
import Data.Vector.Strict qualified as Strict
import LLVM.Core qualified as LLVM
import LLVM.InstructionBuilder qualified as LLVMBuilder
import Vega.Util (forIndexed_)

data AttributeFunctionType = MkAttributeFunctionType
    { context :: LLVM.Context
    , parameters :: Strict.Vector (LLVM.Type, Seq LLVM.Attribute)
    , returnType :: LLVM.Type
    , returnAttributes :: Seq LLVM.Attribute
    }

attributeFunctionType :: (?context :: LLVM.Context) => Strict.Vector (LLVM.Type, Seq LLVM.Attribute) -> (LLVM.Type, Seq LLVM.Attribute) -> AttributeFunctionType
attributeFunctionType parameters (returnType, returnAttributes) = MkAttributeFunctionType{parameters, returnType, returnAttributes, context = ?context}

rawFunctionType :: AttributeFunctionType -> LLVM.FunctionType
rawFunctionType MkAttributeFunctionType{parameters, returnType, context} = do
    let ?context = context
    LLVM.functionType (Strict.convert (fmap fst parameters)) returnType False

applyAttributes :: (MonadIO io) => AttributeFunctionType -> LLVM.Value -> io ()
applyAttributes MkAttributeFunctionType{parameters, returnAttributes} function = do
    let parameterAttributes = fmap snd parameters
    forIndexed_ parameterAttributes \attributes index -> do
        for_ attributes \attribute -> do
            LLVM.addAttributeAtIndex function (parameterIndex index) attribute
    for_ returnAttributes \attribute -> do
        LLVM.addAttributeAtIndex function returnIndex attribute

applyCallSiteAttributes :: (MonadIO io) => AttributeFunctionType -> LLVM.Value -> io ()
applyCallSiteAttributes MkAttributeFunctionType{parameters, returnAttributes} function = do
    let parameterAttributes = fmap snd parameters
    forIndexed_ parameterAttributes \attributes index -> do
        for_ attributes \attribute -> do
            LLVM.addCallSiteAttribute function (parameterIndex index) attribute
    for_ returnAttributes \attribute -> do
        LLVM.addCallSiteAttribute function returnIndex attribute



addFunctionWithAttributes :: (MonadIO io) => LLVM.Module -> Text -> AttributeFunctionType -> io LLVM.Value
addFunctionWithAttributes module_ name attributeFunctionType = do
    let functionType = rawFunctionType attributeFunctionType
    function <- LLVM.addFunction module_ name functionType
    applyAttributes attributeFunctionType function
    pure function

buildCallWithAttributes ::
    (MonadIO io) =>
    LLVMBuilder.Builder ->
    AttributeFunctionType ->
    LLVM.Value ->
    Storable.Vector LLVM.Value ->
    Text ->
    io LLVM.Value
buildCallWithAttributes builder attributeFunctionType function arguments varName = do
    call <- LLVMBuilder.buildCall builder (rawFunctionType attributeFunctionType) function arguments varName
    applyCallSiteAttributes attributeFunctionType call
    pure call

parametersWithAttributes :: AttributeFunctionType -> Strict.Vector (LLVM.Type, Seq LLVM.Attribute)
parametersWithAttributes MkAttributeFunctionType{parameters} = parameters

returnTypeWithAttributes :: AttributeFunctionType -> (LLVM.Type, Seq LLVM.Attribute)
returnTypeWithAttributes MkAttributeFunctionType{returnType, returnAttributes} = (returnType, returnAttributes)

-- TODO: move this to llvm-ng and wrap AttributeIndex properly
parameterIndex :: Int -> Int
parameterIndex n = n + 1

returnIndex :: Int
returnIndex = 0

attributeFunctionIndex :: Int
attributeFunctionIndex = 4294967295
