module Vega.Builtins (
    Primop (..),
    primops,
    asPrimop,
    primopType,
    primopRepresentation,
    CorePrimop (..),
    corePrimops,
    asCorePrimop,
    corePrimopType,
    corePrimopRepresentation,
    primitiveTypeConstructors,
    defaultImportScope,
    builtinGlobals,
    intType,
    uintType,
    int32Type,
    uint32Type,
    int16Type,
    uint16Type,
    int8Type,
    uint8Type,
    stringType,
    doubleType,
    boolType,
    arrayType,
    stringRepresentation,
    stringFromByteArrayFunction,
    wiredInDeclarations,
) where

import Data.Char qualified as Char
import Data.HashMap.Strict qualified as HashMap
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Relude hiding (NonEmpty, Type)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Debug (showHeadConstructor)
import Vega.Panic (panic)
import Vega.Pretty (Pretty, keyword, number, pretty)
import Vega.Seq.NonEmpty (NonEmpty (..))
import Vega.Syntax hiding (forall_, stringRepresentation)
import Vega.Syntax qualified as Vega hiding (stringRepresentation)

data Primop
    = -- Array operations
      ReplicateArray
    | UnsafeReadArray
    | UnsafeReadMutableArray
    | UnsafeWriteMutableArray
    | ArrayLength
    | MutableArrayLength
    | UnsafeArrayContents
    | UnsafeMutableArrayContents
    | UnsafeFreezeArray
    | UnsafeThawArray
    | -- Pointer operations
      NullPointer
    | OffsetPointerBytes
    | -- JS specifics
      CodePoints
    | -- Numeric conversions
      Int8ToInt
    | UInt8ToInt
    | Int16ToInt
    | UInt16ToInt
    | Int32ToInt
    | UInt32ToInt
    | UIntToInt
    | IntToInt8
    | IntToUInt8
    | IntToInt16
    | IntToUInt16
    | IntToInt32
    | IntToUInt32
    | IntToUInt
    | -- FFI
      Errno
    | -- Debugging
      Panic
    | DebugInt
    | -- Evil
      UnsafeCoerce
    deriving (Show, Enum, Bounded)

instance Pretty Primop where
    pretty primop = case show primop of
        "" -> ""
        (first : rest) -> keyword (toText (Char.toLower first : rest))

primopVarName :: Primop -> Text
primopVarName = \case
    ReplicateArray -> "replicateArray"
    UnsafeReadArray -> "unsafeReadArray"
    UnsafeReadMutableArray -> "unsafeReadMutableArray"
    UnsafeWriteMutableArray -> "unsafeWriteMutableArray"
    ArrayLength -> "arrayLength"
    MutableArrayLength -> "mutableArrayLength"
    UnsafeArrayContents -> "unsafeArrayContents"
    UnsafeMutableArrayContents -> "unsafeMutableArrayContents"
    UnsafeFreezeArray -> "unsafeFreezeArray"
    UnsafeThawArray -> "unsafeThawArray"
    NullPointer -> "nullPointer"
    OffsetPointerBytes -> "offsetPointerBytes"
    CodePoints -> "codePoints"
    Int8ToInt -> "int8ToInt"
    UInt8ToInt -> "uint8ToInt"
    Int16ToInt -> "int16ToInt"
    UInt16ToInt -> "uint16ToInt"
    Int32ToInt -> "int32ToInt"
    UInt32ToInt -> "uint32ToInt"
    UIntToInt -> "uintToInt"
    IntToInt8 -> "intToInt8"
    IntToUInt8 -> "intToUInt8"
    IntToInt16 -> "intToInt16"
    IntToUInt16 -> "intToUInt16"
    IntToInt32 -> "intToInt32"
    IntToUInt32 -> "intToUInt32"
    IntToUInt -> "intToUInt"
    Errno -> "errno"
    Panic -> "panic"
    DebugInt -> "debugInt"
    UnsafeCoerce -> "unsafeCoerce"

primops :: HashMap Text Primop
primops = fromList [(primopVarName primop, primop) | primop <- [minBound .. maxBound]]

asPrimop :: GlobalName -> Maybe Primop
asPrimop name
    | not (isInternalName name) = Nothing
    | otherwise = case HashMap.lookup name.name primops of
        Just primop -> Just primop
        Nothing -> Nothing

{- | CorePrimops are primitive operations that are already resolved in VegaToCore.
These are primarily operations that have dedicated syntax in core but
behave like regular functions in vega
-}
data CorePrimop
    = Box
    | Unbox
    deriving (Show)

instance Pretty CorePrimop where
    pretty primop = case show primop of
        "" -> ""
        (first : rest) -> keyword (toText (Char.toLower first : rest))

corePrimops :: HashMap Text CorePrimop
corePrimops =
    [ ("box", Box)
    , ("unbox", Unbox)
    ]

asCorePrimop :: GlobalName -> Maybe CorePrimop
asCorePrimop name
    | not (isInternalName name) = Nothing
    | otherwise = case HashMap.lookup name.name corePrimops of
        Just primop -> Just primop
        Nothing -> Nothing

corePrimopType :: CorePrimop -> Type
corePrimopType = \case
    Box -> forall_ "a" \a -> [a] --> boxType @@ [a]
    Unbox -> forall_ "a" \a -> [boxType @@ [a]] --> a

corePrimopRepresentation ::
    (HasCallStack) =>
    CorePrimop ->
    Seq Core.Representation ->
    (Seq Core.Representation, Core.Representation)
corePrimopRepresentation primop arguments = case primop of
    Box -> ([argument 0], Core.PrimitiveRep Vega.BoxedRep)
    Unbox -> ([Core.PrimitiveRep Vega.BoxedRep], argument 0)
  where
    argument i = case Seq.lookup i arguments of
        Just representation -> representation
        Nothing -> panic $ "Core primop " <> pretty primop <> " called with too few arguments. Provided: " <> number (length arguments)

primitiveTypeConstructors :: HashMap Text Kind
primitiveTypeConstructors =
    [ ("Int", Type (PrimitiveRep (IntRep 64))) -- TODO: Int should really be an alias for Int64
    , ("UInt", Type (PrimitiveRep (IntRep 64))) -- TODO: Int should really be an alias for Int64
    , ("Int32", Type (PrimitiveRep (IntRep 32)))
    , ("UInt32", Type (PrimitiveRep (IntRep 32)))
    , ("Int16", Type (PrimitiveRep (IntRep 16)))
    , ("UInt16", Type (PrimitiveRep (IntRep 16)))
    , ("Int8", Type (PrimitiveRep (IntRep 8)))
    , ("UInt8", Type (PrimitiveRep (IntRep 8)))
    , ("Double", Type (PrimitiveRep DoubleRep))
    , ("Array", forallVisible Monomorphized "r" Rep \r -> [Type r] :-> Type (ArrayRep r))
    , -- TODO: we *might* eventually want a different representation for mutable arrays because
      -- they have different write barriers. we *might* be able to do that entirely dynamically though
      ("MutableArray", forallVisible Monomorphized "r" Rep \r -> [Type r] :-> Type (ArrayRep r))
    , ("Box", forallVisible Monomorphized "r" Rep \r -> [Type r] :-> Type (PrimitiveRep BoxedRep))
    , ("Pointer", forallVisible Parametric "r" Rep \r -> [Type r] :-> Type (PrimitiveRep PointerRep))
    ]

builtinGlobals :: HashMap (Text, NameKind) GlobalName
builtinGlobals =
    fromList $
        [((name, VarKind), internalName name) | (name, _) <- HashMap.toList primops]
            <> [((name, VarKind), internalName name) | (name, _) <- HashMap.toList corePrimops]
            <> [((name, TypeConstructorKind), internalName name) | (name, _) <- HashMap.toList primitiveTypeConstructors]

primopType :: Primop -> Type
primopType = \case
    ReplicateArray -> forall_ "a" \a -> [intType, a] --> mutableArrayType @@ [a]
    UnsafeReadArray -> forall_ "a" \a -> [arrayType @@ [a], intType] --> a
    UnsafeReadMutableArray -> forall_ "a" \a -> [mutableArrayType @@ [a], intType] --> a
    UnsafeWriteMutableArray -> forall_ "a" \a -> [mutableArrayType @@ [a], intType, a] --> unitType
    ArrayLength -> forall_ "a" \a -> [arrayType @@ [a]] --> intType
    MutableArrayLength -> forall_ "a" \a -> [mutableArrayType @@ [a]] --> intType
    UnsafeArrayContents -> forall_ "a" \a -> [arrayType @@ [a]] --> pointerType @@ [a]
    UnsafeMutableArrayContents -> forall_ "a" \a -> [mutableArrayType @@ [a]] --> pointerType @@ [a]
    UnsafeFreezeArray -> forall_ "a" \a -> [mutableArrayType @@ [a]] --> arrayType @@ [a]
    UnsafeThawArray -> forall_ "a" \a -> [arrayType @@ [a]] --> mutableArrayType @@ [a]
    NullPointer -> forall_ "a" \a -> [] --> pointerType @@ [a]
    OffsetPointerBytes -> forall_ "a" \a -> [pointerType @@ [a], intType] --> pointerType @@ [a]
    CodePoints -> [stringType] --> arrayType @@ [int32Type]
    Panic -> forall_ "a" \a -> [stringType] --> a
    DebugInt -> [intType] --> unitType
    Int8ToInt -> [int8Type] --> intType
    UInt8ToInt -> [uint8Type] --> intType
    Int16ToInt -> [int16Type] --> intType
    UInt16ToInt -> [uint16Type] --> intType
    Int32ToInt -> [int32Type] --> intType
    UInt32ToInt -> [uint32Type] --> intType
    UIntToInt -> [uintType] --> intType
    IntToInt8 -> [intType] --> int8Type
    IntToUInt8 -> [intType] --> uint8Type
    IntToInt16 -> [intType] --> int16Type
    IntToUInt16 -> [intType] --> uint16Type
    IntToInt32 -> [intType] --> int32Type
    IntToUInt32 -> [intType] --> uint32Type
    IntToUInt -> [intType] --> uintType
    Errno -> [] --> int32Type
    UnsafeCoerce -> forallInferred Monomorphized "r" Rep \r ->
        forallVisible Parametric "a" r \a ->
            forallVisible Parametric "b" r \b ->
                [a] --> b

-- This should really be determined by primopType but we can't currently do that without
-- involving the type checker so we have to write it out manually for now.
primopRepresentation :: (HasCallStack) => Primop -> Seq Core.Representation -> (Seq Core.Representation, Core.Representation)
primopRepresentation primop arguments = case primop of
    ReplicateArray -> ([intRep 64, argument 0], Core.ArrayRep (argument 0))
    UnsafeReadArray -> ([Core.ArrayRep (argument 0), intRep 64], argument 0)
    UnsafeReadMutableArray -> ([Core.ArrayRep (argument 0), intRep 64], argument 0)
    UnsafeWriteMutableArray -> ([Core.ArrayRep (argument 0), intRep 64, argument 0], unitRep)
    ArrayLength -> ([Core.ArrayRep (argument 0)], intRep 64)
    MutableArrayLength -> ([Core.ArrayRep (argument 0)], intRep 64)
    UnsafeArrayContents -> ([Core.ArrayRep (argument 0)], pointerRep)
    UnsafeMutableArrayContents -> ([Core.ArrayRep (argument 0)], pointerRep)
    UnsafeFreezeArray -> ([Core.ArrayRep (argument 0)], Core.ArrayRep (argument 0))
    UnsafeThawArray -> ([Core.ArrayRep (argument 0)], Core.ArrayRep (argument 0))
    NullPointer -> ([], pointerRep)
    OffsetPointerBytes -> ([pointerRep, intRep 64], pointerRep)
    CodePoints -> ([Core.stringRepresentation], Core.ArrayRep (intRep 32))
    Panic -> ([Core.stringRepresentation], argument 0)
    DebugInt -> ([intRep 64], unitRep)
    Int8ToInt -> ([intRep 8], intRep 64)
    UInt8ToInt -> ([intRep 8], intRep 64)
    Int16ToInt -> ([intRep 16], intRep 64)
    UInt16ToInt -> ([intRep 16], intRep 64)
    Int32ToInt -> ([intRep 32], intRep 64)
    UInt32ToInt -> ([intRep 32], intRep 64)
    UIntToInt -> ([intRep 64], intRep 64)
    IntToInt8 -> ([intRep 64], intRep 8)
    IntToUInt8 -> ([intRep 64], intRep 8)
    IntToInt16 -> ([intRep 64], intRep 16)
    IntToUInt16 -> ([intRep 64], intRep 16)
    IntToInt32 -> ([intRep 64], intRep 32)
    IntToUInt32 -> ([intRep 64], intRep 32)
    IntToUInt -> ([intRep 64], intRep 64)
    Errno -> ([], intRep 32)
    UnsafeCoerce -> ([argument 0], argument 0)
  where
    argument i = case Seq.lookup i arguments of
        Just representation -> representation
        Nothing -> panic $ "Primop " <> pretty primop <> " called with too few arguments. Provided: " <> number (length arguments)

defaultImportScope :: ImportScope
defaultImportScope =
    MkImportScope
        { imports =
            [
                ( internalModuleName
                , MkImportedItems
                    { qualifiedAliases = []
                    , unqualifiedItems =
                        [ "Int"
                        , "UInt"
                        , "Int32"
                        , "UInt32"
                        , "Int16"
                        , "UInt16"
                        , "Int8"
                        , "UInt8"
                        , "Double"
                        , "Array"
                        , "MutableArray"
                        , "Box"
                        , "Pointer"
                        , "panic"
                        , "box"
                        , "unbox"
                        ]
                    }
                )
            ,
                ( MkModuleName{package = (MkPackageName "std"), subModules = "String" :<|| []}
                , MkImportedItems
                    { qualifiedAliases = []
                    , unqualifiedItems = ["String"]
                    }
                )
            ,
                ( MkModuleName{package = (MkPackageName "std"), subModules = "Bool" :<|| []}
                , MkImportedItems
                    { qualifiedAliases = []
                    , unqualifiedItems = ["Bool", "True", "False"]
                    }
                )
            ]
        }

-- | Refer to a type defined in the 'std' package
stdName :: NonEmpty Text -> Text -> GlobalName
stdName subModules name = MkGlobalName{name, moduleName = MkModuleName{subModules, package = MkPackageName "std"}}

stdDeclarationName :: NonEmpty Text -> Text -> DeclarationName
stdDeclarationName subModules name = MkDeclarationName{name, moduleName = MkModuleName{subModules, package = MkPackageName "std"}}

-- | This is necessary so we can lower literals to calls to String.fromByteArray
stringRepresentation :: Core.Representation
stringRepresentation =
    Core.ProductRep
        [ Core.ArrayRep (Core.PrimitiveRep (Vega.IntRep 8))
        , Core.PrimitiveRep (Vega.IntRep 64)
        , Core.PrimitiveRep (Vega.IntRep 64)
        ]

stringFromByteArrayFunction :: GlobalName
stringFromByteArrayFunction = stdName ("String" :<|| []) "fromByteArray"

{- | A list of all declarations that might be referred to by primitive operations or syntax (like string literals)
This is important since we always need to compile these, even if they don't *look* like they're reachable from core,
where the operations that refer to them haven't been lowered yet
-}
wiredInDeclarations :: Seq DeclarationName
wiredInDeclarations = [stdDeclarationName ("String" :<|| []) "fromByteArray"]

stringType :: Type
stringType = TypeConstructor (Global (stdName ("String" :<|| []) "String"))

boolType :: Type
boolType = TypeConstructor (Global (stdName ("Bool" :<|| []) "Bool"))

intType :: Type
intType = TypeConstructor (Global (internalName "Int"))

uintType :: Type
uintType = TypeConstructor (Global (internalName "UInt"))

int32Type :: Type
int32Type = TypeConstructor (Global (internalName "Int32"))

uint32Type :: Type
uint32Type = TypeConstructor (Global (internalName "UInt32"))

int16Type :: Type
int16Type = TypeConstructor (Global (internalName "Int16"))

uint16Type :: Type
uint16Type = TypeConstructor (Global (internalName "UInt16"))

int8Type :: Type
int8Type = TypeConstructor (Global (internalName "Int8"))

uint8Type :: Type
uint8Type = TypeConstructor (Global (internalName "UInt8"))

doubleType :: Type
doubleType = TypeConstructor (Global (internalName "Double"))

arrayType :: Type
arrayType = TypeConstructor (Global (internalName "Array"))

mutableArrayType :: Type
mutableArrayType = TypeConstructor (Global (internalName "MutableArray"))

boxType :: Type
boxType = TypeConstructor (Global (internalName "Box"))

pointerType :: Type
pointerType = TypeConstructor (Global (internalName "Pointer"))

unitType :: Type
unitType = Tuple []

(@@) :: Type -> Seq Type -> Type
(@@) = TypeApplication

infixr 0 -->
(-->) :: Seq Type -> Type -> Type
parameters --> result = Function parameters Pure result

infixr 0 :->
pattern (:->) :: Seq Type -> Type -> Type
pattern parameters :-> result = TypeFunction parameters result

forallVisible :: Monomorphization -> Text -> Kind -> (Type -> Type) -> Type
forallVisible monomorphization name kind body =
    let localName = MkLocalName internalDeclarationName name 0
     in Forall
            (MkForallBinder{varName = localName, visibility = Visible, kind, monomorphization} :<|| [])
            (body (TypeVar localName))

forallInferred :: Monomorphization -> Text -> Kind -> (Type -> Type) -> Type
forallInferred monomorphization name kind body =
    let localName = MkLocalName internalDeclarationName name 0
     in Forall
            (MkForallBinder{varName = localName, visibility = Inferred, kind, monomorphization} :<|| [])
            (body (TypeVar localName))

forall_ :: Text -> (Type -> Type) -> Type
forall_ varName body =
    forallInferred
        Monomorphized
        (varName <> "_r")
        Rep
        ( \r ->
            forallVisible Parametric varName (Type r) body
        )

intRep :: Int -> Core.Representation
intRep sizeInBits = Core.PrimitiveRep (Vega.IntRep sizeInBits)

unitRep :: Core.Representation
unitRep = Core.ProductRep []

pointerRep :: Core.Representation
pointerRep = Core.PrimitiveRep Vega.PointerRep
