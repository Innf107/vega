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
) where

import Data.Char qualified as Char
import Data.HashMap.Strict qualified as HashMap
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Relude hiding (Type)
import Vega.Compilation.Core.Syntax qualified as Core
import Vega.Debug (showHeadConstructor)
import Vega.Panic (panic)
import Vega.Pretty (Pretty, keyword, number, pretty)
import Vega.Seq.NonEmpty (NonEmpty (..))
import Vega.Syntax hiding (forall_)
import Vega.Syntax qualified as Vega

data Primop
    = ReplicateArray
    | UnsafeReadArray
    | UnsafeWriteArray
    | ArrayLength
    | UnsafeArrayContents
    | CodePoints
    | Panic
    | DebugInt
    deriving (Show)

instance Pretty Primop where
    pretty primop = case show primop of
        "" -> ""
        (first : rest) -> keyword (toText (Char.toLower first : rest))

primops :: HashMap Text Primop
primops =
    [ ("replicateArray", ReplicateArray)
    , ("unsafeReadArray", UnsafeReadArray)
    , ("unsafeWriteArray", UnsafeWriteArray)
    , ("arrayLength", ArrayLength)
    , ("unsafeArrayContents", UnsafeArrayContents)
    , ("codePoints", CodePoints)
    , ("panic", Panic)
    , ("debugInt", DebugInt)
    ]

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
    , ("String", Type (PrimitiveRep BoxedRep))
    , ("Double", Type (PrimitiveRep DoubleRep))
    , ("Bool", Type boolRepresentation)
    , ("Array", forallVisible Monomorphized "r" Rep \r -> [Type r] :-> Type (ArrayRep r))
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
    ReplicateArray -> forall_ "a" \a -> [intType, a] --> arrayType @@ [a]
    UnsafeReadArray -> forall_ "a" \a -> [arrayType @@ [a], intType] --> a
    UnsafeWriteArray -> forall_ "a" \a -> [arrayType @@ [a], intType, a] --> unitType
    ArrayLength -> forall_ "a" \a -> [arrayType @@ [a]] --> intType
    UnsafeArrayContents -> forall_ "a" \a -> [arrayType @@ [a]] --> pointerType @@ [a]
    CodePoints -> [stringType] --> arrayType @@ [int32Type]
    Panic -> forall_ "a" \a -> [stringType] --> a
    DebugInt -> [intType] --> unitType

-- This should really be determined by primopType but we can't currently do that without
-- involving the type checker so we have to write it out manually for now.
primopRepresentation :: (HasCallStack) => Primop -> Seq Core.Representation -> (Seq Core.Representation, Core.Representation)
primopRepresentation primop arguments = case primop of
    ReplicateArray -> ([intRep 64, argument 0], Core.ArrayRep (argument 0))
    UnsafeReadArray -> ([Core.ArrayRep (argument 0), intRep 64], argument 0)
    UnsafeWriteArray -> ([Core.ArrayRep (argument 0), intRep 64, argument 0], unitRep)
    ArrayLength -> ([Core.ArrayRep (argument 0)], intRep 64)
    UnsafeArrayContents -> ([Core.ArrayRep (argument 0)], pointerRep)
    CodePoints -> ([Core.stringRepresentation], Core.ArrayRep (intRep 32))
    Panic -> ([Core.stringRepresentation], argument 0)
    DebugInt -> ([intRep 64], unitRep)
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
                        , "Bool"
                        , "Array"
                        , "Box"
                        , "panic"
                        , "box"
                        , "unbox"
                        ]
                    }
                )
            ]
        }

stringType :: Type
stringType = TypeConstructor (Global (internalName "String"))

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

boolType :: Type
boolType = TypeConstructor (Global (internalName "Bool"))

arrayType :: Type
arrayType = TypeConstructor (Global (internalName "Array"))

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
