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
    | ArrayLength
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
    , ("arrayLength", ArrayLength)
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
    [ ("Int", Type (PrimitiveRep IntRep))
    , ("String", Type (PrimitiveRep BoxedRep))
    , ("Double", Type (PrimitiveRep DoubleRep))
    , ("Bool", Type boolRepresentation)
    , ("Array", forallVisible Monomorphized "r" Rep \r -> [Type r] :-> Type (ArrayRep r))
    , ("Box", forallVisible Monomorphized "r" Rep \r -> [Type r] :-> Type (PrimitiveRep BoxedRep))
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
    ArrayLength -> forall_ "a" \a -> [arrayType @@ [a]] --> intType
    CodePoints -> [stringType] --> arrayType @@ [intType]
    Panic -> forall_ "a" \a -> [stringType] --> a
    DebugInt -> [intType] --> unitType

-- This should really be determined by primopType but we can't currently do that without
-- involving the type checker so we have to write it out manually for now.
primopRepresentation :: (HasCallStack) => Primop -> Seq Core.Representation -> (Seq Core.Representation, Core.Representation)
primopRepresentation primop arguments = case primop of
    ReplicateArray -> ([intRep, argument 0], Core.ArrayRep (argument 0))
    UnsafeReadArray -> ([Core.ArrayRep (argument 0), intRep], argument 0)
    ArrayLength -> ([Core.ArrayRep (argument 0)], intRep)
    CodePoints -> ([undefined], Core.ArrayRep intRep)
    Panic -> ([undefined], argument 0)
    DebugInt -> ([intRep], unitRep)
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
                    , unqualifiedItems = ["Int", "String", "Double", "Bool", "Array", "Box", "panic", "box", "unbox"]
                    }
                )
            ]
        }

stringType :: Type
stringType = TypeConstructor (Global (internalName "String"))

intType :: Type
intType = TypeConstructor (Global (internalName "Int"))

doubleType :: Type
doubleType = TypeConstructor (Global (internalName "Double"))

boolType :: Type
boolType = TypeConstructor (Global (internalName "Bool"))

arrayType :: Type
arrayType = TypeConstructor (Global (internalName "Array"))

boxType :: Type
boxType = TypeConstructor (Global (internalName "Box"))

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

intRep :: Core.Representation
intRep = Core.PrimitiveRep Vega.IntRep

unitRep :: Core.Representation
unitRep = Core.ProductRep []
