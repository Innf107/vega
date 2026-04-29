module Vega.Builtins (
    Primop (..),
    primops,
    asPrimop,
    primopType,
    primitiveTypeConstructors,
    defaultImportScope,
    builtinGlobals,
    intType,
    stringType,
    doubleType,
    boolType,
    arrayType,
) where

import Data.HashMap.Strict qualified as HashMap
import Relude hiding (Type)
import Vega.Panic (panic)
import Vega.Seq.NonEmpty (NonEmpty (..))
import Vega.Syntax hiding (forall_)

data Primop
    = ReplicateArray
    | UnsafeReadArray
    | ArrayLength
    | CodePoints
    | Panic
    | DebugInt

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

primitiveTypeConstructors :: HashMap Text Kind
primitiveTypeConstructors =
    [ ("Int", Type (PrimitiveRep IntRep))
    , ("String", Type (PrimitiveRep BoxedRep))
    , ("Double", Type (PrimitiveRep DoubleRep))
    , ("Bool", Type boolRepresentation)
    , ("Array", forallVisible Monomorphized "r" Rep \r -> [Type r] :-> Type (ArrayRep r))
    ]

builtinGlobals :: HashMap (Text, NameKind) GlobalName
builtinGlobals =
    fromList $
        [((name, VarKind), internalName name) | (name, _) <- HashMap.toList primops]
            <> [((name, TypeConstructorKind), internalName name) | (name, _) <- HashMap.toList primitiveTypeConstructors]

primopType :: Primop -> Type
primopType = \case
    ReplicateArray -> forall_ "a" \a -> [intType, a] --> arrayType @@ [a]
    UnsafeReadArray -> forall_ "a" \a -> [arrayType @@ [a], intType] --> a
    ArrayLength -> forall_ "a" \a -> [arrayType @@ [a]] --> intType
    CodePoints -> [stringType] --> arrayType @@ [intType]
    Panic -> forall_ "a" \a -> [stringType] --> a
    DebugInt -> [intType] --> unitType

defaultImportScope :: ImportScope
defaultImportScope =
    MkImportScope
        { imports =
            [
                ( internalModuleName
                , MkImportedItems
                    { qualifiedAliases = []
                    , unqualifiedItems = ["Int", "String", "Double", "Bool", "Array", "panic"]
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