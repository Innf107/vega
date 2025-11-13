module Vega.Builtins (
    defaultImportScope,
    builtinGlobals,
    builtinKinds,
    builtinTypes,
    intType,
    stringType,
    doubleType,
    boolType,
    arrayType,
) where

import Relude hiding (Type)
import Vega.Seq.NonEmpty (NonEmpty (..))
import Vega.Syntax hiding (forall_)

builtinGlobals :: HashMap (Text, NameKind) GlobalName
builtinGlobals = fromList [((name, kind), internalName name) | (name, kind) <- globals]
  where
    globals =
        [ ("Int", TypeConstructorKind)
        , ("String", TypeConstructorKind)
        , ("Double", TypeConstructorKind)
        , ("Bool", TypeConstructorKind)
        , ("Array", TypeConstructorKind)
        , ("replicateArray", VarKind)
        , ("readArray", VarKind)
        , ("arrayLength", VarKind)
        , ("codePoints", VarKind)
        , ("panic", VarKind)
        ]

builtinKinds :: HashMap GlobalName Kind
builtinKinds =
    [ (internalName "Int", Type (PrimitiveRep IntRep))
    , (internalName "String", Type (PrimitiveRep BoxedRep))
    , (internalName "Double", Type (PrimitiveRep DoubleRep))
    , (internalName "Bool", Type (SumRep [PrimitiveRep UnitRep, PrimitiveRep UnitRep]))
    , (internalName "Array", forallVisible Monomorphized "r" Rep \r -> [Type r] --> Type (ArrayRep r))
    ]

builtinTypes :: HashMap GlobalName Type
builtinTypes =
    [ (internalName "replicateArray", forall_ "a" \a -> [intType, a] --> arrayType @@ [a])
    , (internalName "readArray", forall_ "a" \a -> [arrayType @@ [a], intType] --> a)
    , (internalName "arrayLength", forall_ "a" \a -> [arrayType @@ [a]] --> intType)
    , (internalName "codePoints", [stringType] --> arrayType @@ [intType])
    , (internalName "panic", forall_ "a" \a -> [stringType] --> a)
    ]

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

(@@) :: Type -> Seq Type -> Type
(@@) = TypeApplication

infixr 0 -->
(-->) :: Seq Type -> Type -> Type
parameters --> result = Function parameters Pure result

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