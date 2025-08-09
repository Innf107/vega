module Vega.Builtins (
    defaultImportScope,
    builtinGlobals,
    builtinKinds,
    intType,
    stringType,
    doubleType,
    boolType,
) where

import Relude hiding (Type)
import Vega.Syntax

builtinGlobals :: HashMap (Text, NameKind) GlobalName
builtinGlobals = fromList [((name, kind), internalName name) | (name, kind) <- globals]
  where
    globals =
        [ ("Int", TypeConstructorKind)
        , ("String", TypeConstructorKind)
        , ("Double", TypeConstructorKind)
        , ("Bool", TypeConstructorKind)
        ]

builtinKinds :: HashMap GlobalName Kind
builtinKinds =
    [ (internalName "Int", Type (PrimitiveRep IntRep))
    , (internalName "String", Type (PrimitiveRep BoxedRep))
    , (internalName "Double", Type (PrimitiveRep DoubleRep))
    , (internalName "Bool", Type (SumRep [PrimitiveRep UnitRep, PrimitiveRep UnitRep]))
    ]

defaultImportScope :: ImportScope
defaultImportScope =
    MkImportScope
        { imports =
            [
                ( internalModuleName
                , MkImportedItems
                    { qualifiedAliases = []
                    , unqualifiedItems = ["Int", "String", "Double", "Bool"]
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
