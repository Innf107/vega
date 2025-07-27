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

builtinGlobals :: HashMap Text (GlobalName, NameKind)
builtinGlobals = fromList [(name, (internalName name, kind)) | (name, kind) <- globals]
  where
    globals =
        [ ("Int", TypeConstructorKind)
        , ("String", TypeConstructorKind)
        , ("Double", TypeConstructorKind)
        , ("Bool", TypeConstructorKind)
        ]

builtinKinds :: HashMap GlobalName Kind
builtinKinds =
    [ (internalName "Int", Type IntRep)
    , (internalName "String", Type BoxedRep)
    , (internalName "Double", Type undefined)
    , (internalName "Bool", Type (SumRep [UnitRep, UnitRep]))
    ]

defaultImportScope :: ImportScope
defaultImportScope =
    MkImportScope
        { imports =
            [
                ( internalModuleName
                , MkImportedItems
                    { qualifiedAliases = []
                    , unqualifiedItems = ["Int", "String"]
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
