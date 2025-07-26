module Vega.Builtins (defaultImportScope, builtinGlobals, builtinKinds) where

import Relude
import Vega.Syntax


builtinGlobals :: HashMap Text (GlobalName, NameKind)
builtinGlobals = fromList [(name, (internalName name, kind)) | (name, kind) <- globals]
  where
    globals =
        [ ("Int", TypeConstructorKind)
        , ("String", TypeConstructorKind)
        ]

builtinKinds :: HashMap GlobalName Kind
builtinKinds =
    [ (internalName "Int", Type IntRep)
    , (internalName "String", Type BoxedRep)
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
