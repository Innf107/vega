module Vega.Syntax where

import Relude hiding (Type)

data GlobalName = MkGlobalName {moduleName :: Text, name :: Text}

data LocalName = MkLocalName {parent :: Name, name :: Text, count :: Int}

data Name
    = Global GlobalName
    | Local LocalName
    deriving (Generic)

data Pass = Parsed | Renamed | Typed

type family XName (p :: Pass) where
    XName Parsed = Text
    XName Renamed = Name
    XName Typed = Name

data Declaration p = MkDeclaration
    { name :: Name
    , syntax :: DeclarationSyntax p
    }

data DeclarationSyntax p
    = DefineFunction (XName p)

data PartialType

data Type
    = TypeConstructor Name
    | TypeApplication Type (Seq Type)
    | TypeVar LocalName
    | Function (Seq Type) Type

