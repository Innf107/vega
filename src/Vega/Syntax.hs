{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module Vega.Syntax where

import Relude hiding (Type)

data GlobalName = MkGlobalName {moduleName :: Text, name :: Text}
    deriving stock (Generic, Eq)
    deriving anyclass (Hashable)

data LocalName = MkLocalName {parent :: Name, name :: Text, count :: Int}
    deriving stock (Generic, Eq)
    deriving anyclass (Hashable)

data Name
    = Global GlobalName
    | Local LocalName
    deriving stock (Generic, Eq)
    deriving anyclass (Hashable)

data Pass = Parsed | Renamed | Typed

type family XName (p :: Pass) where
    XName Parsed = Text
    XName Renamed = Name
    XName Typed = Name

data Declaration p = MkDeclaration
    { name :: GlobalName
    , syntax :: DeclarationSyntax p
    }
    deriving (Generic)

data DeclarationSyntax p
    = DefineFunction Type (Seq (XName p)) (Expr p)
    deriving (Generic)

data Expr p
    = Var (XName p)
    deriving (Generic)

data ParsedModule = MkParsedModule
    {   imports :: Seq Import
    ,   declarations :: Seq (Declaration Parsed)
    }
    deriving (Generic)

data Import

data PartialType

data Type
    = TypeConstructor Name
    | TypeApplication Type (Seq Type)
    | TypeVar LocalName
    | Function (Seq Type) Type
    deriving (Generic)
