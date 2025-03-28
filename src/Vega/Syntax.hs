{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Vega.Syntax where

import Data.Unique (Unique)
import Relude hiding (Type)
import Vega.Loc (HasLoc, Loc)

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

internalName :: Text -> GlobalName
internalName name = MkGlobalName{name, moduleName = "<<internal>>"}

data Pass = Parsed | Renamed | Typed

type family XName (p :: Pass) where
    XName Parsed = Text
    XName Renamed = Name
    XName Typed = Name

data Declaration p = MkDeclaration
    { name :: GlobalName
    , syntax :: DeclarationSyntax p
    , loc :: Loc
    }
    deriving (Generic)

data DeclarationSyntax p
    = DefineFunction
        { typeSignature :: TypeSyntax p
        , name :: XName p
        , parameters :: Seq (Pattern p)
        , body :: Expr p
        }
    | DefineVariantType
        { name :: XName p
        , typeParameters :: Seq (XName p)
        , constructors :: Seq (XName p, Seq (TypeSyntax p))
        }
    deriving (Generic)

data Expr p
    = Var (XName p)
    | DataConstructor (XName p)
    | Application
        { functionExpr :: Expr p
        , arguments :: Seq (Expr p)
        }
    | VisibleTypeApplication
        { expr :: Expr p
        , typeArguments :: Seq (TypeSyntax p)
        }
    | Lambda (Seq (Pattern p)) (Expr p)
    | StringLiteral Text
    | IntLiteral Integer
    | DoubleLiteral Double
    | BinaryOperator (Expr p) BinaryOperator (Expr p)
    | If
        { condition :: Expr p
        , thenBranch :: Expr p
        , elseBranch :: Expr p
        }
    | SequenceBlock
        { statements :: Seq (Statement p)
        }
    | Match
        { scrutinee :: Expr p
        , cases :: Seq (MatchCase p)
        }
    deriving (Generic)


data Statement p
    = Run (Expr p)
    | Let (Pattern p) (Expr p)
    | LetFunction
        { name :: XName p
        , typeSignature :: Maybe (TypeSyntax p)
        , parameters :: Seq (Pattern p)
        , body :: Expr p
        }
    deriving (Generic)

data MatchCase p = MkMatchCase
    { pattern_ :: Pattern p
    , body :: Expr p
    }
    deriving (Generic)

data BinaryOperator
    = Add
    | Subtract
    | Multiply
    | Divide
    deriving (Generic)

data Pattern p
    = VarPattern (XName p)
    | AsPattern (Pattern p) (XName p)
    | ConstructorPattern
        { constructor :: XName p
        , subPatterns :: Seq (Pattern p)
        }
    | TypePattern (Pattern p) (TypeSyntax p)
    | OrPattern (Seq (Pattern p))
    deriving (Generic)

data ParsedModule = MkParsedModule
    { imports :: Seq Import
    , declarations :: Seq (Declaration Parsed)
    }
    deriving (Generic)

data Import = ImportUnqualified
    { -- TODO: really just Text?
      moduleName :: Text
    , importedDeclarations :: Seq Text
    }
    deriving (Generic)

data TypeSyntax p
    = TypeConstructorS Loc (XName p)
    | TypeApplicationS Loc (TypeSyntax p) (Seq (TypeSyntax p))
    | TypeVarS Loc (XName p)
    | ForallS Loc (Seq (TypeVarBinderS p)) (TypeSyntax p)
    | PureFunctionS Loc (Seq (TypeSyntax p)) (TypeSyntax p)
    | FunctionS Loc (Seq (TypeSyntax p)) (EffectSyntax p) (TypeSyntax p)
    deriving (Generic)

instance HasLoc (TypeSyntax p)

data TypeVarBinderS p = MkTypeVarBinderS
    { loc :: Loc
    , varName :: XName p
    , kind :: Maybe (KindSyntax p)
    }
    deriving (Generic)

instance HasLoc (TypeVarBinderS p)

data KindSyntax p
    = TypeS Loc
    | EffectS Loc
    | ArrowKindS Loc (Seq (KindSyntax p)) (KindSyntax p)
    deriving (Generic)

instance HasLoc (KindSyntax p)

type EffectSyntax = TypeSyntax

data Type
    = TypeConstructor Name
    | TypeApplication Type (Seq Type)
    | TypeVar LocalName
    | Forall (Seq (LocalName, Kind)) Type
    | Function (Seq Type) Effect Type
    | MetaVar MetaVar
    | Skolem Skolem
    deriving (Generic)

data MetaVar = MkMetaVar
    { underlying :: IORef (Maybe Type)
    , identity :: Unique
    , name :: Text
    }

data Skolem = MkSkolem
    { originalName :: LocalName
    , identity :: Unique
    }

type Effect = Type

data Kind
    = Type
    | Effect
    | ArrowKind (Seq Kind) Kind
    deriving (Generic)
