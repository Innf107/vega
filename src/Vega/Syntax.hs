{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Vega.Syntax where

import Data.Unique (Unique)
import Relude hiding (Type)
import Vega.Loc (HasLoc, Loc)

import Data.HashSet qualified as HashSet
import GHC.Generics (Generically (..))

newtype ModuleName = MkModuleName Text
    deriving stock (Generic, Eq, Show)
    deriving newtype (Hashable)

data GlobalName = MkGlobalName {moduleName :: ModuleName, name :: Text}
    deriving stock (Generic, Eq, Show)
    deriving anyclass (Hashable)

data LocalName = MkLocalName {parent :: GlobalName, name :: Text, count :: Int}
    deriving stock (Generic, Eq, Show)
    deriving anyclass (Hashable)

data Name
    = Global GlobalName
    | Local LocalName
    deriving stock (Generic, Eq, Show)
    deriving anyclass (Hashable)

unqualifiedName :: Name -> Text
unqualifiedName = \case
    Global global -> global.name
    Local local -> local.name

internalName :: Text -> GlobalName
internalName name = MkGlobalName{name, moduleName = MkModuleName "<<internal>>"}

data Pass = Parsed | Renamed | Typed

type family XName (p :: Pass) where
    XName Parsed = Text
    XName Renamed = Name
    XName Typed = Name

type family XGlobalName (p :: Pass) where
    XGlobalName Parsed = Text
    XGlobalName Renamed = GlobalName
    XGlobalName Typed = GlobalName

type family XLocalName (p :: Pass) where
    XLocalName Parsed = Text
    XLocalName Renamed = LocalName
    XLocalName Typed = LocalName

data Declaration p = MkDeclaration
    { loc :: Loc
    , name :: GlobalName
    , syntax :: DeclarationSyntax p
    }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data DeclarationSyntax p
    = DefineFunction
        { typeSignature :: TypeSyntax p
        , parameters :: Seq (Pattern p)
        , body :: Expr p
        }
    | DefineVariantType
        { typeParameters :: Seq (XName p)
        , constructors :: Seq (XName p, Seq (TypeSyntax p))
        }
    deriving stock (Generic)

data Expr p
    = Var Loc (XName p)
    | DataConstructor Loc (XName p)
    | Application
        { loc :: Loc
        , functionExpr :: Expr p
        , arguments :: Seq (Expr p)
        }
    | PartialApplication
        { loc :: Loc
        , functionExpr :: Expr p
        , partialArguments :: Seq (Maybe (Expr p))
        }
    | VisibleTypeApplication
        { loc :: Loc
        , expr :: Expr p
        , typeArguments :: Seq (TypeSyntax p)
        }
    | Lambda Loc (Seq (Pattern p)) (Expr p)
    | StringLiteral Loc Text
    | IntLiteral Loc Integer
    | DoubleLiteral Loc Rational
    | TupleLiteral Loc (Seq (Expr p))
    | BinaryOperator Loc (Expr p) BinaryOperator (Expr p)
    | If
        { loc :: Loc
        , condition :: Expr p
        , thenBranch :: Expr p
        , elseBranch :: Expr p
        }
    | SequenceBlock
        { loc :: Loc
        , statements :: Seq (Statement p)
        }
    | Match
        { loc :: Loc
        , scrutinee :: Expr p
        , cases :: Seq (MatchCase p)
        }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data Statement p
    = Run Loc (Expr p)
    | Let Loc (Pattern p) (Expr p)
    | LetFunction
        { loc :: Loc
        , name :: XLocalName p
        , typeSignature :: Maybe (TypeSyntax p)
        , parameters :: Seq (Pattern p)
        , body :: Expr p
        }
    | Use Loc (Pattern p) (Expr p)
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data MatchCase p = MkMatchCase
    { loc :: Loc
    , pattern_ :: Pattern p
    , body :: Expr p
    }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data BinaryOperator
    = Add
    | Subtract
    | Multiply
    | Divide
    | And
    | Or
    | Less
    | LessEqual
    | Equal
    | NotEqual
    | GreaterEqual
    | Greater
    deriving stock (Generic)

data Pattern p
    = WildcardPattern Loc
    | VarPattern Loc (XLocalName p)
    | AsPattern Loc (Pattern p) (XLocalName p)
    | ConstructorPattern
        { loc :: Loc
        , constructor :: XName p
        , subPatterns :: Seq (Pattern p)
        }
    | TuplePattern
        { loc :: Loc
        , subPatterns :: Seq (Pattern p)
        }
    | TypePattern Loc (Pattern p) (TypeSyntax p)
    | OrPattern Loc (Seq (Pattern p))
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data ParsedModule = MkParsedModule
    { imports :: Seq Import
    , declarations :: Seq (Declaration Parsed)
    }
    deriving stock (Generic)

data Import
    = ImportUnqualified
        { -- TODO: really just Text?
          loc :: Loc
        , moduleName :: ModuleName
        , importedDeclarations :: Seq Text
        }
    | ImportQualified
        { loc :: Loc
        , moduleName :: ModuleName
        , importedAs :: Text
        }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data TypeSyntax p
    = TypeConstructorS Loc (XName p)
    | TypeApplicationS Loc (TypeSyntax p) (Seq (TypeSyntax p))
    | TypeVarS Loc (XLocalName p)
    | ForallS Loc (Seq (TypeVarBinderS p)) (TypeSyntax p)
    | PureFunctionS Loc (Seq (TypeSyntax p)) (TypeSyntax p)
    | FunctionS Loc (Seq (TypeSyntax p)) (EffectSyntax p) (TypeSyntax p)
    | TupleS Loc (Seq (TypeSyntax p))
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data TypeVarBinderS p = MkTypeVarBinderS
    { loc :: Loc
    , varName :: XLocalName p
    , kind :: Maybe (KindSyntax p)
    }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data KindSyntax p
    = TypeS Loc
    | EffectS Loc
    | ArrowKindS Loc (Seq (KindSyntax p)) (KindSyntax p)
    -- This has to implement Eq and Ord because megaparsec is being silly
    deriving stock (Generic, Eq, Ord)
    deriving anyclass (HasLoc)

type EffectSyntax = TypeSyntax

data Type
    = TypeConstructor Name
    | TypeApplication Type (Seq Type)
    | TypeVar LocalName
    | Forall (Seq (LocalName, Kind)) Type
    | Function (Seq Type) Effect Type
    | Tuple (Seq Type)
    | MetaVar MetaVar
    | Skolem Skolem
    | Pure
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

newtype ImportScope
    = ImportScope
    { imports :: HashMap ModuleName ImportedItems
    }
    deriving stock (Eq, Generic)
    deriving newtype (Semigroup, Monoid)

data ImportedItems = MkImportedItems
    { qualifiedAliases :: HashSet Text
    , unqualifiedItems :: HashSet Text
    }
    deriving (Eq, Generic)
    deriving (Semigroup, Monoid) via Generically ImportedItems
