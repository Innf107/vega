{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Vega.Syntax where

import Data.Unique (Unique)
import Relude hiding (Type)
import Vega.Loc (HasLoc, Loc)

import Data.Sequence (Seq (..))
import GHC.Generics (Generically (..))
import Vega.Pretty (Ann, Doc, Pretty (..), globalConstructorText, globalIdentText, intercalateDoc, keyword, localConstructorText, localIdentText, lparen, meta, rparen, skolem, (<+>))

newtype ModuleName = MkModuleName Text
    deriving stock (Generic, Eq, Show)
    deriving newtype (Hashable)

renderModuleName :: ModuleName -> Text
renderModuleName (MkModuleName name) = name

data DeclarationName = MkDeclarationName {moduleName :: ModuleName, name :: Text}
    deriving stock (Generic, Eq, Show)
    deriving anyclass (Hashable)

instance Pretty DeclarationName where
    pretty (MkDeclarationName{moduleName, name}) = globalIdentText (renderModuleName moduleName <> ":" <> name)

data GlobalName = MkGlobalName {moduleName :: ModuleName, name :: Text}
    deriving stock (Generic, Eq, Show)
    deriving anyclass (Hashable)

data LocalName = MkLocalName {parent :: DeclarationName, name :: Text, count :: Int}
    deriving stock (Generic, Eq, Show)
    deriving anyclass (Hashable)

renderLocalName :: LocalName -> Text
renderLocalName MkLocalName{parent = _, name, count} = case count of
    0 -> name
    _ -> name <> "@" <> show count

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

type family XLocalName (p :: Pass) where
    XLocalName Parsed = Text
    XLocalName Renamed = LocalName
    XLocalName Typed = LocalName

data NameKind
    = VarKind
    | TypeConstructorKind
    | DataConstructorKind
    deriving stock (Generic, Eq)
    deriving anyclass (Hashable)

data Declaration p = MkDeclaration
    { loc :: Loc
    , name :: DeclarationName
    , syntax :: DeclarationSyntax p
    }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data DeclarationSyntax p
    = DefineFunction
        { name :: GlobalName
        , typeSignature :: TypeSyntax p
        , declaredTypeParameters :: Maybe (Seq (XLocalName p))
        , parameters :: Seq (Pattern p)
        , body :: Expr p
        }
    | DefineVariantType
        { name :: GlobalName
        , typeParameters :: Seq (ForallBinderS p)
        , constructors :: Seq (Loc, GlobalName, Seq (TypeSyntax p))
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
    | Lambda
        { loc :: Loc
        , boundTypeParameters :: Seq (XLocalName p)
        , parameters :: Seq (Pattern p)
        , body :: Expr p
        }
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
    | ForallS Loc (Seq (ForallBinderS p)) (TypeSyntax p)
    | PureFunctionS Loc (Seq (TypeSyntax p)) (TypeSyntax p)
    | FunctionS Loc (Seq (TypeSyntax p)) (EffectSyntax p) (TypeSyntax p)
    | TupleS Loc (Seq (TypeSyntax p))
    | -- Kinds
      RepS Loc
    | TypeS Loc (KindSyntax p)
    | EffectS Loc
    | SumRepS Loc (Seq (TypeSyntax p))
    | ProductRepS Loc (Seq (TypeSyntax p))
    | UnitRepS Loc
    | EmptyRepS Loc
    | BoxedRepS Loc
    | KindS Loc
    deriving stock (Generic)
    deriving anyclass (HasLoc)

type KindSyntax = TypeSyntax

typeApplicationS :: Loc -> TypeSyntax p -> Seq (TypeSyntax p) -> TypeSyntax p
typeApplicationS _ constructor Empty = constructor
typeApplicationS loc constructor arguments = TypeApplicationS loc constructor arguments

forallS :: Loc -> Seq (ForallBinderS p) -> TypeSyntax p -> TypeSyntax p
forallS _loc Empty result = result
forallS loc binders result = ForallS loc binders result

data Monomorphization
    = Monomorphized
    | Parametric
    deriving (Generic, Show, Eq)

data ForallBinderS p
    = UnspecifiedBinderS
        { loc :: Loc
        , varName :: XLocalName p
        }
    | TypeVarBinderS
        { loc :: Loc
        , varName :: XLocalName p
        , monomorphization :: Monomorphization
        , kind :: KindSyntax p
        }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

varNameInBinder :: ForallBinderS p -> XLocalName p
varNameInBinder = \case
    UnspecifiedBinderS{varName} -> varName
    TypeVarBinderS{varName} -> varName

type EffectSyntax = TypeSyntax

data Type
    = TypeConstructor Name
    | TypeApplication Type (Seq Type)
    | TypeVar LocalName
    | Forall (Seq (LocalName, Kind, Monomorphization)) Type
    | Function (Seq Type) Effect Type
    | Tuple (Seq Type)
    | MetaVar MetaVar
    | Skolem Skolem
    | Pure
    | -- Kinds
      Rep
    | Type Kind
    | Effect
    | SumRep (Seq Type)
    | ProductRep (Seq Type)
    | UnitRep
    | EmptyRep
    | BoxedRep
    | Kind
    deriving (Generic)

type Kind = Type

-- TODO: don't meta variables need kinds?
-- TODO: levels
data MetaVar = MkMetaVar
    { underlying :: IORef (Maybe Type)
    , identity :: Unique
    , name :: Text
    , monomorphization :: Monomorphization
    }

instance Eq MetaVar where
    meta1 == meta2 = meta1.identity == meta2.identity

data Skolem = MkSkolem
    { originalName :: LocalName
    , identity :: Unique
    , monomorphization :: Monomorphization
    }
    deriving (Generic)

instance Eq Skolem where
    skolem1 == skolem2 = skolem1.identity == skolem2.identity

type Effect = Type

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

instance Pretty Type where
    pretty = \case
        TypeConstructor name -> prettyName TypeConstructorKind name
        TypeApplication typeConstructor argTypes ->
            pretty typeConstructor <> prettyArguments argTypes
        TypeVar name -> prettyLocal VarKind name
        Forall binders body -> keyword "forall" <+> intercalateDoc " " (fmap prettyTypeVarBinder binders) <> "." <+> pretty body
        Function arguments Pure result ->
            prettyArguments arguments <+> keyword "->" <+> pretty result
        Function arguments effect result ->
            prettyArguments arguments <+> keyword "-{" <> pretty effect <> keyword "}>" <+> pretty result
        Tuple elements -> prettyArguments elements
        MetaVar meta -> pretty meta
        Skolem skolem -> pretty skolem
        Pure -> keyword "Pure"
        Rep -> keyword "Rep"
        Type rep -> keyword "Type" <> prettyArguments @[] [rep]
        Effect -> keyword "Effect"
        SumRep reps -> lparen "(" <> intercalateDoc (keyword "+") (fmap pretty reps) <> rparen ")"
        ProductRep reps -> lparen "(" <> intercalateDoc (keyword "*") (fmap pretty reps) <> rparen ")"
        UnitRep -> keyword "Unit"
        EmptyRep -> keyword "Empty"
        BoxedRep -> keyword "Boxed"
        Kind -> keyword "Kind"

prettyTypeVarBinder :: (LocalName, Kind, Monomorphization) -> Doc Ann
prettyTypeVarBinder (name, kind, monomorphization) = do
    let prefix = case monomorphization of
            Parametric -> mempty
            Monomorphized -> keyword "*"
    prefix <> lparen "(" <> prettyLocal VarKind name <+> keyword ":" <+> pretty kind <> ")"

instance Pretty MetaVar where
    pretty (MkMetaVar{identity, name}) = meta identity ("?" <> name)

instance Pretty Skolem where
    pretty (MkSkolem{identity, originalName}) = skolem identity (renderLocalName originalName)

prettyName :: NameKind -> Name -> Doc Ann
prettyName kind = \case
    Local name -> prettyLocal kind name
    Global name -> prettyGlobal kind name

prettyLocal :: NameKind -> LocalName -> Doc Ann
prettyLocal kind name = case kind of
    VarKind -> globalIdentText (renderLocalName name)
    TypeConstructorKind -> globalConstructorText (renderLocalName name)
    DataConstructorKind -> globalConstructorText (renderLocalName name)

prettyGlobal :: NameKind -> GlobalName -> Doc Ann
prettyGlobal kind MkGlobalName{moduleName, name} = prettyGlobalText kind (renderModuleName moduleName <> ":" <> name)

prettyGlobalText :: NameKind -> Text -> Doc Ann
prettyGlobalText kind raw = case kind of
    VarKind -> globalIdentText raw
    TypeConstructorKind -> globalConstructorText raw
    DataConstructorKind -> globalConstructorText raw

prettyArguments :: (Foldable list, Functor list, Pretty a) => list a -> Doc Ann
prettyArguments list = lparen "(" <> intercalateDoc (keyword ",") (fmap pretty list) <> rparen ")"

definedGlobals :: DeclarationSyntax p -> Seq (GlobalName, NameKind)
definedGlobals = \case
    DefineFunction{name} -> pure (name, VarKind)
    DefineVariantType{name, constructors} ->
        [(name, TypeConstructorKind)] <> fmap (\(_, name, _) -> (name, DataConstructorKind)) constructors

typeOfGlobal :: (HasCallStack) => GlobalName -> DeclarationSyntax Renamed -> TypeSyntax Renamed
typeOfGlobal global = \case
    DefineFunction{name, typeSignature}
        | name == global -> typeSignature
        | otherwise -> error $ "global (term) variable not found in function '" <> show name <> "': " <> show global
    DefineVariantType{name = variantName, typeParameters, constructors} ->
        case find (\(_, name, _) -> name == global) constructors of
            Nothing -> error $ "global (term) variable not found in variant definition '" <> show variantName <> ": " <> show global
            Just (loc, _, parameterTypes) -> do
                let boundVar = \case
                        -- TODO: kind applications??? ughhh maybe Type : Type would be better
                        _ -> undefined

                forallS
                    loc
                    typeParameters
                    (PureFunctionS loc parameterTypes (typeApplicationS loc (TypeConstructorS loc (Global variantName)) (fmap boundVar typeParameters)))

kindOfGlobal :: (HasCallStack) => Declaration Renamed -> KindSyntax Renamed
kindOfGlobal declaration = case declaration.syntax of
    DefineFunction{} -> error "trying to access 'kind' of a function"
    DefineVariantType{name = _, typeParameters, constructors = _} -> do
        let argumentKinds =
                typeParameters & fmap \case
                    _ -> undefined
        PureFunctionS declaration.loc argumentKinds (TypeS declaration.loc undefined)
