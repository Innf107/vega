{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Vega.Syntax where

import Data.Unique (Unique)
import Relude hiding (NonEmpty, State, Type, evalState, get, put)
import Vega.Loc (HasLoc, Loc)

import Data.Sequence (Seq (..))
import Data.Text qualified as Text
import Effectful (Eff, IOE, runEff, (:>))
import Effectful.State.Static.Local (State, evalState, get, put)
import GHC.Generics (Generically (..))
import System.IO.Unsafe (unsafePerformIO)
import Vega.Pretty (Ann, Doc, Pretty (..), globalConstructorText, globalIdentText, intercalateDoc, keyword, lparen, meta, rparen, skolem, (<+>))
import Vega.Seq.NonEmpty (NonEmpty (..))

newtype PackageName = MkPackageName Text
    deriving stock (Generic, Eq, Show)
    deriving newtype (Hashable)

renderPackageName :: PackageName -> Text
renderPackageName (MkPackageName name) = name

data ModuleName = MkModuleName
    { package :: PackageName
    , subModules :: NonEmpty Text
    }
    deriving stock (Generic, Eq, Show)
    deriving anyclass (Hashable)

data ParsedModuleName = MkParsedModuleName
    { package :: Maybe PackageName
    , subModules :: NonEmpty Text
    }

renderModuleName :: ModuleName -> Text
renderModuleName (MkModuleName{package, subModules}) =
    renderPackageName package <> ":" <> Text.intercalate "/" (toList subModules)

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

internalModuleName :: ModuleName
internalModuleName = MkModuleName{package = MkPackageName "internal", subModules = "Internal" :<|| []}

internalName :: Text -> GlobalName
internalName name = MkGlobalName{name, moduleName = internalModuleName}

isInternalName :: GlobalName -> Bool
isInternalName globalName = globalName.moduleName == internalModuleName

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
        , declaredTypeParameters :: Seq (Loc, XLocalName p)
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
        , varName :: XName p
        , typeArguments :: Seq (TypeSyntax p)
        }
    | Lambda
        { loc :: Loc
        , boundTypeParameters :: Seq (Loc, XLocalName p)
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
        , moduleName :: ParsedModuleName
        , importedDeclarations :: Seq Text
        }
    | ImportQualified
        { loc :: Loc
        , moduleName :: ParsedModuleName
        , importedAs :: Text
        }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data TypeSyntax p
    = TypeConstructorS Loc (XName p)
    | TypeApplicationS Loc (TypeSyntax p) (Seq (TypeSyntax p))
    | TypeVarS Loc (XLocalName p)
    | ForallS Loc (NonEmpty (ForallBinderS p)) (TypeSyntax p)
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
    | IntRepS Loc
    | KindS Loc
    deriving stock (Generic)
    deriving anyclass (HasLoc)

type KindSyntax = TypeSyntax

typeApplicationS :: Loc -> TypeSyntax p -> Seq (TypeSyntax p) -> TypeSyntax p
typeApplicationS _ constructor Empty = constructor
typeApplicationS loc constructor arguments = TypeApplicationS loc constructor arguments

forallS :: Loc -> Seq (ForallBinderS p) -> TypeSyntax p -> TypeSyntax p
forallS _loc Empty result = result
forallS loc (x :<| xs) result = ForallS loc (x :<|| xs) result

forall_ :: Seq ForallBinder -> Type -> Type
forall_ Empty result = result
forall_ (x :<| xs) result = Forall (x :<|| xs) result

data Monomorphization
    = Monomorphized
    | Parametric
    deriving (Generic, Show, Eq)

data BinderVisibility
    = Visible
    | Inferred
    deriving (Generic, Show, Eq)

data ForallBinderS p
    = UnspecifiedBinderS
        { loc :: Loc
        , varName :: XLocalName p
        , monomorphization :: Monomorphization
        }
    | TypeVarBinderS
        { loc :: Loc
        , varName :: XLocalName p
        , monomorphization :: Monomorphization
        , kind :: KindSyntax p
        , visibility :: BinderVisibility
        }
    deriving stock (Generic)
    deriving anyclass (HasLoc)

data ForallBinder = MkForallBinder
    { varName :: LocalName
    , visibility :: BinderVisibility
    , kind :: Kind
    , monomorphization :: Monomorphization
    }
    deriving stock (Generic)

type EffectSyntax = TypeSyntax

data Type
    = TypeConstructor Name
    | TypeApplication Type (Seq Type)
    | TypeVar LocalName
    | Forall (NonEmpty ForallBinder) Type
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
    | IntRep
    | Kind
    deriving (Generic)

type Kind = Type

-- TODO: levels
data MetaVar = MkMetaVar
    { underlying :: IORef (Maybe Type)
    , identity :: Unique
    , name :: Text
    , kind :: Kind
    }

followMetas :: (IOE :> es) => Type -> Eff es Type
followMetas = \case
    type_@(MetaVar meta) -> do
        readIORef meta.underlying >>= \case
            Nothing -> pure type_
            Just substitution -> do
                actualType <- followMetas substitution
                -- path compression
                writeIORef meta.underlying (Just actualType)

                pure actualType
    type_ -> pure type_

instance Eq MetaVar where
    meta1 == meta2 = meta1.identity == meta2.identity

data Skolem = MkSkolem
    { originalName :: LocalName
    , identity :: Unique
    , monomorphization :: Monomorphization
    , kind :: Kind
    }
    deriving (Generic)

instance Eq Skolem where
    skolem1 == skolem2 = skolem1.identity == skolem2.identity

type Effect = Type

newtype ImportScope
    = MkImportScope
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
        Forall binders body -> keyword "forall" <+> intercalateDoc " " (fmap prettyForallBinder binders) <> "." <+> pretty body
        Function arguments Pure result ->
            prettyArguments arguments <+> keyword "->" <+> pretty result
        Function arguments effect result ->
            prettyArguments arguments <+> keyword "-{" <> pretty effect <> keyword "}>" <+> pretty result
        Tuple elements -> prettyArguments elements
        MetaVar meta ->
            -- The use of unsafePerformIO here is pretty benign since we only use it to
            -- read from a mutable reference
            case unsafePerformIO (runEff (followMetas (MetaVar meta))) of
                MetaVar meta -> pretty meta
                type_ -> pretty type_
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
        IntRep -> keyword "IntRep"
        Kind -> keyword "Kind"

prettyForallBinder :: ForallBinder -> Doc Ann
prettyForallBinder MkForallBinder{varName, kind, monomorphization, visibility} = do
    let (left, right) = case visibility of
            Visible -> (lparen "(", rparen ")")
            Inferred -> (lparen "{", rparen "}")
    let prefix = case monomorphization of
            Parametric -> mempty
            Monomorphized -> keyword "*"
    prefix <> left <> prettyLocal VarKind varName <+> keyword ":" <+> pretty kind <> right

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
prettyArguments list = lparen "(" <> intercalateDoc (keyword "," <> " ") (fmap pretty list) <> rparen ")"

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
                        UnspecifiedBinderS{loc, varName} -> TypeVarS loc varName
                        TypeVarBinderS{loc, varName} -> TypeVarS loc varName

                let appliedType = typeApplicationS loc (TypeConstructorS loc (Global variantName)) (fmap boundVar typeParameters)
                case parameterTypes of
                    Empty -> forallS loc typeParameters $ appliedType
                    _ -> forallS loc typeParameters $ PureFunctionS loc parameterTypes appliedType
