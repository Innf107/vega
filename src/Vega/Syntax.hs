{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Vega.Syntax where

import Data.Unique (Unique)
import Relude hiding (NonEmpty, State, Type, evalState, get, put)
import Vega.Loc (HasLoc, Loc)

import Data.HashMap.Strict qualified as HashMap
import Data.Sequence (Seq (..))
import Data.Text qualified as Text
import Effectful (Eff, IOE, runEff, (:>))
import GHC.Generics (Generically (..))
import System.IO.Unsafe (unsafePerformIO)
import Vega.Pretty (Ann, Doc, Pretty (..), globalConstructorText, globalIdentText, intercalateDoc, keyword, lparen, meta, rparen, skolem, (<+>))
import Vega.Seq.NonEmpty (NonEmpty (..))

newtype PackageName = MkPackageName Text
    deriving stock (Generic, Eq, Show, Ord)
    deriving newtype (Hashable)

renderPackageName :: PackageName -> Text
renderPackageName (MkPackageName name) = name

data ModuleName = MkModuleName
    { package :: PackageName
    , subModules :: NonEmpty Text
    }
    deriving stock (Generic, Eq, Show, Ord)
    deriving anyclass (Hashable)

data ParsedModuleName = MkParsedModuleName
    { package :: Maybe PackageName
    , subModules :: NonEmpty Text
    }

renderModuleName :: ModuleName -> Text
renderModuleName (MkModuleName{package, subModules}) =
    renderPackageName package <> ":" <> Text.intercalate "/" (toList subModules)

data DeclarationName = MkDeclarationName {moduleName :: ModuleName, name :: Text}
    deriving stock (Generic, Eq, Show, Ord)
    deriving anyclass (Hashable)

instance Pretty DeclarationName where
    pretty (MkDeclarationName{moduleName, name}) = globalIdentText (renderModuleName moduleName <> ":" <> name)

data GlobalName = MkGlobalName {moduleName :: ModuleName, name :: Text}
    deriving stock (Generic, Eq, Show, Ord)
    deriving anyclass (Hashable)

data LocalName = MkLocalName {parent :: DeclarationName, name :: Text, count :: Int}
    deriving stock (Generic, Eq, Show, Ord)
    deriving anyclass (Hashable)

renderLocalName :: LocalName -> Text
renderLocalName MkLocalName{parent = _, name, count} = case count of
    0 -> name
    _ -> name <> "@" <> show count

data Name
    = Global GlobalName
    | Local LocalName
    deriving stock (Generic, Eq, Show, Ord)
    deriving anyclass (Hashable)

unqualifiedName :: Name -> Text
unqualifiedName = \case
    Global global -> global.name
    Local local -> local.name

internalModuleName :: ModuleName
internalModuleName = MkModuleName{package = MkPackageName "internal", subModules = "Internal" :<|| []}

internalDeclarationName :: DeclarationName
internalDeclarationName = MkDeclarationName{moduleName = internalModuleName, name = "internal"}

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
    deriving stock (Generic, Eq, Show)
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
        { ext :: XDefineFunction p
        , name :: GlobalName
        , typeSignature :: TypeSyntax p
        , declaredTypeParameters :: Seq (Loc, XLocalName p)
        , parameters :: Seq (Pattern p, XParameterRepresentation p)
        , body :: Expr p
        }
    | DefineVariantType
        { name :: GlobalName
        , typeParameters :: Seq (ForallBinderS p)
        , constructors :: Seq (Loc, GlobalName, Seq (TypeSyntax p))
        }
    | DefineExternalFunction
        { name :: GlobalName
        , type_ :: TypeSyntax p
        }
    deriving stock (Generic)

type family XDefineFunction p where
    XDefineFunction Parsed = ()
    XDefineFunction Renamed = ()
    XDefineFunction Typed = DefineFunctionTypedExt

data DefineFunctionTypedExt = MkDefineFunctionTypedExt
    { returnRepresentation :: Kind
    }

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
        , ext :: XLetFunction p
        , name :: XLocalName p
        , typeSignature :: Maybe (TypeSyntax p)
        , parameters :: Seq (Pattern p, XParameterRepresentation p)
        , body :: Expr p
        }
    | Use Loc (Pattern p) (Expr p)
    deriving stock (Generic)
    deriving anyclass (HasLoc)

type family XLetFunction p where
    XLetFunction Parsed = ()
    XLetFunction Renamed = ()
    XLetFunction Typed = LetFunctionTypedExt

data LetFunctionTypedExt = MkLetFunctionTypedExt
    { returnRepresentation :: Kind
    }

type family XParameterRepresentation p where
    XParameterRepresentation Parsed = ()
    XParameterRepresentation Renamed = ()
    XParameterRepresentation Typed = Type

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
    | VarPattern Loc (XVarPattern p) (XLocalName p)
    | AsPattern Loc (XAsPattern p) (Pattern p) (XLocalName p)
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
    | OrPattern Loc (NonEmpty (Pattern p))
    deriving stock (Generic)
    deriving anyclass (HasLoc)

type family XVarPattern p where
    XVarPattern Parsed = ()
    XVarPattern Renamed = ()
    XVarPattern Typed = Type -- Representation

type family XAsPattern p where
    XAsPattern Parsed = ()
    XAsPattern Renamed = ()
    XAsPattern Typed = Type -- Representation

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
    | ExistsS Loc (NonEmpty (XLocalName p, KindSyntax p)) (TypeSyntax p)
    | TypeFunctionS Loc (Seq (TypeSyntax p)) (TypeSyntax p)
    | PureFunctionS Loc (Seq (TypeSyntax p)) (TypeSyntax p)
    | FunctionS Loc (Seq (TypeSyntax p)) (EffectSyntax p) (TypeSyntax p)
    | TupleS Loc (Seq (TypeSyntax p))
    | -- Kinds
      RepS Loc
    | TypeS Loc (KindSyntax p)
    | EffectS Loc
    | SumRepS Loc (Seq (TypeSyntax p))
    | ProductRepS Loc (Seq (TypeSyntax p))
    | ArrayRepS Loc (TypeSyntax p)
    | PrimitiveRepS Loc PrimitiveRep
    | KindS Loc
    deriving stock (Generic)
    deriving anyclass (HasLoc)

deriving instance (Eq (XName p), Eq (XLocalName p)) => Eq (TypeSyntax p)
deriving instance (Ord (XName p), Ord (XLocalName p)) => Ord (TypeSyntax p)

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
    deriving (Generic, Show, Eq, Ord)

data BinderVisibility
    = Visible
    | Inferred
    deriving (Generic, Show, Eq, Ord)

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

deriving instance (Eq (XName p), Eq (XLocalName p)) => Eq (ForallBinderS p)
deriving instance (Ord (XName p), Ord (XLocalName p)) => Ord (ForallBinderS p)

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
    | Exists (NonEmpty (LocalName, Kind)) Type
    | Function (Seq Type) Effect Type
    | TypeFunction (Seq Type) Type
    | Tuple (Seq Type)
    | MetaVar MetaVar
    | Skolem Skolem
    | Pure
    | -- Kinds
      Rep
    | Type Kind
    | Effect
    | Kind
    | -- Representations
      SumRep (Seq Type)
    | ProductRep (Seq Type)
    | ArrayRep Type -- TODO: this should really be an AbstractRep (just like the primitiveReps)
    | PrimitiveRep PrimitiveRep
    deriving (Generic)

-- TODO: Why do we have UnitRep and EmptyRep here? Shouldn't they just be `ProductRep []` and `SumRep []`?
data PrimitiveRep
    = UnitRep
    | EmptyRep
    | BoxedRep
    | IntRep
    | DoubleRep
    deriving (Generic, Eq, Ord)

instance Pretty PrimitiveRep where
    pretty = \case
        UnitRep -> keyword "Unit"
        EmptyRep -> keyword "Empty"
        BoxedRep -> keyword "Boxed"
        IntRep -> keyword "IntRep"
        DoubleRep -> keyword "DoubleRep"

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
    deriving stock (Show, Eq, Generic)

instance Semigroup ImportScope where
    scope1 <> scope2 = MkImportScope{imports = HashMap.unionWith (<>) scope1.imports scope2.imports}
instance Monoid ImportScope where
    mempty = MkImportScope mempty

-- TODO: if we use a hash map here this is actually quite inefficient
data ImportedItems = MkImportedItems
    { qualifiedAliases :: HashSet Text
    , unqualifiedItems :: HashSet Text
    }
    deriving (Show, Eq, Generic)
    deriving (Semigroup, Monoid) via Generically ImportedItems

instance Pretty Type where
    pretty = \case
        TypeConstructor name -> prettyName TypeConstructorKind name
        TypeApplication typeConstructor argTypes ->
            pretty typeConstructor <> prettyArguments argTypes
        TypeVar name -> prettyLocal VarKind name
        Forall binders body -> keyword "forall" <+> intercalateDoc " " (fmap prettyForallBinder binders) <> keyword "." <+> pretty body
        Exists binders body ->
            keyword "exists"
                <+> intercalateDoc " " (fmap (\(name, kind) -> lparen "(" <> prettyLocal VarKind name <+> keyword ":" <+> pretty kind <> rparen ")") binders)
                <> keyword "." <+> pretty body
        TypeFunction arguments result ->
            prettyArguments arguments <+> keyword ":->" <+> pretty result
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
        SumRep reps -> lparen "(" <> intercalateDoc (" " <> keyword "+" <> " ") (fmap pretty reps) <> rparen ")"
        ProductRep reps -> lparen "(" <> intercalateDoc (" " <> keyword "*" <> " ") (fmap pretty reps) <> rparen ")"
        ArrayRep inner -> keyword "ArrayRep" <> lparen "(" <> pretty inner <> rparen ")"
        PrimitiveRep rep -> pretty rep
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
    pretty (MkSkolem{identity, originalName}) = skolem identity originalName.name

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
    DefineExternalFunction{name} -> pure (name, VarKind)

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
    DefineExternalFunction{name, type_}
        | name == global -> type_
        | otherwise -> error $ "global (term) variable not found in external function '" <> show name <> "': " <> show global

-- | The representation of strings (and in particular string literals)
stringRepresentation :: Type
stringRepresentation = PrimitiveRep BoxedRep

-- The representation of functions. This *will* probably change in the future so code
-- should treat it abstractly instead of depending on its concrete value
functionRepresentation :: Type
functionRepresentation = PrimitiveRep BoxedRep

{- NOTE: Ord instances
-----------------------------------------------------
Nearly all derived `Ord` instances in this module are entirely meaningless.
We only need to derive them because megaparsec stores its custom parse errors
in a `Set` and we sometimes need to store AST nodes to improve our error messages
(e.g. InvalidExistentialBinder contains the ForallBinderS value the user actually wrote)
-}
