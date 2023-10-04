module Vega.Syntax (
  Pass (..),
  XName,
  -- Surface Syntax
  Declaration (..),
  Expr (..),
  Statement (..),
  Pattern (..),
  Literal (..),
  -- Core Syntax
  CoreDeclarationF (..),
  CoreExprF (..),
  CorePattern (..),
  -- Values
  ValueF (..),
  ClosureF (..),
  Skolem (..),
  MetaVarF (..),
  -- Reexports
  Loc,
  getLoc,
  Name,
) where

import Vega.Prelude

import Vega.Loc (HasLoc, Loc, getLoc)
import Vega.Name
import Vega.Pretty

import System.IO.Unsafe (unsafePerformIO)

data Pass = Parsed | Renamed

type family XName (p :: Pass) where
  XName Parsed = Text
  XName Renamed = Name

type SourceType = Expr

data Declaration (p :: Pass)
  = DefineFunction Loc (XName p) (SourceType p) (Vector (Pattern p)) (Expr p)
  deriving (Generic)
instance HasLoc (Declaration p)

data Expr (p :: Pass)
  = Var Loc (XName p)
  | App Loc (Expr p) (Expr p)
  | Lambda Loc (Pattern p) (Expr p)
  | Case Loc (Expr p) (Vector (Pattern p, Expr p))
  | Literal Loc Literal
  | TupleLiteral Loc (Vector (Expr p))
  | Sequence Loc (Vector (Statement p))
  | Ascription Loc (Expr p) (SourceType p)
  | -- Types
    EPi Loc (Maybe (XName p)) (Expr p) (Expr p)
  | EForall Loc (XName p) (Expr p) (Expr p)
  | ETupleType Loc (Vector (Expr p))
  deriving (Generic)
instance HasLoc (Expr p)

data Statement (p :: Pass)
  = Let Loc (Pattern p) (Expr p)
  | LetFunction Loc (XName p) (Maybe (SourceType p)) (Vector (Pattern p)) (Expr p)
  | RunExpr Loc (Expr p)
  deriving (Generic)
instance HasLoc (Statement p)

data Pattern (p :: Pass)
  = VarPat Loc (XName p)
  | IntPat Loc Integer
  | StringPat Loc Text
  | TuplePat Loc (Vector (Pattern p))
  | OrPat Loc (Pattern p) (Pattern p)
  deriving (Generic)
instance HasLoc (Pattern p)

data Literal
  = TypeLit
  | IntTypeLit
  | StringTypeLit
  | IntLit Integer
  | StringLit Text
  deriving (Generic)

data CoreDeclarationF context
  = CDefineFunction Name (Vector Name) (CoreExprF context)

-- TODO: Maybe this shouldn't be a separate core type but just another TTG pass.
-- Core cannot deviate that much from source syntax anyway since it needs to be shown in error messages
type CoreTypeF = CoreExprF
data CoreExprF context
  = CVar Name
  | CApp (CoreExprF context) (CoreExprF context)
  | -- Patterns are desugared in core
    CLambda Name (CoreExprF context)
  | CCase (CoreExprF context) (Vector (CorePattern, CoreExprF context))
  | CLiteral Literal
  | CTupleLiteral (Vector (CoreExprF context))
  | -- Statements are just desugared to let expressions
    CLet Name (CoreTypeF context) (CoreExprF context)
  | -- Types
    CPi (Maybe Name) (CoreTypeF context) (CoreExprF context)
  | CForall Name (CoreTypeF context) (CoreExprF context)
  | CMeta (MetaVarF context)
  | CTupleType (Vector (CoreExprF context))
  | CQuote (ValueF context)

data CorePattern
  = CVarPat Name
  | CIntPat Integer
  | CStringPat Text
  | CTuplePat (Vector Name)

data ValueF context
  = IntV Integer
  | StringV Text
  | ClosureV {-# UNPACK #-} (ClosureF context)
  | TupleV (Vector (ValueF context))
  | -- Types
    Type
  | Int
  | String
  | Tuple (Vector (ValueF context))
  | -- TODO: Add effects
    Pi (Maybe Name) (ValueF context) (CoreExprF context, context)
  | Forall Name (ValueF context) (CoreExprF context, context)
  | -- Stuck expressions
    SkolemApp Skolem (Seq (ValueF context))
  | MetaApp (MetaVarF context) (Seq (ValueF context))

data ClosureF context = MkClosure Name (CoreExprF context) context

data Skolem = MkSkolem Name Unique

-- Skolems only keep their names for debugging purposes. All comparisons
-- are performed on the unique.
instance Eq Skolem where
  (MkSkolem _ unique1) == (MkSkolem _ unique2) = unique1 == unique2

data MetaVarF context = MkMeta Name Unique (IORef (Maybe (ValueF context)))

-- TODO: Precedence :/
-- TODO: This should quote things before printing so that we don't need to rely on the context as weirdly
instance Pretty (ValueF context) where
  pretty = \case
    IntV v -> number v
    StringV str -> literal ("\"" <> str <> "\"")
    TupleV values -> lparen "(" <> intercalateMap (keyword ", ") pretty values <> rparen ")"
    ClosureV (MkClosure name core _context) ->
      keyword "\\" <> ident name <+> keyword "->" <+> pretty core
    Type -> constructorText "Type"
    Int -> constructorText "Int"
    String -> constructorText "String"
    Tuple values -> constructorText "Tuple" <> lparen "(" <> intercalateMap (keyword ", ") pretty values <> rparen ")"
    Pi Nothing domain (core, _context) ->
      lparen "(" <> pretty domain <+> keyword "->" <+> pretty core <> rparen ")"
    Pi (Just name) domain (core, _context) ->
      lparen "(" <> lparen "(" <> ident name <+> keyword ":" <+> pretty domain <> rparen ")" <+> keyword "->" <+> pretty core <> rparen ")"
    Forall name domain (core, _context) ->
      lparen "("
        <> keyword "forall"
        <> lparen "("
        <> ident name
        <+> ":"
        <+> pretty domain
        <> rparen ")"
        <> keyword "."
        <+> pretty core
        <> rparen ")"
    SkolemApp skolem [] ->
      pretty skolem
    SkolemApp skolem arguments ->
      lparen "(" <> pretty skolem <+> sep (map pretty (toList arguments)) <> rparen ")"
    MetaApp meta arguments ->
      prettyMetaApp meta arguments

-- TODO: Zap these correctly instead of using unsafePerformIO here

-- Using NOINLINE, just in case
prettyMetaApp :: MetaVarF context -> Seq (ValueF context) -> Doc Ann
prettyMetaApp (MkMeta name _ ref) arguments = unsafePerformIO do
  readIORef ref >>= \case
    Nothing ->
      case arguments of
        [] -> pure $ meta ("?" <> original name)
        arguments -> pure $ lparen "(" <> meta (original name) <+> sep (map pretty (toList arguments)) <> rparen ")"
    Just replacement -> pure $ prettyApp replacement arguments
{-# NOINLINE prettyMetaApp #-}

prettyApp :: ValueF context -> Seq (ValueF context) -> Doc Ann
prettyApp (MetaApp meta arguments) additionalArguments =
  prettyMetaApp meta (arguments <> additionalArguments)
prettyApp (SkolemApp skolem arguments) additionalArguments =
  lparen "(" <> pretty skolem <+> sep (map pretty (toList (arguments <> additionalArguments))) <> rparen ")"
prettyApp type_ arguments =
  case arguments of
    [] -> pretty type_
    arguments -> lparen "(" <> pretty type_ <+> sep (map pretty (toList arguments)) <> rparen ")"

instance Pretty Skolem where
  pretty (MkSkolem name _) = skolem name

-- TODO: PRECEDEEEENCE
instance Pretty (CoreExprF context) where
  pretty = \case
    CVar name -> ident name
    CApp funExpr argExpr ->
      lparen "(" <> pretty funExpr <+> pretty argExpr <> rparen ")"
    CLambda name result ->
      lparen "(" <> keyword "\\" <> ident name <+> keyword "->" <+> pretty result <> rparen ")"
    CCase{} -> undefined
    CTupleLiteral arguments -> lparen "(" <> intercalateMap ", " pretty arguments
    CLiteral literal -> pretty literal
    CLet name body rest ->
      lparen "(" <> keyword "let" <+> ident name <+> "=" <+> pretty body <> ";" <+> pretty rest <> rparen ")"
    CPi Nothing domain codomain ->
      lparen "(" <> pretty domain <+> keyword "->" <+> pretty codomain <> rparen ")"
    CPi (Just name) domain codomain ->
      lparen "(" <> lparen "(" <> ident name <+> keyword ":" <+> pretty domain <> rparen ")" <+> keyword "->" <+> pretty codomain <> rparen ")"
    CForall name domain codomain ->
      lparen "("
        <> keyword "forall"
        <> lparen "("
        <> ident name
        <+> keyword ":"
        <+> pretty domain
        <> rparen ")"
        <> keyword "."
        <+> pretty codomain
        <> rparen ")"
    CMeta meta -> prettyMetaApp meta []
    CTupleType arguments -> constructorText "Tuple" <> lparen "(" <> intercalateMap "," pretty arguments <> rparen ")"
    CQuote value_ -> pretty value_

instance Pretty Literal where
  pretty = \case
    TypeLit -> constructorText "Type"
    IntTypeLit -> constructorText "Int"
    StringTypeLit -> constructorText "String"
    IntLit int -> number int
    StringLit text -> literal ("\"" <> text <> "\"")
