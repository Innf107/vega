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
  CoreDeclaration (..),
  CoreExpr (..),
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
  | Sequence Loc (Vector (Statement p))
  | Ascription Loc (Expr p) (SourceType p)
  | -- Types
    EPi Loc (Maybe (XName p)) (Expr p) (Expr p)
  | EForall Loc (XName p) (Expr p) (Expr p)
  deriving (Generic)
instance HasLoc (Expr p)

data Statement (p :: Pass)
  = Let Loc (XName p) (Maybe (SourceType p)) (Expr p)
  | LetFunction Loc (XName p) (Maybe (SourceType p)) (Vector (Pattern p)) (Expr p)
  | Perform Loc (Expr p)
  deriving (Generic)
instance HasLoc (Statement p)

data Pattern (p :: Pass)
  = VarPat Loc (XName p)
  | IntPat Loc Integer
  | StringPat Loc Text
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

data CoreDeclaration
  = CDefineFunction Name (Vector Name) CoreExpr

type CoreType = CoreExpr
data CoreExpr
  = CVar Name
  | CApp CoreExpr CoreExpr
  | -- Patterns are desugared in core
    CLambda Name CoreExpr
  | CCase CoreExpr (Vector (CorePattern, CoreExpr))
  | CLiteral Literal
  | -- Statements are just desugared to let expressions
    CLet Name CoreType CoreExpr
  | -- Types
    CPi (Maybe Name) CoreType CoreExpr
  | CForall Name CoreType CoreExpr

data CorePattern
  = CVarPat Name
  | CIntPat Integer
  | CStringPat Text

data ValueF context
  = IntV Integer
  | StringV Text
  | ClosureV {-# UNPACK #-} (ClosureF context)
  | -- Types
    Type
  | Int
  | String
  | -- TODO: Add effects
    Pi (Maybe Name) (ValueF context) (CoreExpr, context)
  | Forall Name (ValueF context) (CoreExpr, context)
  | -- Stuck expressions
    SkolemApp Skolem (Seq (ValueF context))
  | MetaApp (MetaVarF context) (Seq (ValueF context))

data ClosureF context = MkClosure Name CoreExpr context

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
    ClosureV (MkClosure name core _context) ->
      keyword "\\" <> ident name <+> keyword "->" <+> pretty core
    Type -> constructorText "Type"
    Int -> constructorText "Int"
    String -> constructorText "String"
    Pi Nothing domain (core, _context) ->
      lparen "(" <> pretty domain <+> "->" <+> pretty core <> rparen ")"
    Pi (Just name) domain (core, _context) ->
      lparen "(" <> lparen "(" <> ident name <+> keyword ":" <+> pretty domain <> rparen ")" <+> "->" <+> pretty core <> rparen ")"
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
        [] -> pure $ meta (original name)
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

instance Pretty CoreExpr where
  pretty = undefined