{-# LANGUAGE AllowAmbiguousTypes #-}

module Vega.Syntax (
    Pass (..),
    XName,
    -- Surface Syntax
    Declaration (..),
    Expr (..),
    SourceType,
    Statement (..),
    Pattern (..),
    Literal (..),
    Primop (..),
    -- Core Syntax
    CoreDeclarationF (..),
    CoreExprF (..),
    CorePattern (..),
    EvalClosureForPrinting (..),
    -- Values
    ValueF (..),
    StuckCont (..),
    ClosureF (..),
    Skolem (..),
    MetaVarF (..),
    -- Reexports
    Loc,
    getLoc,
    Name,
) where

import Vega.Prelude

import Vega.Debug
import Vega.Loc (HasLoc, Loc, getLoc)
import Vega.Name as Name
import Vega.Pretty
import Vega.Util

import System.IO.Unsafe (unsafePerformIO)

data Pass = Parsed | Renamed

type family XName (p :: Pass) where
    XName Parsed = Text
    XName Renamed = Name

type SourceType = Expr

data Declaration (p :: Pass)
    = DefineFunction Loc (XName p) (SourceType p) (Vector (Pattern p)) (Expr p)
    | DefineGADT Loc (XName p) (SourceType p) (Vector (XName p, SourceType p))
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
    | Primop Loc Primop
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
    | ConstructorPat Loc (XName p) (Vector (Pattern p))
    | IntPat Loc Integer
    | StringPat Loc Text
    | TuplePat Loc (Vector (Pattern p))
    | OrPat Loc (Pattern p) (Pattern p)
    | TypePat Loc (Pattern p) (SourceType p)
    deriving (Generic)
instance HasLoc (Pattern p)

data Literal
    = TypeLit
    | IntTypeLit
    | StringTypeLit
    | IntLit Integer
    | StringLit Text
    deriving (Generic, Typeable)

data Primop
    = Debug
    | Add
    | Subtract
    | Multiply
    | IntDivide
    deriving (Generic, Show, Eq, Ord)

data CoreDeclarationF context
    = CDefineVar Name (ValueF context)
    | CDefineGADT Name (Vector (Name, Int))

-- TODO: Maybe this shouldn't be a separate core type but just another TTG pass.
-- Core cannot deviate that much from source syntax anyway since it needs to be shown in error messages
type CoreTypeF = CoreExprF
data CoreExprF context
    = CVar Name
    | CApp (CoreExprF context) (CoreExprF context)
    | -- Patterns are desugared in core
      CLambda Name (CoreExprF context)
    | CCase (CoreExprF context) (Vector (CorePattern Name, CoreExprF context))
    | CLiteral Literal
    | CTupleLiteral (Vector (CoreExprF context))
    | -- Statements are just desugared to let expressions
      CLet Name (CoreTypeF context) (CoreExprF context)
    | CPrimop Primop
    | -- Types
      CPi (Maybe Name) (CoreTypeF context) (CoreExprF context)
    | CForall Name (CoreTypeF context) (CoreExprF context)
    | CMeta (MetaVarF context)
    | CTupleType (Vector (CoreExprF context))
    | CQuote (ValueF context)
    deriving (Generic)

data CorePattern subPattern
    = CVarPat Name
    | CWildcardPat
    | CIntPat Integer
    | CStringPat Text
    | CTuplePat (Vector subPattern)
    | CConstructorPat Name (Vector subPattern)
    deriving (Generic)

data ValueF context
    = IntV Integer
    | StringV Text
    | ClosureV (ClosureF context)
    | TupleV (Vector (ValueF context))
    | -- Types
      Type
    | Int
    | String
    | TupleType (Vector (ValueF context))
    | TypeConstructorApp Name (Seq (ValueF context)) -- TODO: is this type/data constructor distinction even meaningful here?
    | DataConstructorApp Name (Seq (ValueF context))
    | -- TODO: Add effects
      Pi (Maybe Name) (ValueF context) (CoreExprF context, context)
    | Forall Name (ValueF context) (CoreExprF context, context)
    | StuckSkolem Skolem (Seq (StuckCont context))
    | StuckMeta (MetaVarF context) (Seq (StuckCont context))
    deriving (Generic)

data StuckCont context
    = StuckApp (ValueF context)
    | StuckCase context (Vector (CorePattern Name, CoreExprF context))

data ClosureF context
    = MkClosure Name (CoreExprF context) context
    | PrimopClosure Primop (Seq (ValueF context))

data Skolem = MkSkolem Name Unique

-- Skolems only keep their names for debugging purposes. All comparisons
-- are performed on the unique.
instance Eq Skolem where
    (MkSkolem _ unique1) == (MkSkolem _ unique2) = unique1 == unique2
instance Ord Skolem where
    (MkSkolem _ unique1) `compare` (MkSkolem _ unique2) = unique1 `compare` unique2

data MetaVarF context = MkMeta Name Unique (IORef (Maybe (ValueF context)))

instance Eq (MetaVarF context) where
    MkMeta _ unique1 _ == MkMeta _ unique2 _ = unique1 == unique2

-- TODO: Precedence :/
-- TODO: This should quote things before printing so that we don't need to rely on the context as weirdly
instance (EvalClosureForPrinting context) => Pretty (ValueF context) where
    pretty :: ValueF context -> Doc Ann
    pretty = \case
        IntV v -> number v
        StringV str -> literal ("\"" <> str <> "\"")
        TupleV values -> lparen "(" <> intercalateMap (keyword ", ") pretty values <> rparen ")"
        ClosureV (MkClosure name core _context) ->
            keyword "\\" <> ident name <+> keyword "->" <+> pretty core
        ClosureV (PrimopClosure primop arguments) ->
            pretty primop <> lparen "(" <> intercalateDoc (keyword ", ") (fmap pretty arguments) <> rparen ")"
        Type -> constructorText "Type"
        Int -> constructorText "Int"
        String -> constructorText "String"
        TupleType [] -> keyword "Unit"
        DataConstructorApp name [] -> constructor name
        DataConstructorApp name args -> lparen "(" <> constructor name <+> sep (fmap pretty args) <> rparen ")"
        TypeConstructorApp name [] -> constructor name
        TypeConstructorApp name args -> lparen "(" <> constructor name <+> sep (fmap pretty args) <> rparen ")"
        TupleType values -> lparen "(" <> intercalateMap (keyword " ** ") pretty values <> rparen ")"
        Pi Nothing domain (core, context) -> do
            let codomain = unsafePerformIO (applyNullaryClosurePrint context core)
            lparen "(" <> pretty domain <+> keyword "->" <+> pretty codomain <> rparen ")"
        Pi (Just name) domain (core, context) -> do
            let codomain = unsafePerformIO (applyClosureForPrinting context core name)
            lparen "(" <> lparen "(" <> ident name <+> keyword ":" <+> pretty domain <> rparen ")" <+> keyword "->" <+> pretty codomain <> rparen ")"
        Forall name domain (core, context) -> do
            let codomain = unsafePerformIO (applyClosureForPrinting context core name)
            lparen "("
                <> keyword "forall"
                <> lparen "("
                <> ident name
                <+> ":"
                <+> pretty domain
                <> rparen ")"
                <> keyword "."
                <+> pretty codomain
                <> rparen ")"
        StuckSkolem skolem cont ->
            prettyStuckCont (pretty skolem) cont
        StuckMeta meta cont ->
            prettyStuckCont (prettyMeta meta) cont

class EvalClosureForPrinting context where
    applyNullaryClosurePrint :: context -> CoreExprF context -> IO (ValueF context)
    applyClosureForPrinting :: context -> CoreExprF context -> Name -> IO (ValueF context)

prettyStuckCont :: EvalClosureForPrinting context => Doc Ann -> Seq (StuckCont context) -> Doc Ann
prettyStuckCont target Empty = target
prettyStuckCont target (StuckApp argument :<| rest) = do
    prettyStuckCont (lparen "(" <> target <+> pretty argument <> ")") rest
prettyStuckCont target (StuckCase closureContext cases :<| rest) =
    prettyStuckCont (keyword "case" <+> target <+> lparen "{" <> "TODO" <> rparen "}") rest

-- TODO: Zonk these correctly instead of using unsafePerformIO here

-- Using NOINLINE, just in case
prettyMeta :: (EvalClosureForPrinting context) => MetaVarF context -> Doc Ann
prettyMeta (MkMeta name unique ref) = unsafePerformIO do
    readIORef ref >>= \case
        Nothing -> pure $ meta unique ("?" <> original name)
        Just replacement -> pure $ pretty replacement
{-# NOINLINE prettyMeta #-}

instance Pretty Skolem where
    pretty (MkSkolem name unique) =
        withUnique unique $ skolem unique name

instance (EvalClosureForPrinting context) => Pretty (CoreDeclarationF context) where
    pretty = \case
        CDefineVar name body -> ident name <+> keyword "=" <+> pretty body
        CDefineGADT _ _ -> "<<DEFINE GADT>>"

-- TODO: PRECEDEEEENCE
instance (EvalClosureForPrinting context) => Pretty (CoreExprF context) where
    pretty :: (EvalClosureForPrinting context) => CoreExprF context -> Doc Ann
    pretty = \case
        CVar name -> ident name
        CApp funExpr argExpr ->
            lparen "(" <> pretty funExpr <+> pretty argExpr <> rparen ")"
        CLambda name result ->
            lparen "(" <> keyword "\\" <> ident name <+> keyword "->" <+> pretty result <> rparen ")"
        CCase scrutinee cases ->
            keyword "case"
                <+> pretty scrutinee
                <+> keyword "of"
                <> indent
                    2
                    ( align
                        $ "\n"
                        <> vsep
                            ( fmap
                                ( \(pattern_, expr) ->
                                    pretty (coerce pattern_ :: CorePattern PrettyIdent)
                                        <+> keyword "->"
                                        <+> pretty expr
                                )
                                cases
                            )
                    )
        CTupleLiteral arguments -> lparen "(" <> intercalateMap (keyword ", ") pretty arguments <> rparen ")"
        CLiteral literal -> pretty literal
        CLet name body rest ->
            lparen "(" <> keyword "let" <+> ident name <+> keyword "=" <+> pretty body <> keyword ";" <+> pretty rest <> rparen ")"
        CPi Nothing domain codomain ->
            lparen "(" <> pretty domain <+> keyword "->" <+> pretty codomain <> rparen ")"
        CPi (Just name) domain codomain ->
            lparen "(" <> lparen "(" <> ident name <+> keyword ":" <+> pretty domain <> rparen ")" <+> keyword "->" <+> pretty codomain <> rparen ")"
        CPrimop primop -> pretty primop
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
        CMeta meta -> prettyMeta meta
        CTupleType [] -> keyword "Unit"
        CTupleType arguments -> lparen "(" <> intercalateMap (keyword " ** ") pretty arguments <> rparen ")"
        CQuote value_ -> pretty value_

instance (Pretty subPattern) => Pretty (CorePattern subPattern) where
    pretty = \case
        CVarPat name -> ident name
        CWildcardPat -> keyword "_"
        CIntPat n -> number n
        CStringPat text -> literal ("\"" <> text <> "\"")
        CTuplePat subPatterns -> lparen "(" <> intercalateMap (keyword ", ") pretty subPatterns <> rparen ")"
        CConstructorPat name subPatterns -> lparen "(" <> constructor name <+> sep (fmap pretty subPatterns) <> rparen ")"

instance Pretty Literal where
    pretty = \case
        TypeLit -> constructorText "Type"
        IntTypeLit -> constructorText "Int"
        StringTypeLit -> constructorText "String"
        IntLit int -> number int
        StringLit text -> literal ("\"" <> text <> "\"")

instance HeadConstructorArg Literal where
    headConstructorArg = pretty

instance Pretty Primop where
    pretty primop = identText $ case primop of
        Debug -> "debug"
        Add -> "(+)"
        Subtract -> "(-)"
        Multiply -> "(*)"
        IntDivide -> "(//)"

instance (HeadConstructorOverrides p) => HeadConstructorArg (Expr p) where
    headConstructorArg (Var _ name) = headConstructorArg name
    headConstructorArg (Literal _ literal) = headConstructorArg literal
    headConstructorArg app@App{} = showHeadConstructor app
    headConstructorArg pi@EPi{} = showHeadConstructor pi
    headConstructorArg forall_@EForall{} = showHeadConstructor forall_
    headConstructorArg _ = defaultHeadConstructorArg

type HeadConstructorOverrides p = AllConstraints HeadConstructorArg '[XName p, Expr p]
