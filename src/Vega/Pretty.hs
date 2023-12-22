{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Vega.Pretty (
    Ann,
    plain,
    identText,
    constructorText,
    skolemText,
    number,
    numberDoc,
    emphasis,
    errorDoc,
    quote,
    note,
    keyword,
    lparen,
    rparen,
    meta,
    literal,
    Pretty (..),
    PP.Doc,
    renderPlain,
    renderANSII,
    prettyPlain,
    prettyANSII,
    showPlain,
    intercalateDoc,
    -- Utility reexports
    (PP.<+>),
    PP.indent,
    PP.line,
    PP.align,
    -- Reexports with generalized types
    sep,
    vsep,
    cat,
    vcat,
) where

import Vega.Prelude

import Vega.Util (Untagged (..))

import Data.List ((!!))
import Prettyprinter (Doc)
import Prettyprinter qualified as PP
import Prettyprinter.Render.Util.SimpleDocTree qualified as PP

import GHC.Generics

data Ann
    = Ident
    | Constructor
    | Skolem
    | Number
    | Emphasis
    | Error
    | Quote
    | Note
    | Keyword
    | LParen
    | RParen
    | Meta

plain :: Text -> Doc Ann
plain = PP.pretty

identText :: Text -> Doc Ann
identText = PP.annotate Ident . PP.pretty

constructorText :: Text -> Doc Ann
constructorText = PP.annotate Constructor . PP.pretty

skolemText :: Text -> Doc Ann
skolemText = PP.annotate Skolem . PP.pretty

number :: (Num a, Show a) => a -> Doc Ann
number = PP.annotate Number . PP.pretty . show @Text

numberDoc :: Doc Ann -> Doc Ann
numberDoc = PP.annotate Number

emphasis :: Text -> Doc Ann
emphasis = PP.annotate Emphasis . PP.pretty

errorDoc :: Text -> Doc Ann
errorDoc = PP.annotate Error . PP.pretty

quote :: Doc Ann -> Doc Ann
quote = PP.annotate Quote

note :: Text -> Doc Ann
note = PP.annotate Note . PP.pretty

keyword :: Text -> Doc Ann
keyword = PP.annotate Keyword . PP.pretty

lparen :: Text -> Doc Ann
lparen = PP.annotate LParen . PP.pretty

rparen :: Text -> Doc Ann
rparen = PP.annotate RParen . PP.pretty

meta :: Text -> Doc Ann
meta = PP.annotate Meta . PP.pretty

literal :: Text -> Doc Ann
literal = PP.pretty

class Pretty a where
    pretty :: a -> Doc Ann

renderPlain :: PP.SimpleDocTree Ann -> Text
renderPlain = PP.renderSimplyDecorated id $ \ann x -> case ann of
    Ident -> x
    Constructor -> x
    Skolem -> x
    Number -> x
    Emphasis -> x
    Error -> x
    Quote -> "'" <> x <> "'"
    Note -> x
    Keyword -> x
    LParen -> x
    RParen -> x
    Meta -> x

renderANSII :: PP.SimpleDocTree Ann -> Text
renderANSII =
    flip evalState 0 . PP.renderSimplyDecoratedA @(State Int) pure \ann textA -> do
        text <- textA
        case ann of
            Ident -> pure $ "\ESC[38;5;159m\STX" <> text <> "\ESC[0m\STX"
            Constructor -> pure $ "\ESC[96m\STX" <> text <> "\ESC[0m\STX"
            Skolem -> pure $ "\ESC[93m\STX" <> text <> "\ESC[0m\STX"
            Number -> pure $ "\ESC[1m\ESC[93m\STX" <> text <> "\ESC[0m\STX"
            Emphasis -> pure $ "\ESC[1m\STX" <> text <> "\ESC[0m\STX"
            Error -> pure $ "\ESC[1m\ESC[31m\STX" <> text <> "\ESC[0m\STX"
            Note -> pure $ "\ESC[38;5;8m\STX" <> text <> "\ESC[0m\STX"
            Keyword -> pure $ "\ESC[94m\STX" <> text <> "\ESC[0m\STX"
            Quote -> pure text
            LParen -> do
                colorIndex <- state (\i -> (i, (i + 1) `mod` (length parenColors)))
                pure $ parenColors !! colorIndex <> text <> "\ESC[0m\STX"
            RParen -> do
                colorIndex <- state (\i -> ((i - 1) `mod` (length parenColors), (i - 1) `mod` (length parenColors)))
                pure $ parenColors !! colorIndex <> text <> "\ESC[0m\STX"
            Meta -> pure $ "\ESC[38;5;195m\STX" <> text <> "\ESC[0m\STX"
  where
    parenColors = ["\ESC[38;5;46m\STX", "\ESC[38;5;50m\STX", "\ESC[38;5;191m\STX"]

prettyPlain :: Doc Ann -> Text
prettyPlain doc = renderPlain (PP.treeForm (PP.layoutSmart PP.defaultLayoutOptions doc))

prettyANSII :: Doc Ann -> Text
prettyANSII doc = renderANSII (PP.treeForm (PP.layoutSmart PP.defaultLayoutOptions doc))

showPlain :: (Pretty a) => a -> Text
showPlain = prettyPlain . pretty

intercalateDoc :: (Foldable f) => Doc ann -> f (Doc ann) -> Doc ann
intercalateDoc separator foldable = case toList foldable of
    [] -> mempty
    (initial : rest) -> initial <> foldMap (\doc -> separator <> doc) rest

sep :: (Foldable t) => t (Doc ann) -> Doc ann
sep foldable = PP.sep (toList foldable)
vsep :: (Foldable t) => t (Doc ann) -> Doc ann
vsep foldable = PP.vsep (toList foldable)
cat :: (Foldable t) => t (Doc ann) -> Doc ann
cat foldable = PP.cat (toList foldable)
vcat :: (Foldable t) => t (Doc ann) -> Doc ann
vcat foldable = PP.vcat (toList foldable)

instance (Generic a, PrettyGenUntagged (Rep a)) => Pretty (Untagged a) where
    pretty (MkUntagged x) = prettyGenUntagged (from x)

class PrettyGenUntagged f where
    prettyGenUntagged :: f x -> Doc Ann

instance PrettyGenUntagged V1 where
    prettyGenUntagged = \case {}

instance (PrettyGenUntagged f, PrettyGenUntagged g) => PrettyGenUntagged (f :+: g) where
    prettyGenUntagged = \case
        L1 x -> prettyGenUntagged x
        R1 y -> prettyGenUntagged y

instance (Pretty c) => PrettyGenUntagged (K1 i c) where
    prettyGenUntagged (K1 x) = pretty x

instance (PrettyGenUntagged f) => PrettyGenUntagged (M1 i t f) where
    prettyGenUntagged (M1 x) = prettyGenUntagged x
