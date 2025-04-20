{-# LANGUAGE UndecidableInstances #-}
-- We include a Num constraint on 'number' to prevent mistakes so -Wredundant-constraints doesn't make sense here
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Vega.Pretty (
    Ann,
    plain,
    identText,
    identTextWith,
    constructorText,
    constructorTextWith,
    skolemText,
    skolemTextWith,
    number,
    numberDoc,
    emphasis,
    errorDoc,
    warning,
    quote,
    note,
    keyword,
    withUnique,
    lparen,
    rparen,
    meta,
    literal,
    Pretty (..),
    PP.Doc,
    renderPlain,
    PrettyANSIIConfig (..),
    defaultPrettyANSIIConfig,
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

import Relude

import Vega.Disambiguate (disambiguate)
import Vega.Disambiguate qualified as Disambiguate
import Vega.Util (Untagged (..))

import Prettyprinter (Doc)
import Prettyprinter qualified as PP
import Prettyprinter.Render.Util.SimpleDocTree qualified as PP

import Control.Monad.ST.Strict (runST)
import Data.Unique (Unique, hashUnique, newUnique)
import Data.Vector ((!))
import GHC.Generics
import System.IO.Unsafe (unsafePerformIO)

data Ann
    = Ident Text Unique
    | Constructor Text Unique
    | Skolem Text Unique
    | Number
    | Literal
    | Emphasis
    | Error
    | Warning
    | Quote
    | Note
    | Keyword
    | LParen
    | RParen
    | Meta Text Unique
    | Unique Unique

plain :: Text -> Doc Ann
plain = PP.pretty

{-# NOINLINE textUnique #-}
textUnique :: Unique
textUnique = unsafePerformIO newUnique

identTextWith :: Unique -> Text -> Doc Ann
identTextWith unique name = PP.annotate (Ident name unique) (PP.pretty name)

identText :: Text -> Doc Ann
identText = identTextWith textUnique

constructorTextWith :: Unique -> Text -> Doc Ann
constructorTextWith unique name = PP.annotate (Constructor name unique) (PP.pretty name)

constructorText :: Text -> Doc Ann
constructorText = constructorTextWith textUnique

skolemTextWith :: Unique -> Text -> Doc Ann
skolemTextWith unique name = PP.annotate (Skolem name unique) (PP.pretty name)

skolemText :: Text -> Doc Ann
skolemText = skolemTextWith textUnique

number :: (Num a, Show a) => a -> Doc Ann
number = PP.annotate Number . PP.pretty . show @Text

numberDoc :: Doc Ann -> Doc Ann
numberDoc = PP.annotate Number

emphasis :: Text -> Doc Ann
emphasis = PP.annotate Emphasis . PP.pretty

errorDoc :: Text -> Doc Ann
errorDoc = PP.annotate Error . PP.pretty

warning :: Text -> Doc Ann
warning = PP.annotate Warning . PP.pretty

quote :: Doc Ann -> Doc Ann
quote = PP.annotate Quote

note :: Text -> Doc Ann
note = PP.annotate Note . PP.pretty

keyword :: Text -> Doc Ann
keyword = PP.annotate Keyword . PP.pretty

withUnique :: Unique -> Doc Ann -> Doc Ann
withUnique unique doc = PP.annotate (Unique unique) doc

lparen :: Text -> Doc Ann
lparen = PP.annotate LParen . PP.pretty

rparen :: Text -> Doc Ann
rparen = PP.annotate RParen . PP.pretty

meta :: Unique -> Text -> Doc Ann
meta unique name = PP.annotate (Meta name unique) (PP.pretty name)

literal :: Text -> Doc Ann
literal = PP.annotate Literal . PP.pretty

class Pretty a where
    pretty :: a -> Doc Ann

renderPlain :: PP.SimpleDocTree Ann -> Text
renderPlain tree = runST do
    idents <- Disambiguate.new
    constructors <- Disambiguate.new
    skolems <- Disambiguate.new
    metas <- Disambiguate.new
    tree & PP.renderSimplyDecoratedA pure \ann textA -> do
        text <- textA
        case ann of
            Ident name unique -> disambiguate idents name unique
            Constructor name unique -> disambiguate constructors name unique
            Skolem name unique -> disambiguate skolems name unique
            Number -> pure text
            Literal -> pure text
            Emphasis -> pure text
            Error -> pure text
            Warning -> pure text
            Quote -> pure $ "'" <> text <> "'"
            Note -> pure text
            Keyword -> pure text
            LParen -> pure text
            RParen -> pure text
            Meta name unique -> disambiguate metas name unique
            Unique _ -> pure text

data PrettyANSIIConfig = MkPrettyANSIIConfig
    { includeUnique :: Bool
    }
defaultPrettyANSIIConfig :: PrettyANSIIConfig
defaultPrettyANSIIConfig =
    MkPrettyANSIIConfig
        { includeUnique = False
        }

renderANSII :: (?config :: PrettyANSIIConfig) => PP.SimpleDocTree Ann -> Text
renderANSII tree = runST do
    idents <- Disambiguate.new
    constructors <- Disambiguate.new
    skolems <- Disambiguate.new
    metas <- Disambiguate.new
    flip evalStateT 0 $ tree & PP.renderSimplyDecoratedA pure \ann textA -> do
        text <- textA
        case ann of
            Ident name unique -> lift do
                text <- disambiguate idents name unique
                pure $ "\ESC[38;5;159m\STX" <> text <> "\ESC[0m\STX"
            Constructor name unique -> lift do
                text <- disambiguate constructors name unique
                pure $ "\ESC[96m\STX" <> text <> "\ESC[0m\STX"
            Skolem name unique -> lift do
                text <- disambiguate skolems name unique
                pure $ "\ESC[38;5;159m\STX" <> text <> "\ESC[0m\STX"
            Number -> pure $ "\ESC[1m\ESC[93m\STX" <> text <> "\ESC[0m\STX"
            Literal -> pure $ "\ESC[32m\STX" <> text <> "\ESC[0m\STX"
            Emphasis -> pure $ "\ESC[1m\STX" <> text <> "\ESC[0m\STX"
            Error -> pure $ "\ESC[1m\ESC[31m\STX" <> text <> "\ESC[0m\STX"
            Warning -> pure $ "\ESC[1m\ESC[93m\STX" <> text <> "\ESC[0m\STX"
            Note -> pure $ "\ESC[38;5;8m\STX" <> text <> "\ESC[0m\STX"
            Keyword -> pure $ "\ESC[94m\STX" <> text <> "\ESC[0m\STX"
            Quote -> pure text
            LParen -> do
                colorIndex <- state (\i -> (i, (i + 1) `mod` (length parenColors)))
                pure $ parenColors ! colorIndex <> text <> "\ESC[0m\STX"
            RParen -> do
                colorIndex <- state (\i -> ((i - 1) `mod` (length parenColors), (i - 1) `mod` (length parenColors)))
                pure $ parenColors ! colorIndex <> text <> "\ESC[0m\STX"
            Meta name unique -> lift do
                text <- disambiguate metas name unique
                pure $ "\ESC[38;5;195m\STX" <> text <> "\ESC[0m\STX"
            Unique unique
                | ?config.includeUnique ->
                    pure $ text <> "\ESC[38;5;159m\STX_" <> show (hashUnique unique) <> "\ESC[0m\STX"
                | otherwise -> pure text
  where
    parenColors = ["\ESC[38;5;46m\STX", "\ESC[38;5;50m\STX", "\ESC[38;5;191m\STX"]

prettyPlain :: Doc Ann -> Text
prettyPlain doc = renderPlain (PP.treeForm (PP.layoutSmart (PP.defaultLayoutOptions{PP.layoutPageWidth = PP.Unbounded}) doc))

prettyANSII :: (?config :: PrettyANSIIConfig) => Doc Ann -> Text
prettyANSII doc = renderANSII (PP.treeForm (PP.layoutSmart (PP.defaultLayoutOptions{PP.layoutPageWidth = PP.Unbounded}) doc))

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
    prettyGenUntagged :: forall k c i (x :: k). (Pretty c) => K1 i c x -> Doc Ann
    prettyGenUntagged (K1 x) = pretty x

instance (PrettyGenUntagged f) => PrettyGenUntagged (M1 i t f) where
    prettyGenUntagged (M1 x) = prettyGenUntagged x