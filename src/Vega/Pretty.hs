{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE UndecidableInstances #-}
-- We include a Num constraint on 'number' to prevent mistakes so -Wredundant-constraints doesn't make sense here
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Vega.Pretty (
    Ann,
    plain,
    localIdentText,
    globalIdentText,
    localConstructorText,
    globalConstructorText,
    skolem,
    generatedVar,
    number,
    numberDoc,
    emphasis,
    errorText,
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
    PrettyId (..),
    PP.Doc,
    renderPlain,
    PrettyANSIIConfig (..),
    defaultPrettyANSIIConfig,
    renderANSII,
    prettyPlain,
    prettyANSII,
    eprintANSII,
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

import Vega.Disambiguate (disambiguate, disambiguate0)
import Vega.Disambiguate qualified as Disambiguate
import Vega.Util (Untagged (..))

import Prettyprinter (Doc)
import Prettyprinter qualified as PP
import Prettyprinter.Render.Util.SimpleDocTree qualified as PP

import Control.Monad.ST.Strict (runST)
import Data.Text.IO qualified as Text
import Data.Unique (Unique, hashUnique, newUnique)
import Data.Vector ((!))
import GHC.Generics
import GHC.TypeLits (KnownSymbol, symbolVal)

data Ann
    = LocalIdent
    | GlobalIdent
    | LocalConstructor
    | GlobalConstructor
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
    | GeneratedVar Text Unique

plain :: Text -> Doc Ann
plain = PP.pretty

localIdentText :: Text -> Doc Ann
localIdentText name = PP.annotate LocalIdent (PP.pretty name)

globalIdentText :: Text -> Doc Ann
globalIdentText name = PP.annotate GlobalIdent (PP.pretty name)

localConstructorText :: Text -> Doc Ann
localConstructorText name = PP.annotate LocalConstructor (PP.pretty name)

globalConstructorText :: Text -> Doc Ann
globalConstructorText name = PP.annotate GlobalConstructor (PP.pretty name)

skolem :: Unique -> Text -> Doc Ann
skolem unique name = PP.annotate (Unique unique) $ PP.annotate (Skolem name unique) (PP.pretty name)

generatedVar :: Unique -> Text -> Doc Ann
generatedVar unique name = PP.annotate (Unique unique) $ PP.annotate (GeneratedVar name unique) (PP.pretty name)

number :: (Num a, Show a) => a -> Doc Ann
number = PP.annotate Number . PP.pretty . show @Text

numberDoc :: Doc Ann -> Doc Ann
numberDoc = PP.annotate Number

emphasis :: Text -> Doc Ann
emphasis = PP.annotate Emphasis . PP.pretty

errorText :: Text -> Doc Ann
errorText = PP.annotate Error . PP.pretty

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
meta unique name = PP.annotate (Unique unique) $ PP.annotate (Meta name unique) (PP.pretty name)

literal :: Text -> Doc Ann
literal = PP.annotate Literal . PP.pretty

class Pretty a where
    pretty :: a -> Doc Ann

newtype PrettyId = PrettyId (Doc Ann)

instance Pretty PrettyId where
    pretty = coerce

renderPlain :: PP.SimpleDocTree Ann -> Text
renderPlain tree = runST do
    skolems <- Disambiguate.new
    metas <- Disambiguate.new
    generated <- Disambiguate.new
    tree & PP.renderSimplyDecoratedA pure \ann textA -> do
        text <- textA
        case ann of
            LocalIdent -> pure text
            GlobalIdent -> pure text
            LocalConstructor -> pure text
            GlobalConstructor -> pure text
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
            GeneratedVar unique name -> disambiguate0 generated unique name

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
    skolems <- Disambiguate.new
    metas <- Disambiguate.new
    generated <- Disambiguate.new
    flip evalStateT 0 $
        tree & PP.renderSimplyDecoratedA pure \ann textA -> do
            text <- textA
            case ann of
                LocalIdent -> lift do
                    pure $ "\ESC[38;5;159m\STX" <> text <> "\ESC[0m\STX"
                GlobalIdent -> lift do
                    pure $ "\ESC[96m\STX" <> text <> "\ESC[0m\STX"
                LocalConstructor -> lift do
                    pure $ "\ESC[38;5;223m\STX" <> text <> "\ESC[0m\STX"
                GlobalConstructor -> lift do
                    pure $ "\ESC[38;5;225m\STX" <> text <> "\ESC[0m\STX"
                Skolem name unique -> lift do
                    text <- case ?config.includeUnique of
                        -- If we include the unique anyway, we don't need to disambiguate
                        True -> pure name
                        False -> disambiguate skolems name unique
                    pure $ "\ESC[38;5;227m\STX" <> text <> "\ESC[0m\STX"
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
                    text <- case ?config.includeUnique of
                        -- If we include the unique anyway, we don't need to disambiguate
                        True -> pure name
                        False -> disambiguate metas name unique
                    pure $ "\ESC[38;5;195m\STX" <> text <> "\ESC[0m\STX"
                Unique unique
                    | ?config.includeUnique ->
                        pure $ text <> "\ESC[38;5;8m\STX#" <> show (hashUnique unique) <> "\ESC[0m\STX"
                    | otherwise -> pure text
                GeneratedVar name unique -> lift do
                    text <- case ?config.includeUnique of
                        -- If we include the unique anyway, we don't need to disambiguate
                        True -> pure name
                        False -> disambiguate0 generated name unique
                    pure $ "\ESC[38;5;230m\STX" <> text <> "\ESC[0m\STX"
  where
    parenColors = ["\ESC[38;5;46m\STX", "\ESC[38;5;50m\STX", "\ESC[38;5;191m\STX"]

prettyPlain :: Doc Ann -> Text
prettyPlain doc = renderPlain (PP.treeForm (PP.layoutSmart (PP.defaultLayoutOptions{PP.layoutPageWidth = PP.Unbounded}) doc))

prettyANSII :: (?config :: PrettyANSIIConfig) => Doc Ann -> Text
prettyANSII doc = renderANSII (PP.treeForm (PP.layoutSmart (PP.defaultLayoutOptions{PP.layoutPageWidth = PP.Unbounded}) doc))

eprintANSII :: (?config :: PrettyANSIIConfig, MonadIO io) => Doc Ann -> io ()
eprintANSII doc = liftIO $ Text.hPutStrLn stderr (prettyANSII doc)

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

instance Pretty Int where
    pretty = number

instance Pretty () where
    pretty () = keyword "()"

instance (Generic a, PrettyGen (Rep a)) => Pretty (Generically a) where
    pretty (Generically x) = prettyGen (from x)

class PrettyGen f where
    prettyGen :: f x -> Doc Ann

instance PrettyGen V1 where
    prettyGen = \case {}

instance (Pretty a) => PrettyGen (K1 _r a) where
    prettyGen (K1 x) = pretty x

instance (PrettyGen f, PrettyGen g) => PrettyGen (f :+: g) where
    prettyGen (L1 x) = prettyGen x
    prettyGen (R1 x) = prettyGen x

instance (PrettyGen f) => PrettyGen (D1 _meta f) where
    prettyGen (M1 x) = prettyGen x

instance (PrettyGenArguments f, KnownSymbol name) => PrettyGen (C1 (MetaCons name _fixity False) f) where
    prettyGen (M1 x) = globalConstructorText (toText $ symbolVal (Proxy @name)) <> lparen "(" <> prettyGenArguments x <> rparen ")"

instance (PrettyGenArguments f, KnownSymbol name) => PrettyGen (C1 (MetaCons name _fixity True) f) where
    prettyGen (M1 x) = globalConstructorText (toText $ symbolVal (Proxy @name)) <> lparen "{" <> prettyGenArguments x <> rparen "}"

class PrettyGenArguments f where
    prettyGenArguments :: f x -> Doc Ann

instance PrettyGenArguments V1 where
    prettyGenArguments = \case {}

instance PrettyGenArguments U1 where
    prettyGenArguments = mempty

instance {-# OVERLAPPING #-} (Pretty a) => PrettyGenArguments (K1 _r (Seq a)) where
    prettyGenArguments (K1 seq) = lparen "[" <> intercalateDoc (keyword ", ") (fmap pretty seq) <> rparen "]"

instance (Pretty a) => PrettyGenArguments (K1 _r a) where
    prettyGenArguments (K1 y) = pretty y

instance (PrettyGenArguments f, PrettyGenArguments g) => PrettyGenArguments (f :*: g) where
    prettyGenArguments (x :*: y) = prettyGenArguments x <> keyword "," PP.<+> prettyGenArguments y

instance (PrettyGenArguments f) => PrettyGenArguments (S1 (MetaSel Nothing _unpacked _sourceStrictness _realStrictness) f) where
    prettyGenArguments (M1 x) = prettyGenArguments x

instance (PrettyGenArguments f, KnownSymbol name) => PrettyGenArguments (S1 (MetaSel (Just name) _unpacked _sourceStrictness _realStrictness) f) where
    prettyGenArguments (M1 x) = globalIdentText (toText (symbolVal (Proxy @name))) PP.<+> keyword "::" PP.<+> prettyGenArguments x
