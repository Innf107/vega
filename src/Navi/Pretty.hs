module Navi.Pretty (
    Pretty (..),
    TextStyle (..),
    intercalate,
    ANSI (ANSI),
    Plain (Plain),
) where

import Navi.Prelude hiding (intercalate)

class Pretty a where
    pretty :: (?style :: style, TextStyle style) => a -> Doc style

class (Monoid (Doc a)) => TextStyle a where
    literal :: (?style :: a) => Text -> Doc a

    identifier :: (?style :: a) => Text -> Doc a
    keyword :: (?style :: a) => Text -> Doc a
    operator :: (?style :: a) => Text -> Doc a
    paren :: (?style :: a) => Text -> Doc a
    error :: (?style :: a) => Text -> Doc a
    emphasis :: (?style :: a) => Text -> Doc a
    note :: (?style :: a) => Text -> Doc a
    number :: (?style :: a, Num number, Show number) => number -> Doc a

    type Doc a

intercalate :: (Monoid a) => a -> [a] -> a
intercalate _ [] = mempty
intercalate _ [x] = x
intercalate sep (x : xs) = x <> sep <> intercalate sep xs

data ANSI = ANSI

instance TextStyle ANSI where
    literal :: (?style::ANSI) => Text -> Doc ANSI
    literal text = text

    identifier text = "\ESC[1m\STX" <> text <> "\ESC[0m\STX"
    keyword text = "\ESC[96m\STX" <> text <> "\ESC[0m\STX"
    operator text = "\ESC[94m\STX" <> text <> "\ESC[0m\STX"
    paren = operator
    error text = "\ESC[31m\ESC[38;2;255;0;0m\STX" <> text <> "\ESC[0m\STX"
    emphasis text = "\ESC[1m\STX" <> text <> "\ESC[0m\STX"
    note text = "\ESC[38;5;8m\STX" <> text <> "\ESC[0m\STX"
    number num = "\ESC[1m\ESC[93m\STX" <> show num <> "\ESC[0m\STX"

    type Doc ANSI = Text

data Plain = Plain

instance TextStyle Plain where
    literal = id

    identifier = id
    keyword = id
    operator = id
    paren = id
    error = id
    emphasis = id
    note = id
    number = show

    type Doc Plain = Text
