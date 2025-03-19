{-# LANGUAGE NoOverloadedLists #-}

module Vega.Lexer (
    Lexer,
    lex,
    Token (..),
) where

import Relude hiding (many)

import Data.Char (isLetter)
import Data.Text qualified as Text
import Data.Vector (Vector)
import Text.Megaparsec as Megaparsec hiding (Token)
import Text.Megaparsec.Char qualified as Char
import Text.Megaparsec.Char.Lexer (skipBlockCommentNested, skipLineComment)
import Text.Megaparsec.Char.Lexer qualified as MegaParsec.Lexer
import Vega.Loc (Loc (MkLoc))

type Lexer = Megaparsec.Parsec Void Text

data Token
    = Ident Text
    | Constructor Text
    | LParen
    | RParen
    | Lambda
    | Equals
    | Arrow
    | EffArrowStart
    | EffArrowEnd
    | LBrace
    | RBrace
    | Colon
    | Semicolon
    | Comma
    | Period
    | Pipe
    | Let
    | Data
    | Forall
    deriving (Show, Eq, Ord, Generic)

space :: Lexer ()
space = MegaParsec.Lexer.space Char.space1 (skipLineComment "--") (skipBlockCommentNested "{-" "-}")

lexeme :: Lexer a -> Lexer a
lexeme = MegaParsec.Lexer.lexeme space

symbol :: Text -> Lexer Text
symbol = MegaParsec.Lexer.symbol space

loc :: Lexer ()
loc = undefined

lex :: Lexer [Token]
lex =
    many
        $ choice
            [ symbol "-{" >> pure EffArrowStart
            , symbol "}>" >> pure EffArrowEnd
            , symbol "(" >> pure LParen
            , symbol ")" >> pure RParen
            , symbol "{" >> pure LBrace
            , symbol "}" >> pure RBrace
            , symbol "\\" >> pure Lambda
            , symbol "=" >> pure Equals -- TODO: parse operators together (not actual symbols like parens or lambdas though)
            , symbol "->" >> pure Arrow
            , symbol ":" >> pure Colon
            , symbol ";" >> pure Semicolon
            , symbol "," >> pure Comma
            , symbol "." >> pure Period
            , symbol "|" >> pure Pipe
            , constructor
            , identOrKeyword
            ]

identOrKeyword :: Lexer Token
identOrKeyword = lexeme do
    firstChar <- Char.lowerChar
    rest <- takeWhile1P Nothing isLetter
    case Text.cons firstChar rest of
        "let" -> pure Let
        "data" -> pure Data
        "forall" -> pure Forall
        identifier -> pure (Ident identifier)

constructor :: Lexer Token
constructor = lexeme do
    firstChar <- Char.upperChar
    rest <- takeWhile1P Nothing isLetter
    pure (Constructor (Text.cons firstChar rest))
