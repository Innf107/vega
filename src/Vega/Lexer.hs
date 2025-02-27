{-# LANGUAGE NoOverloadedLists #-}

module Vega.Lexer (lex) where

import Relude hiding (many)

import Data.Char (isLetter)
import Data.Text qualified as Text
import Data.Vector (Vector)
import Text.Megaparsec as Megaparsec hiding (Token)
import Text.Megaparsec.Char qualified as Char
import Text.Megaparsec.Char.Lexer (skipBlockCommentNested, skipLineComment)
import Text.Megaparsec.Char.Lexer qualified as MegaParsec.Lexer
import Vega.Loc (Loc)

type Lexer = Megaparsec.Parsec Void Text

data TokenClass
    = Ident Text
    | Constructor Text
    | LParen
    | RParen
    | Lambda
    | Equals
    | Arrow
    | LBrace
    | RBrace
    | Colon
    | Comma
    | Period

data Token = MkToken
    { token :: TokenClass
    , loc :: Loc
    }

space :: Lexer ()
space = MegaParsec.Lexer.space Char.space1 (skipLineComment "--") (skipBlockCommentNested "{-" "-}")

lexeme :: Lexer a -> Lexer a
lexeme = MegaParsec.Lexer.lexeme space

symbol :: Text -> Lexer Text
symbol = MegaParsec.Lexer.symbol space

keyword :: Text -> Lexer ()
keyword text = lexeme (chunk text) >> pure ()

withLoc :: Lexer TokenClass -> Lexer Token
withLoc tokenParser = do
    position <- undefined -- we aren't supposed to call getSourcePos every time so i guess we should use offsets huh
    token <- tokenParser
    pure $ MkToken{token, loc = undefined}

lex :: Lexer [Token]
lex =
    many
        $ withLoc
        $ choice
            [ symbol "(" >> pure LParen
            , symbol ")" >> pure RParen
            , symbol "{" >> pure LBrace
            , symbol "}" >> pure RBrace
            , symbol "\\" >> pure Lambda
            , symbol "=" >> pure Equals -- TODO: parse operators together (not actual symbols like parens or lambdas though)
            , symbol "->" >> pure Arrow
            , symbol ":" >> pure Colon
            , symbol "," >> pure Comma
            , symbol "." >> pure Period
            , constructor
            , ident
            ]

ident :: Lexer TokenClass
ident = lexeme do
    firstChar <- Char.lowerChar
    rest <- takeWhile1P Nothing isLetter
    pure (Ident (Text.cons firstChar rest))

constructor :: Lexer TokenClass
constructor = lexeme do
    firstChar <- Char.upperChar
    rest <- takeWhile1P Nothing isLetter
    pure (Constructor (Text.cons firstChar rest))
