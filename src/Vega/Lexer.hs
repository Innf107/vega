{-# LANGUAGE NoOverloadedLists #-}

module Vega.Lexer (
    Lexer,
    run,
    Token (..),
) where

import Relude hiding (many)

import Data.Char qualified as Char
import Data.Ratio ((%))
import Data.Text qualified as Text
import Relude.Unsafe (read)
import Vega.Loc (Loc (..))

data LexicalError
    = UnexpectedCharacter Loc Char
    | UnterminatedStringLiteral Loc
    | InvalidStringEscape Loc Char
    | EmptyHexEscape Loc

newtype Lexer a = MkLexer (Either LexicalError a)
    deriving newtype (Functor, Applicative, Monad)
unLexer :: Lexer a -> Either LexicalError a
unLexer (MkLexer either) = either

lexicalError :: LexicalError -> Lexer a
lexicalError error = MkLexer (Left error)

data Token
    = EOF
    | Ident Text
    | Constructor Text
    | StringLiteral Text
    | IntLiteral Integer
    | FloatLiteral Rational
    | LParen
    | RParen
    | Lambda
    | DoubleEquals
    | Equals
    | Arrow
    | EffArrowStart
    | EffArrowEnd
    | LBrace
    | RBrace
    | DoubleColon
    | Colon
    | Semicolon
    | Comma
    | Period
    | Pipe
    | Let
    | Data
    | Forall
    deriving (Show, Eq, Ord, Generic)

data LexState = MkLexState
    { startLine :: Int
    , startColumn :: Int
    , endLine :: Int
    , endColumn :: Int
    , remainingText :: Text
    , file :: Text
    }
    deriving (Show, Generic)

-- TODO
locOfLastCharOnly :: LexState -> Loc
locOfLastCharOnly lexState = locOfNextCharOnly lexState

locOfNextCharOnly :: LexState -> Loc
locOfNextCharOnly lexState =
    MkLoc
        { file = lexState.file
        , startLine = lexState.endLine
        , startColumn = lexState.endColumn
        , endLine = lexState.endColumn
        , endColumn = lexState.endColumn
        }

currentLoc :: LexState -> Loc
currentLoc state =
    MkLoc
        { file = state.file
        , startLine = state.startLine
        , startColumn = state.startColumn
        , endLine = state.endLine
        , endColumn = state.endColumn
        }

newLexState :: Text -> Text -> LexState
newLexState fileName contents =
    MkLexState
        { startLine = 1
        , startColumn = 1
        , endLine = 1
        , endColumn = 1
        , remainingText = contents
        , file = fileName
        }

skipSpaces :: LexState -> LexState
skipSpaces lexState = lexState{startLine = lexState.endLine, startColumn = lexState.endColumn}

takeChar :: LexState -> Maybe (Char, LexState)
takeChar state = case Text.uncons state.remainingText of
    Nothing -> Nothing
    Just ('\n', rest) ->
        Just ('\n', state{endLine = state.endLine + 1, endColumn = 1, remainingText = rest})
    Just (char, rest) ->
        Just (char, state{endColumn = state.endColumn + 1, remainingText = rest})

infixr 5 :!
pattern (:!) :: Char -> LexState -> LexState
pattern char :! state <- (takeChar -> Just (char, state))

pattern IsEOF :: LexState
pattern IsEOF <- (takeChar -> Nothing)

{-# COMPLETE (:!), IsEOF #-}

run :: Text -> Text -> Either LexicalError [(Token, Loc)]
run fileName text = do
    let go state = case unLexer (lex state) of
            Left error -> Left error
            Right (token, state) -> do
                rest <- go (skipSpaces state)
                pure $ (token, currentLoc state) : rest
    go (newLexState fileName text)

lex :: LexState -> Lexer (Token, LexState)
lex state = case state of
    '-' :! '-' :! state -> lexLineComment state
    '(' :! state -> pure (LParen, state)
    ')' :! state -> pure (RParen, state)
    '\\' :! state -> pure (Lambda, state)
    '=' :! '=' :! state -> pure (DoubleEquals, state)
    '=' :! state -> pure (Equals, state)
    '-' :! '>' :! state -> pure (Arrow, state)
    '-' :! '{' :! state -> pure (EffArrowStart, state)
    '}' :! '>' :! state -> pure (EffArrowEnd, state)
    '{' :! state -> pure (LBrace, state)
    '}' :! state -> pure (RBrace, state)
    ':' :! ':' :! state -> pure (DoubleColon, state)
    ':' :! state -> pure (Colon, state)
    ';' :! state -> pure (Semicolon, state)
    ',' :! state -> pure (Comma, state)
    '.' :! state -> pure (Period, state)
    '|' :! state -> pure (Pipe, state)
    '"' :! state -> lexStringLiteral [] state
    char :! state
        | Char.isDigit char -> lexNumber [char] state
        | isConstructorStart char -> lexConstructor [char] state
        | isIdentifierStart char -> lexIdentifier [char] state
        | Char.isSpace char -> lex (skipSpaces state)
        | otherwise -> lexicalError (UnexpectedCharacter (locOfLastCharOnly state) char)
    IsEOF -> pure (EOF, state)

lexLineComment :: LexState -> Lexer (Token, LexState)
lexLineComment state = case state of
    '\n' :! state -> lex (skipSpaces state)
    _ :! state -> lexLineComment state
    IsEOF -> pure (EOF, state)

lexStringLiteral :: [Char] -> LexState -> Lexer (Token, LexState)
lexStringLiteral chars state = case state of
    '"' :! state -> pure (StringLiteral (fromString (reverse chars)), state)
    '\\' :! '0' :! state -> lexStringLiteral ('\0' : chars) state
    '\\' :! 'a' :! state -> lexStringLiteral ('\a' : chars) state
    '\\' :! 'b' :! state -> lexStringLiteral ('\b' : chars) state
    '\\' :! 'e' :! state -> lexStringLiteral ('\ESC' : chars) state
    '\\' :! 'f' :! state -> lexStringLiteral ('\f' : chars) state
    '\\' :! 'n' :! state -> lexStringLiteral ('\n' : chars) state
    '\\' :! 'r' :! state -> lexStringLiteral ('\r' : chars) state
    '\\' :! 't' :! state -> lexStringLiteral ('\t' : chars) state
    '\\' :! 'v' :! state -> lexStringLiteral ('\v' : chars) state
    '\\' :! '\\' :! state -> lexStringLiteral ('\\' : chars) state
    '\\' :! '\'' :! state -> lexStringLiteral ('\'' : chars) state
    '\\' :! '"' :! state -> lexStringLiteral ('\"' : chars) state
    '\\' :! 'x' :! state -> do
        let go :: Int -> Int -> LexState -> Lexer (Char, LexState)
            go maxDigits soFar state
                | maxDigits == 0 = pure (toEnum soFar, state)
                | otherwise = case state of
                    char :! state
                        | Char.isHexDigit char -> go maxDigits (soFar * 16 + hexValue char) state
                    state
                        | maxDigits >= 6 -> lexicalError (EmptyHexEscape (locOfLastCharOnly state))
                        | otherwise -> pure (toEnum soFar, state)

        (escapedChar, state) <- go 6 0 state
        lexStringLiteral (escapedChar : chars) state
    '\\' :! char :! state -> lexicalError (InvalidStringEscape (locOfLastCharOnly state) char)
    char :! state -> lexStringLiteral (char : chars) state
    IsEOF -> lexicalError (UnterminatedStringLiteral (locOfNextCharOnly state))

hexValue :: (HasCallStack) => Char -> Int
hexValue char
    | char `elem` ("abcdef" :: String) = fromEnum char - fromEnum 'a'
    | char `elem` ("ABCDEF" :: String) = fromEnum char - fromEnum 'A'
    | char `elem` ("0123456789" :: String) = fromEnum char - fromEnum '0'
    | otherwise = error $ "hexValue: called on non hex digit: " <> show char

lexNumber :: [Char] -> LexState -> Lexer (Token, LexState)
lexNumber digits state = case state of
    '_' :! state -> lexNumber digits state
    '.' :! state -> lexFloat digits [] state
    char :! state
        | Char.isDigit char -> lexNumber (char : digits) state
    _ -> pure (IntLiteral (read (reverse digits)), state)

lexFloat :: [Char] -> [Char] -> LexState -> Lexer (Token, LexState)
lexFloat integralDigits decimalDigits state = case state of
    '_' :! state -> lexFloat integralDigits decimalDigits state
    char :! state
        | Char.isDigit char -> lexFloat integralDigits (char : decimalDigits) state
    _ -> do
        let enumerator :: Integer = read (reverse (integralDigits) <> reverse decimalDigits)
        let denominator :: Integer = 10 ^ (length decimalDigits)
        pure (FloatLiteral (enumerator % denominator), state)

lexConstructor :: [Char] -> LexState -> Lexer (Token, LexState)
lexConstructor chars state = case state of
    char :! state
        | isConstructor char -> lexConstructor (char : chars) state
    state -> pure (Constructor (fromString (reverse chars)), state)

lexIdentifier :: [Char] -> LexState -> Lexer (Token, LexState)
lexIdentifier chars state = case state of
    char :! state
        | isIdentifier char -> lexIdentifier (char : chars) state
    state -> pure (Ident (fromString (reverse chars)), state)

isIdentifierStart :: Char -> Bool
isIdentifierStart char = Char.isAlpha char || char == '_'

isIdentifier :: Char -> Bool
isIdentifier char = Char.isAlphaNum char || char `elem` ("_'" :: String)

isConstructorStart :: Char -> Bool
isConstructorStart char = Char.isAlpha char && Char.isUpper char

isConstructor :: Char -> Bool
isConstructor char = isIdentifier char
