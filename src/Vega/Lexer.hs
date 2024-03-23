module Vega.Lexer (run, LexError (..), Token (..), TokenClass (..)) where

import Vega.Prelude

import Vega.Loc
import Vega.Pretty

import Vega.Difflist

import Data.Char qualified as Char
import Data.Text qualified as Text

import GHC.Show qualified as Show
import Prelude qualified as Read (read)

data LexError
    = UnexpectedEOF Loc
    | UnexpectedChar Loc Char
    | UnterminatedStringLiteral Loc
    deriving (Generic)
instance HasLoc LexError

instance Pretty LexError where
    pretty (UnexpectedEOF _) =
        "Unexpected end of file"
    pretty (UnexpectedChar _ char) =
        "Unexpected character " <> quote (identText [char])
    pretty (UnterminatedStringLiteral _) =
        "Unterminated string literal"

data TokenClass
    = IDENT Text
    | INT Integer
    | STRING Text
    | LAMBDA
    | ARROW
    | COLON
    | EQUALS
    | LBRACE
    | RBRACE
    | LPAREN
    | RPAREN
    | DOUBLESTAR
    | COMMA
    | SEMI
    | PIPE
    | DOT
    | LET
    | CASE
    | FORALL
    | PLUS
    | MINUS
    | STAR
    | DOUBLESLASH
    | EOF
    deriving (Generic, Show)

data Token
    = MkToken TokenClass Loc
    deriving (Generic)

instance HasLoc Token where
    getLoc (MkToken _ loc) = loc
instance Show.Show Token where
    show (MkToken class_ _) = show class_

data LexState = MkLexState
    { underlying :: Text
    , currentLoc :: Loc
    }

-- TODO: this doesn't even stream the tokens since forcing
-- the either needs to force the entire list to see if an error occured
run :: FilePath -> Text -> Either LexError [Token]
run fileName text =
    runLex
        ( MkLexState
            { underlying = text
            , currentLoc =
                Loc
                    { fileName = toText fileName
                    , startLine = 1
                    , startColumn = 1
                    , endLine = 1
                    , endColumn = 1
                    }
            }
        )
        $ lexAll
  where
    lexAll = do
        token <- lex
        case token of
            (MkToken EOF _) -> pure []
            _ -> (token :) <$> lexAll

advance :: Int -> Lex ()
advance amount = MkLex do
    modify
        ( \lexState@MkLexState{currentLoc, underlying} ->
            lexState
                { underlying = Text.drop amount underlying
                , currentLoc =
                    currentLoc
                        { endColumn = currentLoc.endColumn + amount
                        }
                }
        )

advanceLine :: Lex ()
advanceLine = MkLex do
    modify
        ( \lexState@MkLexState{currentLoc} ->
            lexState
                { currentLoc =
                    currentLoc
                        { startLine = currentLoc.endLine + 1
                        , endLine = currentLoc.endLine + 1
                        , startColumn = 1
                        , endColumn = 1
                        }
                }
        )

advanceWhitespace :: Lex ()
advanceWhitespace = MkLex do
    modify
        ( \lexState@MkLexState{currentLoc} ->
            lexState
                { currentLoc =
                    currentLoc
                        { startLine = currentLoc.endLine
                        , startColumn = currentLoc.endColumn
                        }
                }
        )

type family FunctionFrom arguments result where
    FunctionFrom '[] result = result
    FunctionFrom (a : as) result = a -> FunctionFrom as result

data MatchPattern bound where
    Literal :: Text -> MatchPattern '[]
    Or :: Vector (MatchPattern bound) -> MatchPattern bound
    Satisfies :: (Char -> Bool) -> MatchPattern '[]
    SatisfiesAdvance :: (Char -> Bool) -> MatchPattern '[Char]

data MatchCase a where
    C :: MatchPattern bound -> FunctionFrom bound (Lex a) -> MatchCase a

tryMatch :: MatchCase a -> Lex (Maybe (Lex a))
tryMatch matchCase = do
    MkLexState{underlying} <- MkLex get
    case matchCase of
        C (Literal literal) cont
            | literal `Text.isPrefixOf` underlying -> do
                advance (Text.length literal)
                pure (Just cont)
            | otherwise -> pure Nothing
        C (Or patterns) cont ->
            findMapM tryMatch (fmap (\pattern_ -> (C pattern_ cont)) patterns)
        C (Satisfies predicate) cont -> do
            case Text.uncons underlying of
                Just (char, _)
                    | predicate char -> do
                        pure (Just cont)
                _ -> pure Nothing
        C (SatisfiesAdvance predicate) cont -> do
            case Text.uncons underlying of
                Just (char, _)
                    | predicate char -> do
                        advance 1
                        pure (Just (cont char))
                _ -> pure Nothing

-- The bound ~ '[] trick is necessary to get string literals to infer
-- the correct type. Without this, any other argument to MatchPattern could
-- theoretically have an IsString instance as well.
instance (bound ~ '[]) => IsString (MatchPattern bound) where
    fromString string = Literal (fromString string)

match :: Vector (MatchCase a) -> (Char -> Lex a) -> Lex a -> Lex a
match cases default_ onEOF = do
    matched <- findMapM tryMatch cases
    case matched of
        Nothing -> do
            MkLexState{underlying} <- MkLex get
            case Text.uncons underlying of
                Nothing -> onEOF
                Just (char, _) -> default_ char
        Just cont -> do
            cont

emit :: TokenClass -> Lex Token
emit class_ = do
    loc <- currentLoc
    pure (MkToken class_ loc)

currentLoc :: Lex Loc
currentLoc = MkLex do
    MkLexState{currentLoc} <- get
    pure currentLoc

lex :: Lex Token
lex = do
    match
        [ C "\\" $ emit LAMBDA
        , C ":" $ emit COLON
        , C "." $ emit DOT
        , C "=" $ emit EQUALS
        , C "(" $ emit LPAREN
        , C ")" $ emit RPAREN
        , C "{" $ emit LBRACE
        , C "}" $ emit RBRACE
        , C "**" $ emit DOUBLESTAR
        , C "," $ emit COMMA
        , C ";" $ emit SEMI
        , C "|" $ emit PIPE
        , C "->" $ emit ARROW
        , C "let" $ emit LET
        , C "case" $ emit CASE
        , C "forall" $ emit FORALL
        , C "--" $ lexLineComment
        , C "+" $ emit PLUS
        , C "-" $ emit MINUS
        , C "*" $ emit STAR
        , C "//" $ emit DOUBLESLASH
        , C "\"\"\"" $ lexStringLiteral "\"\"\"" []
        , C "\"" $ lexStringLiteral "\"" []
        , C "\'\'\'" $ lexStringLiteral "\'\'\'" []
        , C "\'" $ lexStringLiteral "\'" []
        , C "\n" $ advanceLine >> advanceWhitespace >> lex
        , C (SatisfiesAdvance Char.isSpace) $ \_ -> advanceWhitespace >> lex
        , C (SatisfiesAdvance Char.isDigit) $ \char -> lexIntLiteral [char]
        , C (SatisfiesAdvance isIdentStart) $ \char -> lexIdent [char]
        ]
        -- otherwise
        ( \char -> do
            loc <- currentLoc
            lexError (UnexpectedChar loc char)
        )
        -- on EOF
        (emit EOF)

lexLineComment :: Lex Token
lexLineComment = do
    match
        [ C "\n" $ advanceLine >> advanceWhitespace >> lex
        ]
        (\_ -> advance 1 >> advanceWhitespace >> lexLineComment)
        (emit EOF)

lexIntLiteral :: Difflist Char -> Lex Token
lexIntLiteral chars =
    match
        [ C (SatisfiesAdvance Char.isDigit) \char -> lexIntLiteral (chars <> [char])
        ]
        (\_ -> emit (INT (Read.read (toList chars))))
        (emit (INT (Read.read (toList chars))))

lexStringLiteral :: Text -> Difflist Char -> Lex Token
lexStringLiteral end chars =
    match
        [ C (Literal end) $ emit (STRING (fromString $ toList chars))
        ]
        (\char -> advance 1 >> lexStringLiteral end (chars <> [char]))
        ( do
            loc <- currentLoc
            lexError (UnterminatedStringLiteral loc)
        )

lexIdent :: Difflist Char -> Lex Token
lexIdent chars =
    match
        [ C (SatisfiesAdvance isIdent) \char -> lexIdent (chars <> [char])
        ]
        (\_ -> emit (IDENT (toText (toList chars))))
        (emit (IDENT (toText (toList chars))))

isIdentStart :: Char -> Bool
isIdentStart char = Char.isAlpha char || char `Text.elem` "_"

isIdent :: Char -> Bool
isIdent char = Char.isAlphaNum char || char `Text.elem` "_'"

newtype Lex a = MkLex (StateT LexState (Either LexError) a)
    deriving newtype (Functor, Applicative, Monad)

runLex :: LexState -> Lex a -> Either LexError a
runLex state (MkLex stateT) = evalStateT stateT state

lexError :: LexError -> Lex a
lexError error = MkLex (throwError error)
