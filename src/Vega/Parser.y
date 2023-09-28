{
{-# LANGUAGE NoStrictData #-}
module Vega.Parser where

import Prelude
import Vega.Prelude (Generic, fromList, Text, Vector)
import Vega.Lexer (Token(..), TokenClass(..))
import Vega.Syntax

import Vega.Loc (HasLoc(..), merge)
import Vega.Pretty
}

%name parse main
%tokentype { Token }
%error { parseErrorFrom }

%monad { ParseM }

%token
    identLoc        { (\case { MkToken (IDENT ident) loc -> Just (loc, ident); _ -> Nothing } -> Just $$) }
    intLoc          { (\case { MkToken (INT int) loc -> Just (loc, int); _ -> Nothing } -> Just $$) }
    stringLoc       { (\case { MkToken (STRING string) loc -> Just (loc, string); _ -> Nothing } -> Just $$) }
    '\\'            { MkToken LAMBDA _ }
    '->'            { MkToken ARROW _ }
    ':'             { MkToken COLON _ }
    '='             { MkToken EQUALS _ }
    '('             { MkToken LPAREN _ }
    ')'             { MkToken RPAREN _ }
    '{'             { MkToken LBRACE _ }
    '}'             { MkToken RBRACE _ }
    ','             { MkToken COMMA _ }
    ';'             { MkToken SEMI _ }
    'let'           { MkToken LET _ }
    'case'          { MkToken CASE _ }
    'forall'        { MkToken FORALL _ }
    eof             { MkToken EOF _ }


%%

ident :: { Text }
ident : identLoc { snd $1 }

int :: { Integer }
int : intLoc { snd $1 }

string :: { Text }
string : stringLoc { snd $1 }


-- TODO: This is technically a little inefficient since
-- left recursion is much faster for shift-reduce parsers
-- like happy
manyList(p)
    :               { [] }
    | p manyList(p) { $1 : $2 }

many(p) : manyList(p) { fromList @(Vector _) $1 }

sepTrailingList(sep, p)
    :                               { [] }
    | p                             { [$1] }
    | p sep sepTrailingList(sep, p) { $1 : $3 }

sepTrailing(sep, p) : sepTrailingList(sep, p) { fromList @(Vector _) $1 }


main :: { Vector (Declaration Parsed) }
main : sepTrailing(';', declaration) { $1 }

declaration :: { Declaration Parsed }
declaration 
    : identLoc ':' type ';' ident many(pattern) '=' expr
        {% if snd $1 /= $5 then 
            parseError (MismatchedDeclarationName { loc = merge $1 $8, signature = snd $1, definition = $5 })
           else 
            pure $ DefineFunction (fst $1) (snd $1) $3 $6 $8 }

expr :: { Expr Parsed }
expr : expr_app '->' expr                   { EPi (merge $1 $3) Nothing $1 $3 }
     | expr_app                             { $1 }

expr_app :: { Expr Parsed }
expr_app : expr_app expr_leaf   { App (merge $1 $2) $1 $2 }
         | expr_leaf            { $1 }

expr_leaf : identLoc                                { Var (fst $1) (snd $1) }
          | '(' expr ')'                            { $2 }
          | '(' ident ':' expr ')' '->' expr        { EPi (merge $1 $7) (Just $2) $4 $7 }
          | '\\' pattern '->' expr                  { Lambda (merge $1 $4) $2 $4 }
          | 'case' expr '{' 
                sepTrailing(';', caseBranch) 
            '}'                                     { Case (merge $1 $5) $2 $4 }

type : expr { $1 }

caseBranch : pattern '->' expr { ($1, $3) }

pattern :: { Pattern Parsed }
pattern : identLoc { VarPat (fst $1) (snd $1) }

{
data ParseError
    = MismatchedDeclarationName { loc :: Loc, signature :: Text, definition :: Text }
    | ParseError Loc
    deriving (Generic)
instance HasLoc ParseError

instance Pretty ParseError where
    pretty (MismatchedDeclarationName { signature, definition }) =
        "Function declared with different names.\n"
        <> "    The type signature calls it        " <> identText signature <> "\n"
        <> "    But its definition refers to it as " <> identText definition
    pretty (ParseError _) = "Parse Error"

newtype ParseM a = MkParseM (Either ParseError a)
    deriving newtype (Functor, Applicative, Monad)

runParseM :: ParseM a -> Either ParseError a
runParseM (MkParseM either) = either

parseError :: ParseError -> ParseM a
parseError error = MkParseM (Left error)

parseErrorFrom :: [Token] -> ParseM a
parseErrorFrom [] = undefined
parseErrorFrom (token : _) = do
    parseError (ParseError (getLoc token))
}