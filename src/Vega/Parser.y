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
    '.'             { MkToken DOT _ }
    '='             { MkToken EQUALS _ }
    '('             { MkToken LPAREN _ }
    ')'             { MkToken RPAREN _ }
    '{'             { MkToken LBRACE _ }
    '}'             { MkToken RBRACE _ }
    ','             { MkToken COMMA _ }
    ';'             { MkToken SEMI _ }
    '|'             { MkToken PIPE _ }
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

many1(p) : p manyList(p) { fromList @(Vector _) ($1 : $2) }

sepTrailingList(sep, p)
    :                               { [] }
    | p                             { [$1] }
    | p sep sepTrailingList(sep, p) { $1 : $3 }

sepTrailing(sep, p) : sepTrailingList(sep, p) { fromList @(Vector _) $1 }


main :: { Vector (Declaration Parsed) }
main : sepTrailing(';', declaration) { $1 }

declaration :: { Declaration Parsed }
declaration
    : identLoc ':' type ';'
      ident many(pattern) '=' expr
        {% if snd $1 /= $5 then
            parseError (MismatchedDeclarationName { loc = merge $1 $8, signature = snd $1, definition = $5 })
           else
            pure $ DefineFunction (fst $1) (snd $1) $3 $6 $8 }

expr :: { Expr Parsed }
expr : expr_ascription '->' expr            { EPi (merge $1 $3) Nothing $1 $3 }
     | expr_ascription                      { $1 }

expr_ascription :: { Expr Parsed }
expr_ascription : expr_app ':' expr     { Ascription (merge $1 $3) $1 $3 }
                | expr_app              { $1 }

expr_app :: { Expr Parsed }
expr_app : expr_app expr_leaf   { App (merge $1 $2) $1 $2 }
         | expr_leaf            { $1 }

expr_leaf :: { Expr Parsed }
expr_leaf : identLoc                                    { Var (fst $1) (snd $1) }
          | '(' expr ')'                                { $2 }
          | '(' ')'                                     { TupleLiteral (merge $1 $2) [] }
          | '(' expr ',' sepTrailingList(',', expr) ')' { TupleLiteral (merge $1 $5) (fromList ($2 : $4)) }
          | '(' ident ':' expr ')' '->' expr            { EPi (merge $1 $7) (Just $2) $4 $7 }
          | '\\' many1(pattern) '->' expr               { foldr (\pattern expr -> Lambda (merge $1 $4) pattern expr) $4 $2 }
          | 'case' expr '{' 
                sepTrailing(';', caseBranch) 
            '}'                                         { Case (merge $1 $5) $2 $4 }
          | literal                                     { Literal (fst $1) (snd $1) }
          | '{' sepTrailing(';', statement) '}'         { Sequence (merge $1 $3) $2 }
          -- Not sure about this syntax yet to be honest
          | '{' sepTrailing(',', type) '}'              { ETupleType (merge $1 $3) $2 }
          | 'forall' many1(forallVar) '.' expr          { foldr (\(name, type_) rest -> EForall (merge $1 $4) name type_ rest) $4 $2 }

forallVar :: { (Text, Expr Parsed) }
forallVar : identLoc                { (snd $1, Literal (fst $1) TypeLit ) }
          | '(' ident ':' type ')'  { ($2, $4) }

literal :: { (Loc, Literal) }
literal : intLoc                   { (fst $1, IntLit (snd $1)) }
        | stringLoc                { (fst $1, StringLit (snd $1)) }
        -- primitive type literals are resolved in the renamer so we don't need to care about them yet

statement :: { Statement Parsed }
statement : expr                                { RunExpr (getLoc $1) $1 }
          | 'let' pattern '=' expr              { Let (merge $1 $4) $2 $4 }
          | 'let' ident ':' type ';' 
            'let' ident many(pattern) '=' expr  {%
                if $2 == $7 then
                    pure $ LetFunction (merge $1 $10) $2 (Just $4) $8 $10
                else
                    -- TODO: This should probably report a smaller location to avoid turning *everything* red in an LSP
                    parseError (MismatchedDeclarationName { loc = merge $1 $10, signature = $2, definition = $7 })
                }
          | 'let' ident many(pattern) '=' expr  { LetFunction (merge $1 $5) $2 Nothing $3 $5 }

type : expr { $1 }

caseBranch : pattern '->' expr { ($1, $3) }

pattern :: { Pattern Parsed }
pattern : identLoc                                                      { VarPat (fst $1) (snd $1) }
        | pattern '|' pattern                                           { OrPat (merge $1 $3) $1 $3 }
        | '(' pattern ')'                                               { $2 }
        | '(' pattern ',' pattern ')'                                   { TuplePat (merge $1 $5) [$2, $4] }
        | '(' pattern ',' pattern ',' sepTrailingList(',', pattern) ')' { TuplePat (merge $1 $7) (fromList ($2 : $4 : $6)) }

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