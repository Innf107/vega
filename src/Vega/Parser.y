{
{-# LANGUAGE NoStrictData #-}
module Vega.Parser where

import Prelude
import Vega.Prelude (Generic, fromList, Text, Vector, Seq((:|>), (:<|)))
import Vega.Lexer (Token(..), TokenClass(..))
import Vega.Syntax

import Vega.Loc (HasLoc(..), merge)
import Vega.Pretty
import Vega.Util (viaList)

import Debug.Trace (trace)

import Data.Vector qualified as Vector
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
    '**'            { MkToken DOUBLESTAR _ }
    ','             { MkToken COMMA _ }
    ';'             { MkToken SEMI _ }
    '|'             { MkToken PIPE _ }
    'let'           { MkToken LET _ }
    'case'          { MkToken CASE _ }
    'forall'        { MkToken FORALL _ }
    'data'          { MkToken DATA _ }
    '+'             { MkToken PLUS _ }
    '-'             { MkToken MINUS _ }
    '*'             { MkToken STAR _ }
    '//'            { MkToken DOUBLESLASH _ }
    eof             { MkToken EOF _ }


%%

ident :: { Text }
ident : identLoc { snd $1 }

int :: { Integer }
int : intLoc { snd $1 }

string :: { Text }
string : stringLoc { snd $1 }


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
      ident patterns '=' expr
        {% if snd $1 /= $5 then
            parseError (MismatchedDeclarationName { loc = merge $1 $8, signature = snd $1, definition = $5 })
           else
            pure $ DefineFunction (fst $1) (snd $1) $3 $6 $8 }
    | 'data' ident':' expr_leaf_no_block '{' sepTrailing(';', dataConstructor) '}'
        { DefineGADT(merge $1 $4) $2 $4 $6 }

dataConstructor :: { (Text, SourceType Parsed) }
dataConstructor : ident ':' type { ($1, $3) }

expr :: { Expr Parsed }
expr : expr_op_tuple '->' expr 
        -- Pi types and type ascriptions are horribly ambiguous, so we don't parse pi types directly
        -- but instead convert any function with a type ascription to a variable as the domain to a pi type *afterwards*
        { case $1 of
            Ascription _ (Var _ name) type_ -> EPi (merge $1 $3) (Just name) type_ $3
            _ -> EPi (merge $1 $3) Nothing $1 $3 }
     | expr_ascription                      { $1 }

expr_ascription :: { Expr Parsed }
expr_ascription : expr_op_tuple ':' expr     { Ascription (merge $1 $3) $1 $3 }
                | expr_op_tuple              { $1 }

expr_op_tuple :: { Expr Parsed }
expr_op_tuple : tuple_type_arguments { 
    case $1 of
        (first :<| (_ :|> last)) -> ETupleType (merge first last) (viaList $1)
        [first] -> first
        [] -> error "expr_op_tuple parsed an empty list"
    }

tuple_type_arguments :: { Seq (Expr Parsed) }
tuple_type_arguments : expr_op_add '**' tuple_type_arguments { $1 :<| $3 }
                     | expr_op_add                           { [$1] }

expr_op_add :: { Expr Parsed }
expr_op_add : expr_op_add '+' expr_op_mul        { binop (merge $1 $3) $2 $1 Add $3 }
           | expr_op_add '-' expr_op_mul         { binop (merge $1 $3) $2 $1 Subtract $3 }
           | expr_op_mul                         { $1 }

expr_op_mul :: { Expr Parsed }
expr_op_mul : expr_op_mul '*' expr_app        { binop (merge $1 $3) $2 $1 Multiply $3 }
            | expr_op_mul '//' expr_app       { binop (merge $1 $3) $2 $1 IntDivide $3 }
            | expr_app                     { $1 }

expr_app :: { Expr Parsed }
expr_app : expr_app expr_leaf   { App (merge $1 $2) $1 $2 }
         | expr_leaf            { $1 }

expr_leaf :: { Expr Parsed }
expr_leaf : expr_leaf_no_block                          { $1 }
          | '{' sepTrailing(';', statement) '}'         { Sequence (merge $1 $3) $2 }


expr_leaf_no_block :: { Expr Parsed }
expr_leaf_no_block
    : identLoc                                    { Var (fst $1) (snd $1) }
    -- TODO: this should include the locations from the '(' ')' or error messages for
    -- applications are going to miss the final ')'
    | '(' expr ')'                                { $2 }
    | '(' ')'                                     { TupleLiteral (merge $1 $2) [] }
    | '(' expr ',' sepTrailingList(',', expr) ')' { TupleLiteral (merge $1 $5) (fromList ($2 : $4)) }
    | '\\' patterns1 '->' expr                    { foldr (\pattern_ expr -> Lambda (merge $1 $4) pattern_ expr) $4 $2 }
    | 'case' expr_leaf '{' 
        sepTrailing(';', caseBranch)
    '}'                                           { Case (merge $1 $5) $2 $4 }
    | literal                                     { Literal (fst $1) (snd $1) }
    -- Not sure about this syntax yet to be honest
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
          | 'let' patternLeaf '=' expr              { Let (merge $1 $4) $2 $4 }
          | 'let' ident ':' type ';' 
            'let' ident patterns '=' expr  {%
                if $2 == $7 then
                    pure $ LetFunction (merge $1 $10) $2 (Just $4) $8 $10
                else
                    -- TODO: This should probably report a smaller location to avoid turning *everything* red in an LSP
                    parseError (MismatchedDeclarationName { loc = merge $1 $10, signature = $2, definition = $7 })
                }
          | 'let' ident patterns '=' expr  { LetFunction (merge $1 $5) $2 Nothing $3 $5 }

type : expr { $1 }

caseBranch : pattern '->' expr { ($1, $3) }

pattern :: { Pattern Parsed }
pattern : identLoc many1(patternLeaf) { ConstructorPat (merge (fst $1) (Vector.last $2)) (snd $1) $2 }
        | pattern '|' patternLeaf     { OrPat (merge $1 $3) $1 $3 }
        | patternLeaf                 { $1 }

patternLeaf :: { Pattern Parsed }
patternLeaf : identLoc                                                      { VarPat (fst $1) (snd $1) }
            | intLoc                                                        { IntPat (fst $1) (snd $1) }
            | stringLoc                                                     { StringPat (fst $1) (snd $1) }
            | '(' pattern ':' expr ')'                                      { TypePat (merge $1 $5) $2 $4 }
            | '(' pattern ')'                                               { $2 }
            | '(' pattern ',' pattern ')'                                   { TuplePat (merge $1 $5) [$2, $4] }
            | '(' pattern ',' pattern ',' sepTrailingList(',', pattern) ')' { TuplePat (merge $1 $7) (fromList ($2 : $4 : $6)) }

patterns :: { Vector (Pattern Parsed) }
patterns : many(patternLeaf) { $1 }

patterns1 :: { Vector (Pattern Parsed) }
patterns1 : many1(patternLeaf) { $1 }


{
binop :: HasLoc opLoc => Loc -> opLoc -> Expr Parsed -> Primop -> Expr Parsed -> Expr Parsed
binop loc op arg1 primop arg2 = App loc (App loc (Primop (getLoc op) primop) arg1) arg2

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
parseErrorFrom (token : _) = parseError (ParseError (getLoc token))
}