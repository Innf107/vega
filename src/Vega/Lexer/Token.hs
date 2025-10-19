module Vega.Lexer.Token (Token (..)) where

import Relude
import Vega.Pretty (Pretty)
import Vega.Pretty qualified as Pretty

data Token
    = EOF
    | Ident Text
    | Constructor Text
    | StringLiteral Text
    | IntLiteral Integer
    | FloatLiteral Rational
    | LParen
    | RParen
    | LBracket
    | RBracket
    | LBrace
    | RBrace
    | Lambda
    | DoubleEqual
    | Equals
    | Arrow
    | EffArrowStart
    | EffArrowEnd
    | DoubleColon
    | Colon
    | Semicolon
    | Comma
    | Period
    | Pipe
    | Let
    | Data
    | Forall
    | Exists
    | As
    | DoubleAmpersand
    | DoublePipe
    | Less
    | LessEqual
    | NotEqual
    | Greater
    | GreaterEqual
    | Asterisk
    | Slash
    | Plus
    | Minus
    | If
    | Then
    | Else
    | Match
    | Underscore
    | Use
    | Import
    deriving (Show, Eq, Ord, Generic)

instance Pretty Token where
    pretty = \case
        EOF -> Pretty.plain "end of input"
        Ident ident -> Pretty.localIdentText ident
        Constructor constr -> Pretty.localConstructorText constr
        StringLiteral literal -> Pretty.literal ("\"" <> literal <> "\"")
        IntLiteral int -> Pretty.number int
        FloatLiteral rational -> undefined
        LParen -> Pretty.keyword "("
        RParen -> Pretty.keyword ")"
        LBracket -> Pretty.keyword "["
        RBracket -> Pretty.keyword "]"
        LBrace -> Pretty.keyword "{"
        RBrace -> Pretty.keyword "}"
        Lambda -> Pretty.keyword "\\"
        DoubleEqual -> Pretty.keyword "=="
        Equals -> Pretty.keyword "="
        Arrow -> Pretty.keyword "->"
        EffArrowStart -> Pretty.keyword "-{"
        EffArrowEnd -> Pretty.keyword "}>"
        DoubleColon -> Pretty.keyword "::"
        Colon -> Pretty.keyword ":"
        Semicolon -> Pretty.keyword ";"
        Comma -> Pretty.keyword ","
        Period -> Pretty.keyword "."
        Pipe -> Pretty.keyword "|"
        Let -> Pretty.keyword "let"
        Data -> Pretty.keyword "data"
        Forall -> Pretty.keyword "forall"
        Exists -> Pretty.keyword "exists"
        As -> Pretty.keyword "as"
        DoubleAmpersand -> Pretty.keyword "&&"
        DoublePipe -> Pretty.keyword "||"
        Less -> Pretty.keyword "<"
        LessEqual -> Pretty.keyword "<="
        NotEqual -> Pretty.keyword "!="
        Greater -> Pretty.keyword ">"
        GreaterEqual -> Pretty.keyword ">="
        Asterisk -> Pretty.keyword "*"
        Slash -> Pretty.keyword "/"
        Plus -> Pretty.keyword "+"
        Minus -> Pretty.keyword "-"
        If -> Pretty.keyword "if"
        Then -> Pretty.keyword "then"
        Else -> Pretty.keyword "else"
        Match -> Pretty.keyword "match"
        Underscore -> Pretty.keyword "_"
        Use -> Pretty.keyword "use"
        Import -> Pretty.keyword "import"
