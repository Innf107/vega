module Vega.Compilation.MIR where

import Data.Unique (Unique)
import Relude
import Vega.Compilation.Shape (Shape)

newtype Local = Local Unique

data Program = MkProgram
    { functions :: Seq FunctionDefinition
    }

data ParameterShape
    = Fixed Shape
    | Polymorphic

data FunctionDefinition = FunctionDefinition
    { parameters :: Seq ParameterShape
    , result :: ParameterShape
    , body :: Expr
    }

data Expr
    = Let Local Expr Expr
    | Match
        { scrutinee :: Local
        , cases :: Undefined
        }
    | Var Local
    | Application Local (Seq Local)
    | Literal Literal

data Literal
    = StringLiteral Text
    | IntLiteral Integer
    | DoubleLiteral Rational
