module Vega.Compile.MIR (Declaration (..), Expr (..), Statement (..), Cont (..), Literal (..)) where

import Vega.Prelude

import Vega.Name (Name)

data Expr
    = Var Name
    | PureApp Expr Expr
    | PureLambda Name Expr
    | Literal Literal
    | Let Name Expr Expr

data Statement
    = ImpureApp Expr Expr Cont
    | ImpureLambda {varName :: Name, contName :: Name, body :: Statement}
    | LetStatement Name Expr Statement

data Cont
    = ContVar Name
    | ContLambda Name Statement

data Literal
    = IntLit Integer
    | UnitLit

data Declaration
    = DefineVar Name Expr
