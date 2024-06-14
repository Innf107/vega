module Vega.Compile.MIR (Declaration (..), Expr (..), Statement (..), Cont (..), Literal (..)) where

import Vega.Prelude

import Vega.Name (Name)
import Vega.Syntax (Primop)

data Statement
    = -- | Applications are represented in uncurried form but we
      -- still support partial application at this stage
      App Expr (Seq Expr) Cont
      -- Continuing lambdas is just equivalent to a let so we only need to care
      -- about continuing variable continuations in the AST
    | Continue Name Expr
    | Let Name Expr Statement
    | IntCase Expr (Vector (Integer, Cont)) (Maybe (Name, Cont))
    | ConstructorCase Expr (Vector (Name, Vector Name, Cont))

data Cont
    = ContVar Name
    | ContLambda Name Statement

data Literal
    = IntLit Integer
    | StringLit Text
    | UnitLit

data Declaration
    = DefineVar Name Expr
 
data Expr
    = Var Name
    | -- | Lambdas are represented in uncurried form with an additional continuation argument.
      Lambda (Seq Name) Name Statement
    | Literal Literal
    | TupleLiteral (Vector Expr)
    | DataConstructor Name (Vector Expr)
    | PrimopApp Primop (Seq Expr)
