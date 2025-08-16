module Vega.Compilation.Core.Syntax where

import Data.Unique (Unique)
import Relude
import Vega.Pretty
import Vega.Syntax (GlobalName)
import Vega.Syntax qualified as Vega

data CoreName
    = Global GlobalName
    | Local {-# UNPACK #-} LocalCoreName
    deriving (Generic, Eq, Hashable)

data LocalCoreName
    = UserProvided Vega.LocalName
    | Generated Unique
    deriving (Generic, Eq, Hashable)

-- TODO: representations?
data Declaration
    = DefineFunction GlobalName (Seq LocalCoreName) (Seq Statement) Expr

data Expr
    = Value Value
    | Application CoreName (Seq Value)
    | -- INVARIANT: JumpJoin never occurs in a let
      JumpJoin LocalCoreName
    | Lambda (Seq LocalCoreName) (Seq Statement) Expr
    | ConstructorCase Value (HashMap CoreName (Seq LocalCoreName, Seq Statement, Expr))

data Statement
    = Let LocalCoreName Expr
    | LetJoin LocalCoreName (Seq LocalCoreName) (Seq Statement) Expr

data Value
    = Var CoreName
    | Literal Literal
    | DataConstructorApplication DataConstructor (Seq Value)

data DataConstructor
    = UserDefinedConstructor GlobalName
    | TupleConstructor {size :: Int}

instance Pretty Value where
    pretty = \case
        _ -> undefined

data Literal
    = IntLiteral Integer
    | DoubleLiteral Rational
    | StringLiteral Text

nameToCoreName :: Vega.Name -> CoreName
nameToCoreName = \case
    Vega.Local localName -> Local (UserProvided localName)
    Vega.Global globalName -> Global globalName
