module Vega.Compilation.JavaScript.Language where

import Relude

type Name = Text

data Statement
    = Const Name Expr
    | Function Name (Seq Name) Expr

data Expr
    