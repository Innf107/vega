module Vega.Compilation.Core where

import Relude
import Vega.Syntax (GlobalName, LocalName)

data CoreDeclaration
    = DefineFunction GlobalName (Seq LocalName) Expr

data Expr
    = Var LocalName

