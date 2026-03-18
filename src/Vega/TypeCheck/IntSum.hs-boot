module Vega.TypeCheck.IntSum where

import Effectful (Eff, (:>))
import Relude
import {-# SOURCE #-} Vega.Effect.Meta.Static (BindMeta, ReadMeta)
import Vega.MultiSet (MultiSet)
import {-# SOURCE #-} Vega.Syntax qualified as Vega

readIntSumNonDestructive :: (ReadMeta :> es) => Vega.IntSum -> Eff es (Int, MultiSet Vega.MetaVar, MultiSet Vega.Skolem, MultiSet Vega.LocalName)
readIntSum :: (ReadMeta :> es, BindMeta :> es) => Vega.IntSum -> Eff es (Int, MultiSet Vega.MetaVar, MultiSet Vega.Skolem, MultiSet Vega.LocalName)
