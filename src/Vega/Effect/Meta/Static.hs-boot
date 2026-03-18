module Vega.Effect.Meta.Static where

import Relude hiding (trace)

import Effectful (Dispatch (Static), DispatchOf, Eff, Effect, IOE, (:>))

import Effectful.Dispatch.Static (SideEffects (NoSideEffects, WithSideEffects), StaticRep, evalStaticRep, unsafeEff_)
import Vega.Effect.Trace (Category (MetaVars), Trace, trace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique)
import Vega.Pretty (Pretty (pretty), align, keyword, note, (<+>))
import {-# SOURCE #-} Vega.Syntax qualified as Vega

data ReadMeta :: Effect
type role ReadMeta phantom phantom

data BindMeta :: Effect
type role BindMeta phantom phantom

readMeta :: (ReadMeta :> es) => Vega.MetaVar -> Eff es (Maybe Vega.Type)
bindMetaUnchecked :: (BindMeta :> es) => Vega.MetaVar -> Vega.Type -> Eff es ()
freshMeta :: (BindMeta :> es, NewUnique :> es, Trace :> es, HasCallStack) => Text -> Vega.Kind -> Eff es Vega.MetaVar
runMeta :: (IOE :> es) => Eff (ReadMeta : BindMeta : es) a -> Eff es a
runReadMetaPure :: Eff (ReadMeta : es) a -> Eff es a
followMetas :: (ReadMeta :> es, BindMeta :> es) => Vega.Type -> Eff es Vega.Type
followMetasWithoutPathCompression :: (ReadMeta :> es) => Vega.Type -> Eff es Vega.Type
