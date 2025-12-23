{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Vega.Effect.Meta.Static (
    ReadMeta,
    BindMeta,
    readMeta,
    bindMetaUnchecked,
    freshMeta,
    runMeta,
    runReadMetaPure,
    followMetas,
    followMetasWithoutPathCompression,
) where

import Relude hiding (trace)

import Effectful (Dispatch (Static), DispatchOf, Eff, Effect, IOE, (:>))

import Effectful.Dispatch.Static (SideEffects (NoSideEffects, WithSideEffects), StaticRep, evalStaticRep, unsafeEff_)
import Vega.Effect.Trace (Category (MetaVars), Trace, trace)
import Vega.Effect.Unique.Static.Local (NewUnique, newUnique)
import Vega.Pretty (Pretty (pretty), align, keyword, note, (<+>))
import Vega.Syntax qualified as Vega

data ReadMeta :: Effect
data BindMeta :: Effect

type instance DispatchOf ReadMeta = Static NoSideEffects
type instance DispatchOf BindMeta = Static WithSideEffects
data instance StaticRep ReadMeta = ReadMeta
data instance StaticRep BindMeta = BindMeta

readMeta :: (ReadMeta :> es) => Vega.MetaVar -> Eff es (Maybe Vega.Type)
readMeta metavar = unsafeEff_ $ readIORef metavar.underlying

bindMetaUnchecked :: (BindMeta :> es) => Vega.MetaVar -> Vega.Type -> Eff es ()
bindMetaUnchecked metavar type_ = unsafeEff_ $ writeIORef metavar.underlying (Just type_)

freshMeta :: (BindMeta :> es, NewUnique :> es, Trace :> es, HasCallStack) => Text -> Vega.Kind -> Eff es Vega.MetaVar
freshMeta name kind = do
    identity <- newUnique
    underlying <- unsafeEff_ $ newIORef Nothing
    let meta = Vega.MkMetaVar{underlying, identity, name, kind}
    trace MetaVars ("freshMeta" <+> align (keyword "~>" <+> pretty meta <+> keyword ":" <+> pretty kind <> "\n" <> note (toText $ prettyCallStack callStack)))
    pure meta

runMeta :: (IOE :> es) => Eff (ReadMeta : BindMeta : es) a -> Eff es a
runMeta eff = evalStaticRep BindMeta $ evalStaticRep ReadMeta eff

{- | Allow reading from meta variables in a pure context. This is only safe if there are definitely
    not going to be any modifications to the meta variables during the execution of this code.

If this invariant is not satisfied, pure code might be able to observe mutations of meta variable
and might behave strangely with optimizations.
Unlike unsafePerformIO, this function *CANNOT* violate soundness.
-}
runReadMetaPure :: Eff (ReadMeta : es) a -> Eff es a
runReadMetaPure eff = evalStaticRep ReadMeta eff

followMetas :: (ReadMeta :> es, BindMeta :> es) => Vega.Type -> Eff es Vega.Type
followMetas = \case
    type_@(Vega.MetaVar meta) -> do
        readMeta meta >>= \case
            Nothing -> pure type_
            Just replacement -> do
                actualType <- followMetas replacement
                -- path compression
                bindMetaUnchecked meta actualType

                pure actualType
    type_ -> pure type_

followMetasWithoutPathCompression :: (ReadMeta :> es) => Vega.Type -> Eff es Vega.Type
followMetasWithoutPathCompression = \case
    type_@(Vega.MetaVar meta) -> do
        readMeta meta >>= \case
            Nothing -> pure type_
            Just replacement -> followMetasWithoutPathCompression replacement
    type_ -> pure type_
