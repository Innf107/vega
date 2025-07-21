{-# LANGUAGE UndecidableInstances #-}

module Vega.TypeCheck.Zonk (Zonkable, zonk) where

import Relude hiding (Type)
import Vega.Syntax

import Data.Unique (Unique)
import Effectful (Eff, IOE, (:>))
import GHC.Generics (Generic)
import GHC.Generics qualified as Generics
import Vega.Error (TypeError, TypeErrorSet)
import Vega.Loc (Loc)

class Zonkable a where
    default zonk :: (IOE :> es) => (Generic a, ZonkableGeneric (Generics.Rep a)) => a -> Eff es a
    zonk :: (IOE :> es) => a -> Eff es a
    zonk x = Generics.to <$> zonkGeneric (Generics.from x)

class ZonkableGeneric f where
    zonkGeneric :: (IOE :> es) => f x -> Eff es (f x)

instance ZonkableGeneric Generics.V1 where
    zonkGeneric = \case {}

instance ZonkableGeneric Generics.U1 where
    zonkGeneric Generics.U1 = pure Generics.U1

instance (ZonkableGeneric f) => ZonkableGeneric (Generics.M1 _a _b f) where
    zonkGeneric (Generics.M1 x) = Generics.M1 <$> zonkGeneric x

instance (Zonkable a) => ZonkableGeneric (Generics.K1 _rec a) where
    zonkGeneric (Generics.K1 x) = Generics.K1 <$> zonk x

instance (ZonkableGeneric f, ZonkableGeneric g) => ZonkableGeneric (f Generics.:+: g) where
    zonkGeneric (Generics.L1 x) = Generics.L1 <$> zonkGeneric x
    zonkGeneric (Generics.R1 x) = Generics.R1 <$> zonkGeneric x

instance (ZonkableGeneric f, ZonkableGeneric g) => ZonkableGeneric (f Generics.:*: g) where
    zonkGeneric (x Generics.:*: y) = liftA2 (Generics.:*:) (zonkGeneric x) (zonkGeneric y)

newtype ZonkIgnored a = ZonkIgnored a

instance Zonkable (ZonkIgnored a) where
    zonk = pure

instance Zonkable Type where
    zonk type_ = do
        firstLevel <- followMetas type_
        coerce <$> zonk (Generics.Generically firstLevel)

instance (Generic a, ZonkableGeneric (Generics.Rep a)) => Zonkable (Generics.Generically a) where
    zonk (Generics.Generically x) = Generics.Generically . Generics.to <$> zonkGeneric (Generics.from x)

instance (Zonkable a) => Zonkable (Seq a) where
    zonk seq = traverse zonk seq

instance (Zonkable a) => Zonkable (Maybe a)

instance Zonkable MetaVar where
    zonk (MkMetaVar{kind, identity, underlying, name}) = do
        -- We do *not* zonk the underlying type this is bound to
        -- since that case is already handled by Zonkable Type.
        -- In fact, if we even get to this case, that means
        -- that underlying is set to Nothing
        kind <- zonk kind
        pure MkMetaVar{kind, identity, underlying, name}

instance Zonkable ForallBinder
instance Zonkable Skolem
instance Zonkable TypeError
instance Zonkable TypeErrorSet

deriving via ZonkIgnored BinderVisibility instance Zonkable BinderVisibility
deriving via ZonkIgnored Monomorphization instance Zonkable Monomorphization
deriving via ZonkIgnored LocalName instance Zonkable LocalName
deriving via ZonkIgnored GlobalName instance Zonkable GlobalName
deriving via ZonkIgnored Name instance Zonkable Name
deriving via ZonkIgnored Unique instance Zonkable Unique
deriving via ZonkIgnored Loc instance Zonkable Loc
deriving via ZonkIgnored Int instance Zonkable Int