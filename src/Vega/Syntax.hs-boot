module Vega.Syntax where

import Relude hiding (NonEmpty, Type)
import Vega.MultiSet (MultiSet)
import Vega.Seq.NonEmpty (NonEmpty)
import Vega.VectorMap (VectorMap)

data Type
    = TypeConstructor Name
    | TypeApplication Type (Seq Type)
    | TypeVar LocalName
    | Forall (NonEmpty ForallBinder) Type
    | Exists (NonEmpty (LocalName, Kind)) Type
    | Function (Seq Type) Effect Type
    | TypeFunction (Seq Type) Type
    | Tuple (Seq Type)
    | Record (VectorMap Text Type)
    | MetaVar MetaVar
    | Skolem Skolem
    | Pure
    | IntSum IntSum
    | -- Kinds
      Rep
    | Type Kind
    | Effect
    | Integer
    | Kind
    | -- Representations
      SumRep (Seq Type)
    | ProductRep (Seq Type)
    | ArrayRep Type -- TODO: this should really be an AbstractRep (just like the primitiveReps)
    | PrimitiveRep PrimitiveRep

data MetaVar
data Skolem
type Kind = Type
type Effect = Type
data LocalName
data Name
data ForallBinder
data PrimitiveRep

data IntSum = MkIntSum
    { literal :: IORef Int
    , metas :: IORef (MultiSet MetaVar)
    , skolems :: IORef (MultiSet Skolem)
    , variables :: IORef (MultiSet LocalName)
    }

instance Ord MetaVar
instance Ord Skolem
instance Ord LocalName
