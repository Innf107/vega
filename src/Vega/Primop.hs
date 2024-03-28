module Vega.Primop (
    PrimopType (..),
    primopDefinitions,
    primopFromName,
    primopType,
    primopArity,
    ContextFromEmpty (..),
) where

import Vega.Prelude
import Vega.Syntax

import Vega.Name qualified as Name

class ContextFromEmpty context where
    emptyContext :: context

newtype PrimopType = WrapPrimopType {type_ :: forall context. (ContextFromEmpty context) => ValueF context}

primopDefinitions :: [(Text, Primop, Int, PrimopType)]
primopDefinitions =
    [
        ( "debug"
        , Debug
        , 1
        , WrapPrimopType (forallV "a" Type \a -> CVar a --> unitType)
        )
    ,
        ( "+"
        , Add
        , 2
        , WrapPrimopType (Int +--> intType --> intType)
        )
    ,
        ( "-"
        , Subtract
        , 2
        , WrapPrimopType (Int +--> intType --> intType)
        )
    ,
        ( "*"
        , Multiply
        , 2
        , WrapPrimopType (Int +--> intType --> intType)
        )
    ,
        ( "//"
        , IntDivide
        , 2
        , WrapPrimopType (Int +--> intType --> intType)
        )
    ]

primopNameMap :: Map Text (Primop, Int, PrimopType)
primopNameMap = fromList (map (\(name, primop, arity, type_) -> (name, (primop, arity, type_))) primopDefinitions)

primopTypeMap :: Map Primop (Int, PrimopType)
primopTypeMap = fromList (map (\(_, primop, arity, type_) -> (primop, (arity, type_))) primopDefinitions)

primopFromName :: Text -> Maybe (Primop, Int, PrimopType)
primopFromName name = lookup name primopNameMap

primopType :: Primop -> PrimopType
primopType primop = case lookup primop primopTypeMap of
    Nothing -> error ("primop without definition: " <> show primop)
    Just (_arity, primopType) -> primopType

primopArity :: Primop -> Int
primopArity primop = case lookup primop primopTypeMap of
    Nothing -> error ("primop without definition: " <> show primop)
    Just (arity, _primopType) -> arity

_type_ :: CoreExprF context
_type_ = CLiteral TypeLit

unitType :: CoreExprF context
unitType = CTupleType (fromList [])

intType :: CoreExprF context
intType = CLiteral IntTypeLit

forallV
    :: (ContextFromEmpty context)
    => Text
    -> ValueF context
    -> (Name -> CoreExprF context)
    -> ValueF context
forallV textName type_ cont = do
    let name = Name.internal textName
    Forall name type_ (cont name, emptyContext)

_forall_ :: Text -> CoreExprF context -> (Name -> CoreExprF context) -> CoreExprF context
_forall_ textName type_ cont = do
    let name = Name.internal textName
    CForall name type_ (cont name)

(-->) :: CoreExprF context -> CoreExprF context -> CoreExprF context
x --> y = CPi Nothing x y
infixr 1 -->

(+-->) :: (ContextFromEmpty context) => ValueF context -> CoreExprF context -> ValueF context
x +--> y = Pi Nothing x (y, emptyContext)
infixr 0 +-->