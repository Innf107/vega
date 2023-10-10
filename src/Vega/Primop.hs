module Vega.Primop (
    PrimopType (..),
    primopDefinitions,
    primopFromName,
    primopType,
    ContextFromEmpty (..),
) where

import Vega.Prelude
import Vega.Syntax

import Vega.Name qualified as Name

class ContextFromEmpty context where
    emptyContext :: context

newtype PrimopType = WrapPrimopType {type_ :: forall context. (ContextFromEmpty context) => ValueF context}

primopDefinitions :: [(Text, Primop, PrimopType)]
primopDefinitions =
    [
        ( "debug"
        , Debug
        , WrapPrimopType (forallV "a" Type \a -> CVar a --> unitType)
        )
    ]

primopNameMap :: Map Text (Primop, PrimopType)
primopNameMap = fromList (map (\(name, primop, type_) -> (name, (primop, type_))) primopDefinitions)

primopTypeMap :: Map Primop PrimopType
primopTypeMap = fromList (map (\(_, primop, type_) -> (primop, type_)) primopDefinitions)

primopFromName :: Text -> Maybe (Primop, PrimopType)
primopFromName name = lookup name primopNameMap

primopType :: Primop -> PrimopType
primopType primop = case lookup primop primopTypeMap of
    Nothing -> error ("primop without definition: " <> show primop)
    Just primopType -> primopType

type_ :: CoreExprF context
type_ = CLiteral TypeLit

unitType :: CoreExprF context
unitType = CTupleType (fromList [])

forallV
    :: (ContextFromEmpty context)
    => Text
    -> ValueF context
    -> (Name -> CoreExprF context)
    -> ValueF context
forallV textName type_ cont = do
    let name = Name.internal textName
    Forall name type_ (cont name, emptyContext)

forall :: Text -> CoreExprF context -> (Name -> CoreExprF context) -> CoreExprF context
forall textName type_ cont = do
    let name = Name.internal textName
    CForall name type_ (cont name)

(-->) :: CoreExprF context -> CoreExprF context -> CoreExprF context
x --> y = CPi Nothing x y
