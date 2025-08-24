module Vega.Disambiguate (
    Disambiguate,
    new,
    disambiguate,
    disambiguate0,
) where

import Relude
import Relude.Extra

import Control.Monad.ST.Strict (ST)
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import Data.Unique (Unique)

newtype Disambiguate s = MkDisambiguate {contents :: STRef s (Map Text (Map Unique Int))}

new :: ST s (Disambiguate s)
new = MkDisambiguate <$> newSTRef mempty

disambiguate :: Disambiguate s -> Text -> Unique -> ST s Text
disambiguate dis name unique = do
    nameMap <- readSTRef dis.contents
    case lookup name nameMap of
        Nothing -> do
            writeSTRef dis.contents (insert name (fromList [(unique, 0)]) nameMap)
            pure name
        Just previousUniques -> case lookup unique previousUniques of
            Nothing -> do
                let id = length previousUniques
                writeSTRef dis.contents (insert name (insert unique id previousUniques) nameMap)
                pure $ name <> show id
            Just 0 -> pure name
            Just id -> pure $ name <> show id

-- | Like disambiguate but includes a `0` for the first entry
disambiguate0 :: Disambiguate s -> Text -> Unique -> ST s Text
disambiguate0 dis name unique = do
    disambiguated <- disambiguate dis name unique
    if disambiguated == name
        then
            pure $ name <> "0"
        else
            pure disambiguated