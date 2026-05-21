module Vega.ListBuilder (ListBuilder, singleton, toList) where

import Relude hiding (toList)

data ListBuilder a
    = -- INVARIANT: Empty never occurs nested
      Empty
    | One a
    | Concat (ListBuilder a) (ListBuilder a)

instance Semigroup (ListBuilder a) where
    Empty <> x = x
    x <> Empty = x
    x <> y = Concat x y

instance Monoid (ListBuilder a) where
    mempty = Empty

singleton :: a -> ListBuilder a
singleton x = One x

toList :: ListBuilder a -> [a]
toList builder = go [] builder
  where
    go built = \case
        Empty -> built
        One x -> x : built
        Concat left right -> do
            let builtRight = go built right
            go builtRight left