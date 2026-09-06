{-# LANGUAGE CPP #-}

module Vega.Panic (
    panic,
    Panic (..),
    prettyCallStack,
    assert,
    assertIn,
    assertWith,
    assertWithIn,
    assertM,
) where

import Control.Exception (throw)
import GHC.Base qualified as GHC.Base
import Relude hiding (prettyCallStack)
import Relude qualified
import Vega.Pretty (Ann, Doc)
import Vega.Pretty qualified as Pretty

data Panic = Panic CallStack (Doc Ann)
    deriving stock (Show)
    deriving anyclass (Exception)

panic :: (HasCallStack) => Doc Ann -> a
panic doc = throw (Panic callStack doc)

prettyCallStack :: CallStack -> Doc Ann
prettyCallStack callStack = Pretty.align (Pretty.note $ toText $ Relude.prettyCallStack callStack)

{-# INLINE assertWith #-}
assertWith :: (HasCallStack, Applicative f) => Bool -> Doc Ann -> f ()
assertWith ~condition message = assertWithIn condition message (pure ())

{-# INLINE assertWithIn #-}
assertWithIn :: (HasCallStack) => Bool -> Doc Ann -> a -> a
#ifdef __GLASGOW_HASKELL_ASSERTS_IGNORED__
assertWithIn _ _ x = x
#else
assertWithIn condition ~message x = case condition of
    True -> x
    False -> panic $ Pretty.errorText "Assertion failed: " <> message
#endif

{-# INLINE assert #-}
assert :: (HasCallStack, Applicative f) => Bool -> f ()
assert ~condition = GHC.Base.assert condition (pure ())

{-# INLINE assertIn #-}
assertIn :: (HasCallStack) => Bool -> a -> a
assertIn = GHC.Base.assert

{- | Assert in debug mode that some condition holds.
For this to be safe, the condition must not have any
side effects that are observable from the outside.

It should primarily be used with (possibly expensive) lookups
in mutable data structures.
-}
{-# INLINE assertM #-}
assertM :: (HasCallStack, Monad m) => m Bool -> m ()
#ifdef __GLASGOW_HASKELL_ASSERTS_IGNORED__
assertM _ = pure ()
#else
assertM condition = do
    condition >>= \case
        True -> pure ()
        False -> panic $ Pretty.errorText "Assertion failed"
#endif