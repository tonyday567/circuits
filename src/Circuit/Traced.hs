{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

-- | Trace typeclass, Circuit GADT, and instances for feedback in circuits.
--
-- Supports any base arrow with different tensor types (,) and Either.
-- Includes delimited-continuation implementation for Kleisli IO.

module Circuit.Traced
  ( Trace (..),
    PromptTag,
    newPromptTag,
    prompt,
    control0,
  )
where

import Control.Arrow (Kleisli (..))
import GHC.Exts (PromptTag#, newPromptTag#, prompt#, control0#)
import GHC.IO (IO (..))

-- | A traced profunctor over tensor @t@.
--
-- This class packages strength and co-strength operations equivalent to
-- those in the @profunctors@ package, with the tensor parameterised:
--
-- @
--   Trace p (,)     ≅  Strong p + Costrong p
--     where untrace = first'    and  trace = unfirst
--
--   Trace p Either  ≅  Choice p + Cochoice p
--     where untrace = left'     and  trace = unleft
-- @
--
-- Users who want to plug @profunctors@-shaped types into Circuit can
-- write the bridge instance themselves; we don't depend on @profunctors@
-- here to keep the library at @base@ only.
class Trace arr t where
  trace :: arr (t a b) (t a c) -> arr b c
  untrace :: arr b c -> arr (t a b) (t a c)

instance {-# OVERLAPPABLE #-} Trace (->) (,) where
  trace f b = let (a, c) = f (a, b) in c
  untrace = fmap

instance {-# OVERLAPPING #-} Trace (->) Either where
  trace f b = go (Right b)
    where
      go x = case f x of
        Right c -> c
        Left a -> go (Left a)
  untrace = fmap

data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: IO (PromptTag a)
newPromptTag = IO \s ->
  case newPromptTag# s of
    (# s', t #) -> (# s', PromptTag t #)

prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag t) (IO m) = IO (prompt# t m)

-- | Captures the continuation up to the nearest prompt with the matching tag.
--
--   The continuation k, when called with a value, returns to the prompt
--   and resumes from there (−F− semantics).
control0 :: forall a b. PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag t) f = IO (control0# t arg)
  where
    arg f# s = case f (\(IO x) -> IO (f# x)) of IO m -> m s

-- | Trace for Kleisli IO with Either tensor using delimited continuations.
--
--   The key: prompt is inside the loop, so every iteration re-establishes
--   the boundary. When control0 fires, it jumps back to the nearest prompt.
instance {-# OVERLAPPING #-} Trace (Kleisli IO) Either where
  trace (Kleisli body) = Kleisli \initial -> do
    tag <- newPromptTag
    let
      loop x = prompt tag $
        body x >>= \case
          Right c -> pure c
          Left a  -> control0 tag \k -> k (loop (Left a))
    loop (Right initial)

  untrace (Kleisli f) = Kleisli \case
    Left a  -> pure (Left a)
    Right b -> Right <$> f b
