{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}

-- | Tensorial strength for a tensor @t@ inside a category @arr@.
--
-- 'strength' tensors a plain morphism with a feedback wire. It is the
-- strength structure that 'Circuit.Trace.Traced' categories inherit as a
-- superclass, and it is all that is needed to compose 'Circuit.Trace.Loop'
-- syntax: 'trace' is only required when a knot is eliminated by 'run' or
-- 'bind'.
module Circuit.Strength
  ( Strength (..),
    strengthD,
  )
where

import Circuit.Category (Category (..), Discrete (..))
import Circuit.Channel (Channel (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- | Tensorial strength for a tensor @t@ inside a category @arr@.
--
-- 'strength' opens a feedback loop, tensoring a plain morphism with the
-- feedback channel. It is /not/ a syntactic inverse of
-- 'Circuit.Trace.trace'; it is the strength ("tensorial strength") of the
-- tensor @t@ acting on morphisms.
class (Channel t arr) => Strength t arr where
  strength ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (t a c)
    ) =>
    arr b c ->
    arr (t a b) (t a c)

-- | Discrete 'strength': discharge 'Ob' constraints with 'withOb'.
strengthD ::
  forall t arr a b c.
  (Strength t arr, Discrete arr) =>
  arr b c ->
  arr (t a b) (t a c)
strengthD f =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t a b) $
          withOb @arr @(t a c) $
            strength f
