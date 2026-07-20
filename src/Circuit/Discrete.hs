{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Discharge kit for authors of 'Discrete' categories and 'Layer' targets.
--
-- Free folds often need 'Ob' evidence at existential or compound objects
-- (intermediate composition objects, tensor products, feedback channels).
-- When the base category is 'Discrete', 'withOb' can manufacture that
-- evidence, but the resulting ladders are noisy. The helpers below package
-- the common patterns so instance authors do not rewrite them.
module Circuit.Discrete
  ( -- * Composition
    compD,

    -- * Channel structure
    assocD,
    assocD',
    braidD,

    -- * Strength and trace
    strengthD,
    traceD,
  )
where

import Circuit.Category (Category (..), Discrete (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..), strengthD)
import Prelude hiding (id, (.))

-- | Discrete composition: compose two arrows while discharging 'Ob'
-- constraints with 'withOb'.
compD ::
  forall arr a b c.
  (Discrete arr) =>
  arr b c ->
  arr a b ->
  arr a c
compD f g =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        f . g

-- | Discrete associator: reassociate leftward while discharging 'Ob'
-- constraints.
assocD ::
  forall t arr a b c.
  (Channel t arr, Discrete arr) =>
  arr (t (t a b) c) (t a (t b c))
assocD =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t a b) $
          withOb @arr @(t b c) $
            withOb @arr @(t (t a b) c) $
              withOb @arr @(t a (t b c)) $
                assoc

-- | Discrete associator inverse: reassociate rightward while discharging
-- 'Ob' constraints.
assocD' ::
  forall t arr a b c.
  (Channel t arr, Discrete arr) =>
  arr (t a (t b c)) (t (t a b) c)
assocD' =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t a b) $
          withOb @arr @(t b c) $
            withOb @arr @(t a (t b c)) $
              withOb @arr @(t (t a b) c) $
                assoc'

-- | Discrete braiding: slide a wire past a nested pair while discharging
-- 'Ob' constraints.
braidD ::
  forall t arr a b c.
  (Channel t arr, Discrete arr) =>
  arr (t a (t b c)) (t b (t a c))
braidD =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t b c) $
          withOb @arr @(t a c) $
            withOb @arr @(t a (t b c)) $
              withOb @arr @(t b (t a c)) $
                slide

-- | Discrete trace: eliminate a feedback loop while discharging 'Ob'
-- constraints.
traceD ::
  forall t arr a b c.
  (Traced t arr, Discrete arr) =>
  arr (t a b) (t a c) ->
  arr b c
traceD f =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @(t a b) $
          withOb @arr @(t a c) $
            trace f
