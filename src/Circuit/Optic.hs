{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Mixed optics as existential residual maps.
--
-- In the equipment-optics story, an optic between two spans with common
-- boundaries is a 2-cell between the corresponding loose arrows.  In
-- @Prof@ that unwinds to the mixed-optic coend
--
-- @
--   Optic_M((S,R),(A,B)) = ∫^M C(S, M ⊙ A) × D(M ⊙ B, R)
-- @
--
-- where @⊙@ is a monoidal action.  In @circuits@ the action is the tensor
-- @t@ itself, and a mixed optic is a pair of base-arrow morphisms with an
-- existentially hidden residual channel.
--
-- This module is the residual-remembering rung of the optic ladder: the
-- residual @ch@ is part of the data, not quotiented away (that would be the
-- @SomeBody@ / @Circ@ view).  The equipment-optics payoff is that
-- composition is just vertical composition of 2-cells, which here reduces to
-- tensoring the residuals and reassociating.
module Circuit.Optic
  ( -- * Mixed optic
    Optic (..),
    SomeOptic (..),

    -- * Category operations
    identityOptic,
    composeOptic,

    -- * Action on morphisms
    opticUpdate,
  )
where

import Circuit.Body (Body (..))
import Circuit.Category (Category (..), (.>))
import Circuit.Channel (Channel (..))
import Circuit.Tensor (Tensor (..), Unit)
import Prelude hiding (id, (.))

-- | A mixed optic from @(s,r)@ to @(a,b)@ with residual @ch@.
--
-- * @opticForward :: arr s (t ch a)@ maps the domain left boundary into the
--   residual plus the codomain left boundary.
-- * @opticBackward :: arr (t ch b) r@ maps the residual plus the codomain
--   right boundary back to the domain right boundary.
--
-- For the cartesian tensor @(,)@ and @arr = (->)@ this is the usual
-- lens-like shape @s -> (ch, a)@ and @(ch, b) -> r@.
data Optic t arr ch a b s r = Optic
  { -- | Forward direction: introduce the residual and the codomain left boundary.
    opticForward :: arr s (t ch a),
    -- | Backward direction: consume the residual and the codomain right boundary.
    opticBackward :: arr (t ch b) r
  }

-- | A mixed optic with the residual existentially hidden.
data SomeOptic t arr a b s r where
  SomeOptic :: ch -> Optic t arr ch a b s r -> SomeOptic t arr a b s r

-- | Identity optic at @(a,b)@.  The residual is the tensor unit.
identityOptic ::
  (Tensor t arr) =>
  Optic t arr (Unit t) a b a b
identityOptic = Optic unitl' unitl
{-# INLINE identityOptic #-}

-- | Vertical composition of mixed optics.
--
-- Given @opt1 :: (s,r) -> (a,b)@ with residual @ch1@ and
-- @opt2 :: (a,b) -> (u,v)@ with residual @ch2@, the composite has residual
-- @t ch1 ch2@.  This is exactly the tensoring of residuals that appears in
-- the coend formula for optic composition.
composeOptic ::
  forall t arr ch1 ch2 a b u v s r.
  (Tensor t arr, Channel t arr) =>
  Optic t arr ch2 u v a b ->
  Optic t arr ch1 a b s r ->
  Optic t arr (t ch1 ch2) u v s r
composeOptic (Optic f2 b2) (Optic f1 b1) =
  Optic
    (f1 .> tensor (id :: arr ch1 ch1) f2 .> assoc')
    (assoc .> tensor (id :: arr ch1 ch1) b2 .> b1)
{-# INLINE composeOptic #-}

-- | Apply an optic to a plain base-arrow morphism.
--
-- Given @m :: arr a b@, an optic @(s,r) -> (a,b)@ produces a morphism
-- @arr s r@ by routing through the residual.  This is the mixed-optic update
-- action: a lens turns a focus-update into a whole-update; a prism turns a
-- branch-update into a sum-update.
opticUpdate ::
  (Tensor t arr) =>
  Optic t arr ch a b s r ->
  arr a b ->
  arr s r
opticUpdate (Optic f b) m =
  f .> tensor id m .> b
{-# INLINE opticUpdate #-}
