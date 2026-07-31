{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Probability as a double-dual continuation category.
--
-- A morphism @Prob arr r a b@ is an expectation transformer: it turns a
-- continuation @arr (x, b) r@ (a "test" on the output) into a continuation
-- @arr (x, a) r@ (a test on the input).  The rank-2 quantification over @x@
-- is the cost of arrow-polymorphism — the same move used by 'Circuit.Ends'.
--
-- This is the categorical substrate for probability, conditioning, and
-- verification: choosing the dualizing object @r@ picks the semantics.
--
-- * @r = Log Double@ over @(->)@ gives expectation transformers / measures.
-- * @r = Bool@ over @(->)@ gives Dijkstra's weakest-precondition semantics.
-- * @r = Min Double@ (tropical) gives Bellman / Viterbi / MAP semantics.
--
-- This module currently provides instances for the function arrow @(->)@.
-- Effectful variants (e.g. @Kleisli m@) follow the same pattern but need
-- scalar-lifting plumbing; the function case is where the design is easiest
-- to validate.
--
-- The tensor action on @Prob@ is /premonoidal/ in general: two valid nestings
-- ('parFG' and 'parGF') agree only on the linear (commutative) fragment.  We
-- therefore do not provide a canonical 'Circuit.Tensor.Tensor' instance; use
-- the explicit nesting you mean.
module Circuit.Prob
  ( -- * Double-dual probability arrow
    Prob (..),

    -- * Primitive constructors
    embed,
    score,
    mass,

    -- * Parallel nestings (Fubini on the linear fragment)
    parFG,
    parGF,
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..))
import Data.Bifunctor (second)
import Prelude hiding (id, (.))
import Prelude qualified

-- $setup
-- >>> import Circuit.Prob
-- >>> import Prelude hiding (id, (.))

-- | Double-dual embedding of @arr@ with respect to dualizing object @r@.
--
-- A value @Prob arr r a b@ reads an output-continuation @arr (x, b) r@ and
-- produces an input-continuation @arr (x, a) r@.  Composition is continuation
-- composition (contravariant in the middle type).
newtype Prob arr r a b = Prob
  { runProb :: forall x. arr (x, b) r -> arr (x, a) r
  }

-- ---------------------------------------------------------------------------
-- Category
-- ---------------------------------------------------------------------------

instance Category (Prob (->) r) where
  type Ob (Prob (->) r) a = ()

  id :: Prob (->) r a a
  id = Prob Prelude.id
  {-# INLINE id #-}

  (.) ::
    Prob (->) r b c ->
    Prob (->) r a b ->
    Prob (->) r a c
  Prob f . Prob g = Prob $ \k -> g (f k)
  {-# INLINE (.) #-}

-- ---------------------------------------------------------------------------
-- Structural instances (cartesian tensor, function arrow)
-- ---------------------------------------------------------------------------

-- | Lift a structural morphism on pairs to act on the second component while
-- carrying the context @x@ along.
ctxSecond :: ((a, b) -> c) -> (x, (a, b)) -> (x, c)
ctxSecond f (x, y) = (x, f y)
{-# INLINE ctxSecond #-}

instance Channel (,) (Prob (->) r) where
  assoc = Prob $ \k -> k . ctxSecond assoc
  {-# INLINE assoc #-}

  assoc' = Prob $ \k -> k . ctxSecond assoc'
  {-# INLINE assoc' #-}

  slide = Prob $ \k -> k . ctxSecond slide
  {-# INLINE slide #-}

  withTensorOb _ _ x = x

instance Strength (,) (Prob (->) r) where
  strength (Prob f) = Prob $ \k -> f (k . assoc) . assoc'
  {-# INLINE strength #-}

  withStrengthOb _ _ _ x = x

-- ---------------------------------------------------------------------------
-- Primitives (function arrow)
-- ---------------------------------------------------------------------------

-- | Embed a deterministic function as a probability morphism.
--
-- The continuation is applied to the transformed output, with the context
-- wire carried along unchanged.
embed :: (a -> b) -> Prob (->) r a b
embed h = Prob $ \k -> k . second h
{-# INLINE embed #-}

-- | Scale the result of a continuation.
score :: (r -> r) -> Prob (->) r a a
score scale = Prob $ \k (x, a) -> scale (k (x, a))
{-# INLINE score #-}

-- | Compute the total mass of an unnormalised morphism against the unit
-- continuation.
mass :: r -> Prob (->) r a b -> a -> r
mass one (Prob f) a = f (const one) ((), a)
{-# INLINE mass #-}

-- ---------------------------------------------------------------------------
-- Parallel nestings (Fubini on the linear fragment)
-- ---------------------------------------------------------------------------

-- | Parallel composition: @g@ runs at context @(x, a)@, @f@ runs at context
-- @(x, c)@.  This is one of two lawful nestings; it agrees with 'parGF' on
-- the linear/commutative fragment.
parFG ::
  Prob (->) r a b ->
  Prob (->) r c d ->
  Prob (->) r (a, c) (b, d)
parFG (Prob f) (Prob g) = Prob $ \k ->
  let kg ((ctx, a), d) = k (ctx, (a, d))
      gc = g kg
      kf ((ctx, c), a) = gc ((ctx, a), c)
      fa = f kf
   in \(ctx, (a, c)) -> fa ((ctx, c), a)
{-# INLINE parFG #-}

-- | Parallel composition: @f@ runs at context @(x, d)@, @g@ runs at context
-- @(x, a)@.  The other nesting; agrees with 'parFG' on the linear fragment.
parGF ::
  Prob (->) r a b ->
  Prob (->) r c d ->
  Prob (->) r (a, c) (b, d)
parGF (Prob f) (Prob g) = Prob $ \k ->
  let kf ((ctx, d), a) = k (ctx, (a, d))
      fa = f kf
      kg ((ctx, a), d) = fa ((ctx, d), a)
      gb = g kg
   in \(ctx, (a, c)) -> gb ((ctx, a), c)
{-# INLINE parGF #-}
