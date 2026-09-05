{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Free traced monoidal category syntax.
--
-- This module packages the traced-monoidal layer on top of the generic
-- free-construction substrate in "Circuit.Syntax". The signature sum is
--
-- @
-- 'SigCompose' ':+:' 'SigYank' t
-- @
--
-- where 'SigCompose' provides sequential composition and 'SigYank' provides
-- feedback / trace over the channel tensor @t@.
--
-- Higher-level signatures (parallel composition, braid, copy\/discard,
-- shared-medium fusion, mediators) live in "Circuit.SMC", "Circuit.Bimonoid",
-- and "Circuit.Shared".
module Circuit.Trace
  ( -- * Free traced category
    Trace,
    base,

    -- * Trace signature
    SigYank (..),

    -- * One-knot normal form
    Knot (..),
    Wire,
    Step,
  )
where

import Circuit.Category (Category (..), (.>))
import Circuit.Syntax (Algebra (..), Layer (..), SigCompose (..), Syntax (..), (:+:) (..), (:~>))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Syntax (eval)
-- >>> import Circuit.Category ((.>))
-- >>> import Circuit.Syntax (run)
-- >>> import Circuit.Traced (Strength (..), Yank (..))

-- Trace signature

-- | Feedback loop / trace over tensor @t@.
--
-- The constructor is 'YankBody' — it wraps a body — rather than @SigYank@;
-- the naming is intentional, while the other @Sig*@ constructors match
-- their type names.
data SigYank (t :: Type -> Type -> Type) arr rec a b where
  YankBody ::
    rec (t s a) (t s b) ->
    SigYank t arr rec a b

instance (Yank t arr') => Algebra (SigYank t) arr arr' where
  type Ctx (SigYank t) arr arr' = Yank t arr'
  alg ::
    forall (rec :: Type -> Type -> Type) (b :: Type) (c :: Type).
    (forall x y. arr x y -> arr' x y) ->
    (forall x y. rec x y -> arr' x y) ->
    SigYank t arr rec b c ->
    arr' b c
  alg _ rec (YankBody @_ @_ @_ @_ @_ @_ f) = yank (rec f)

-- Free traced monoidal category over tensor @t@

-- | Free traced monoidal category over tensor @t@.
type Trace t arr = Syntax (SigCompose :+: SigYank t) arr

-- | Lift a base arrow into the free traced category.
base :: arr a b -> Trace t arr a b
base = Lift

-- Instances for the free traced category

instance (Category arr) => Category (Trace t arr) where
  id = base id
  f . g = Oper (L (SigCompose f g))

instance (Category arr, Assoc t arr) => Assoc t (Trace t arr) where
  assoc = base assoc
  assoc' = base assoc'

instance (Category arr, Slide t arr) => Slide t (Trace t arr) where
  slide = base slide

-- | Tensorial strength for the free traced category, structurally.
--
-- The operation is pushed inside the syntax rather than evaluated:
--
-- * a lifted base arrow is strengthened at the base;
-- * a composition strengthens both halves;
-- * a yanked body is slid so the scaffolding sits outside the loop,
--   strengthened, and yanked — the free form of the traced-category strength
--   axiom (an independent payload wire is invisible to the trace).
--
-- Nothing here evaluates, so the base category is never asked to be traced:
-- the free traced category really is free over an untraced base.
--
-- The structural fold agrees with evaluating first and strengthening at the
-- base (a mutation of the slide placement would swap loop wire and payload,
-- changing the answer):
--
-- >>> let f = (\(s, x) -> (x, s + x)) :: (Int, Int) -> (Int, Int)
-- >>> let t = yank (base f) :: Trace (,) (->) Int Int
-- >>> eval (strength t) (7, 3)
-- (7,6)
-- >>> strength (eval t) (7, 3)
-- (7,6)
instance (Category arr, Slide t arr, Strength t arr) => Strength t (Trace t arr) where
  strength (Lift f) = base (strength f)
  strength (Oper (L (SigCompose g f))) = strength g . strength f
  strength (Oper (R (YankBody body))) = yank (base slide .> strength body .> base slide)

-- | Yank for the free traced category: a constructor, not an evaluation.
--
-- The constraints are exactly what the superclass ('Strength') needs
-- structurally; the base category is not required to be traced.
instance (Category arr, Slide t arr, Strength t arr) => Yank t (Syntax (SigCompose :+: SigYank t) arr) where
  yank body = Oper (R (YankBody body))

-- * One-knot normal form

-- | The free traced monoidal category over tensor @t@, in existential
-- normal form.
--
-- Two constructors:
--
--   * 'Arr' — a plain base arrow.
--   * 'Knot' — a feedback loop with hidden channel @s@.
--
-- The 'Category' instance performs the traced-monoidal laws at
-- composition time: composing a 'Knot' with a 'Knot' reassociates the
-- pair of channels, slides one channel past the other body and back, and
-- rejoins — vanishing (b) as a term rewrite.  Every value is therefore
-- already in normal form: at most one 'Knot' at the top, over a
-- base-arrow body.  The rewrite spends the base's 'Assoc', 'Slide', and
-- 'Strength' structure once per fusion.
--
-- Over a premonoidal base the rewrite is sound only when the structural
-- maps are central — the Benton–Hyland Central Sliding side condition
-- (see the 'Yank' law note in "Circuit.Traced").
--
-- Interpreting a 'Knot' folds it into any base arrow with 'Yank', via
-- the 'Layer' instance: for the cartesian tensor this is the lazy knot,
-- and for the cocartesian tensor it is iteration (see the 'Yank'
-- instances in "Circuit.Traced").
data Knot (t :: Type -> Type -> Type) arr a b where
  -- | A plain base arrow.
  Arr :: arr a b -> Knot t arr a b
  -- | Tie a feedback loop. The tensor @t@ carries the hidden channel @s@.
  Knot :: arr (t s a) (t s b) -> Knot t arr a b

-- | A traced circuit over plain functions with the cartesian tensor.
type Wire = Knot (,) (->)

-- | A traced circuit over plain functions with the cocartesian tensor.
type Step = Knot Either (->)

-- $examples
--
-- >>> run (Arr (+1) :: Knot (,) (->) Int Int) 5
-- 6
--
-- >>> run (Knot (\(acc, x) -> (x, acc)) :: Knot (,) (->) Int Int) 42
-- 42
--
-- For the @(,)@ tensor the channel value is self-referential, so the body
-- must not force the channel before producing its constructor:
--
-- >>> run (Knot (\ ~(ns, ()) -> (0 : ns, take 3 ns)) :: Wire () [Int]) ()
-- [0,0,0]
--
-- The cocartesian tensor iterates: 'Left' feeds back, 'Right' exits.
--
-- >>> let cd = either (\n -> if n > 0 then Left (n - 1) else Right n) (\n -> if n > 0 then Left (n - 1) else Right n)
-- >>> run (Knot cd :: Step Int Int) 5
-- 0
--
-- Composition keeps the normal form: two knots fuse into one.
--
-- >>> let fused = Knot (\(s, x) -> (s + x, s)) .> Knot (\(s, x) -> (s * x, s)) :: Knot (,) (->) Int Int
-- >>> case fused of { Knot _ -> "one knot"; Arr _ -> "plain" }
-- "one knot"

-- | Composition in existential normal form.
--
-- 'Knot' fused with 'Knot' is a single 'Knot' over the paired channel:
-- the composite body reassociates rightward, runs @g@ under the outer
-- channel, slides @f@'s channel out and back, and reassociates leftward.
instance (Strength t arr) => Category (Knot t arr) where
  id = Arr id
  Arr f . Arr g = Arr (f . g)
  Knot f . Arr g = Knot (strength g .> f)
  Arr f . Knot g = Knot (g .> strength f)
  Knot f . Knot g = Knot (assoc .> strength g .> slide .> strength f .> slide .> assoc')

-- | Lift the base associator through 'Knot'.
instance (Strength t arr) => Assoc t (Knot t arr) where
  assoc = Arr assoc
  assoc' = Arr assoc'

-- | Lift the base slide through 'Knot'.
instance (Strength t arr) => Slide t (Knot t arr) where
  slide = Arr slide

-- | Lift 'Strength' through 'Knot'.
--
-- A yanked body is slid so the new outer channel passes outside the
-- loop, strengthened, and slid back.
instance (Strength t arr) => Strength t (Knot t arr) where
  strength (Arr f) = Arr (strength f)
  strength (Knot f) = Knot (slide .> strength f .> slide)

-- | Lift 'Yank' through 'Knot'.
--
-- 'yank' wraps a body as a 'Knot'; yanking a 'Knot' reassociates its two
-- channels into one — vanishing (b) again.
instance (Yank t arr) => Yank t (Knot t arr) where
  yank (Arr f) = Knot f
  yank (Knot f) = Knot (assoc .> f .> assoc')

-- | Postcomposition with a pure payload morphism.
instance (Bifunctor t) => Functor (Knot t (->) a) where
  fmap f (Arr g) = Arr (g .> f)
  fmap f (Knot g) = Knot (g .> second f)

-- | 'Knot' is a free layer over a 'Yank'-able base: 'unit' embeds a base
-- arrow as 'Arr', and 'bind' folds a 'Knot' by yanking the mapped body.
instance Layer (Knot t) where
  type Law (Knot t) arr' = Yank t arr'

  type Run (Knot t) arr = Yank t arr

  type Bind (Knot t) arr = ()

  unit = Arr

  bind ::
    (Law (Knot t) arr') =>
    (arr :~> arr') ->
    Knot t arr a b ->
    arr' a b
  bind h (Arr f) = h f
  bind h (Knot f) = yank (h f)
