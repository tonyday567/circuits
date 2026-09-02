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
  )
where

import Circuit.Category (Category (..), (.>))
import Circuit.Syntax
  ( Algebra (..),
    SigCompose (..),
    Syntax (..),
    (:+:) (..),
  )
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Syntax (eval)
-- >>> import Circuit.Traced (Strength (..), Yank (..))

-- Trace signature

-- | Feedback loop / trace over tensor @t@.
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
