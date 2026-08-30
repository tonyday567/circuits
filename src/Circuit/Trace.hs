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

import Circuit.Category (Category (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Circuit.Syntax
  ( Algebra (..),
    SigCompose (..),
    Syntax (..),
    eval,
    (:+:) (..),
  )
import Data.Kind (Type)
import Prelude hiding (id, (.))

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

instance (Assoc t arr, Slide t arr, Strength t arr, Yank t arr) => Strength t (Trace t arr) where
  strength f = base (strength (eval f))

instance (Yank t arr) => Yank t (Syntax (SigCompose :+: SigYank t) arr) where
  yank body = Oper (R (YankBody body))
