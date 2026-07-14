{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Arrow-level monoidal structure for a tensor @t@ inside a category @arr@.
--
-- This is the minimal structure needed to compose feedback loops: an
-- associator and a braiding for the tensor @t@, expressed as morphisms in
-- @arr@. For @arr = (->)@ this collapses to the value-level combinators in
-- "Circuit.Monoidal".
--
-- Kind-polymorphic: @t@ and @arr@ share object kind (inferred via PolyKinds),
-- so @(+)@ can be a tensor for @MatH@ alongside @Either@ for @Mat@ / @(->)@.
module Circuit.Monoidal.Category
  ( Monoidal (..),
  )
where

import Circuit.Classes (Category (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Classes ((>>>))

-- | A monoidal structure on the tensor @t@ internal to the category @arr@.
--
-- Provides the associator and braiding required to reassociate and swap
-- nested tensor values inside an arrow. This is the structure that traced
-- categories inherit as a superclass.
--
-- Object constraints live on 'Category' / 'Traced', not on these structure
-- maps — free constructions over unconstrained bases stay lightweight.
class (Category arr) => Monoidal t arr where
  -- | Reassociate to the right: @t (t a b) c -> t a (t b c)@.
  assoc :: arr (t (t a b) c) (t a (t b c))

  -- | Inverse reassociation: @t a (t b c) -> t (t a b) c@.
  assoc' :: arr (t a (t b c)) (t (t a b) c)

  -- | Swap the two outer positions, leaving the inner payload in place:
  -- @t a (t b c) -> t b (t a c)@.
  braid :: arr (t a (t b c)) (t b (t a c))

-- | Cartesian monoidal structure for @(,)@.
--
-- >>> assoc ((1, 2), 3) :: (Int, (Int, Int))
-- (1,(2,3))
--
-- >>> assoc' (1, (2, 3)) :: ((Int, Int), Int)
-- ((1,2),3)
--
-- >>> (assoc >>> assoc') ((1, 2), 3) :: ((Int, Int), Int)
-- ((1,2),3)
--
-- >>> braid (1, (2, 3)) :: (Int, (Int, Int))
-- (2,(1,3))
instance Monoidal (,) (->) where
  assoc ~(~(a, b), c) = (a, (b, c))
  assoc' ~(a, ~(b, c)) = ((a, b), c)
  braid ~(a, ~(b, c)) = (b, (a, c))

-- | Cocartesian monoidal structure for @Either@.
--
-- >>> assoc (Left (Left 1) :: Either (Either Int Bool) Char) :: Either Int (Either Bool Char)
-- Left 1
--
-- >>> assoc' (Left 1 :: Either Int (Either Bool Char)) :: Either (Either Int Bool) Char
-- Left (Left 1)
--
-- >>> braid (Left 1 :: Either Int (Either Bool Char)) :: Either Bool (Either Int Char)
-- Right (Left 1)
instance Monoidal Either (->) where
  assoc (Left (Left a)) = Left a
  assoc (Left (Right b)) = Right (Left b)
  assoc (Right c) = Right (Right c)
  assoc' (Left a) = Left (Left a)
  assoc' (Right (Left b)) = Left (Right b)
  assoc' (Right (Right c)) = Right c
  braid (Left a) = Right (Left a)
  braid (Right (Left b)) = Left b
  braid (Right (Right c)) = Right (Right c)
