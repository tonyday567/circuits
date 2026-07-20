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
-- @arr@. For @arr = (->)@ these are ordinary functions on tensor values.
--
-- Note: 'assoc' and 'assoc'' here reassociate /rightward/ and /leftward/
-- respectively. The monomorphic helpers in "Circuit.Tensor" have the same
-- names but the opposite directions. Also, 'slide' here is the slide
-- @t a (t b c) -> t b (t a c)@; the symmetric braiding @t a b -> t b a@
-- lives in 'Circuit.Tensor' as 'swap'. Where both structures exist,
-- @slide = assoc' '>>>' par swap id '>>>' assoc@.
--
-- Kind-polymorphic: @t@ and @arr@ share object kind (inferred via PolyKinds).
module Circuit.Channel
  ( Channel (..),
  )
where

import Circuit.Category (Category (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Category ((>>>))

-- | A monoidal structure on the tensor @t@ internal to the category @arr@.
--
-- Provides the associator and braiding required to reassociate and swap
-- nested tensor values inside an arrow. This is the structure that traced
-- categories inherit as a superclass.
--
-- Object constraints live on 'Category' / 'Traced', not on these structure
-- maps — free constructions over unconstrained bases stay lightweight.
class (Category arr) => Channel t arr where
  -- | Reassociate to the right: @t (t a b) c -> t a (t b c)@.
  assoc :: arr (t (t a b) c) (t a (t b c))

  -- | Inverse reassociation: @t a (t b c) -> t (t a b) c@.
  assoc' :: arr (t a (t b c)) (t (t a b) c)

  -- | Swap the two outer positions, leaving the inner payload in place:
  -- @t a (t b c) -> t b (t a c)@.
  slide :: arr (t a (t b c)) (t b (t a c))

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
-- >>> slide (1, (2, 3)) :: (Int, (Int, Int))
-- (2,(1,3))
instance Channel (,) (->) where
  assoc ~(~(a, b), c) = (a, (b, c))
  assoc' ~(a, ~(b, c)) = ((a, b), c)
  slide ~(a, ~(b, c)) = (b, (a, c))

-- | Cocartesian monoidal structure for @Either@.
--
-- >>> assoc (Left (Left 1) :: Either (Either Int Bool) Char) :: Either Int (Either Bool Char)
-- Left 1
--
-- >>> assoc' (Left 1 :: Either Int (Either Bool Char)) :: Either (Either Int Bool) Char
-- Left (Left 1)
--
-- >>> slide (Left 1 :: Either Int (Either Bool Char)) :: Either Bool (Either Int Char)
-- Right (Left 1)
instance Channel Either (->) where
  assoc (Left (Left a)) = Left a
  assoc (Left (Right b)) = Right (Left b)
  assoc (Right c) = Right (Right c)
  assoc' (Left a) = Left (Left a)
  assoc' (Right (Left b)) = Left (Right b)
  assoc' (Right (Right c)) = Right c
  slide (Left a) = Right (Left a)
  slide (Right (Left b)) = Left b
  slide (Right (Right c)) = Right (Right c)
