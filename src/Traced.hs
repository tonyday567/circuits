{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Traced
  ( Traced (..),
    yank,
    interpret,
    run,
    close,
    loop',
    loop'',
  )
where

import Control.Arrow (Arrow, arr, ArrowLoop, loop, first)
import Control.Category (Category (..))
import Data.Profunctor
import Data.Profunctor.Strong (Strong (..))
import Prelude hiding (id, (.))
import Prelude qualified

-- | The free traced monoidal category over base category @arr@.
data Traced arr a b where
  Pure ::
    -- | Identity morphism.
    Traced arr a a
  Lift ::
    arr a b ->
    -- | Lift a base morphism into syntax.
    Traced arr a b
  Compose ::
    Traced arr b c ->
    Traced arr a b ->
    -- | Sequential composition (right runs first).
    Traced arr a c
  Knot ::
    Traced arr (a, c) (b, c) ->
    -- | Feedback: tie the knot by sealing the @c@ wire.
    Traced arr a b

-- | Tie a knot: yank feedback from a function.
yank :: ((a, c) -> (b, c)) -> Traced (->) a b
yank f = Knot (Lift f)

instance Category (Traced arr) where
  id = Pure
  (.) = Compose

instance Arrow (Traced (->)) where
  arr f = Lift f
  first p = Compose (Lift (\(a, c) -> (run p a, c))) Pure

instance Strong (Traced (->)) where
  first' p = Compose (Lift (\(a, c) -> (run p a, c))) Pure

instance Functor (Traced (->) a) where
  fmap f p = Compose (Lift f) p

instance Profunctor (Traced (->)) where
  dimap f g p = Lift g `Compose` p `Compose` Lift f

instance Costrong (Traced (->)) where
  unfirst = Knot

  unsecond p = Knot (Lift sw `Compose` p `Compose` Lift sw)
    where
      sw (a, b) = (b, a)

-- | Interpret @Traced arr@ into @arr@.
interpret :: (Arrow arr, ArrowLoop arr) => Traced arr a b -> arr a b
interpret Pure = id
interpret (Lift f) = f
interpret (Compose g h) = case g of
  Pure -> interpret h
  Lift f -> f . interpret h
  Compose g1 g2 -> interpret (Compose g1 (Compose g2 h))
  Knot p -> cloop (interpret p) (interpret h)
interpret (Knot p) = loop (interpret p)

loop' :: ((a, k) -> (b, k)) -> (a -> b)
loop' f b = let (k,d) = f (b,d) in k

-- | Alternative knot form via fixed point.
loop'' :: ((a, k) -> (b, k)) -> (a -> b)
loop'' f = \a -> fst (fix (\(_,c) -> f (a, c)))
  where
    fix g = let x = g x in x

cloop' :: ((x, k) -> (y, k)) -> (a -> x) -> (a -> y)
cloop' p h = \a -> loop' p (h a)

cloop :: (Arrow arr, ArrowLoop arr) => arr (x, k) (y, k) -> arr a x -> arr a y
cloop p h = loop (p . first h)

-- | Evaluate @Traced (->)@ to a Haskell function.
--
-- >>> let f = Compose (Lift (+ 1)) (Lift (* 2))
-- >>> run f 5
-- 11
--
-- >>> (run $ Knot $ Lift $ \(i, fibs) -> (fibs !! i, 0 : 1 : zipWith (+) fibs (drop 1 fibs))) 10
-- 55
run :: Traced (->) a b -> (a -> b)
run Pure = Prelude.id
run (Lift f) = f
run (Compose g h) = case g of
  Pure -> run h
  Lift f -> f Prelude.. run h
  Compose g1 g2 -> run (Compose g1 (Compose g2 h))
  Knot p -> cloop' (run p) (run h)
run (Knot p) = loop' (run p)

-- | Take the fixed point of a closed @Traced (->)@ loop.
close :: Traced (->) a a -> a
close = fix Prelude.. run
  where
    fix f = let x = f x in x
