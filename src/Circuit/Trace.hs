{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The free traced monoidal category, in existential normal form.
--
-- @Trace t arr a b@ is the free traced monoidal category over a base
-- morphism @arr@ with tensor @t@. The two constructors encode:
--
--   * 'Arr' — a plain base arrow.
--   * 'Knot' — a feedback loop with a hidden feedback channel.
--
-- The laws of traced monoidal categories are performed by the 'Category'
-- and 'Traced' instances, so every value is already in normal form: at most
-- one 'Knot' at the top, over a base-arrow body. There is no separate
-- quotient step and no "Mendler case" in an interpreter.
--
-- For example, a @Trace (,) (->)@ is the initial traced monoidal cartesian
-- category over Haskell functions.
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor that pairs a feedback value with a payload.
--   The two tensors provided are @(,)@ (simultaneous / lazy sharing) and
--   'Either' (sequential / iteration).
--
-- * __Feedback value__: The component that travels around the loop (the first
--   parameter of the tensor inside a 'Knot' body).
--
-- * __Payload__: The component that is transformed and emitted (the second
--   parameter of the tensor inside a 'Knot' body).
--
-- * __Feedback channel__: The hidden type @s@ in a 'Knot'. It is the value
--   the abstraction hides.
module Circuit.Trace
  ( -- * Trace
    Trace (..),

    -- * Channel plumbing
    Channelled (..),

    -- * Type aliases
    Wire,
    Step,

    -- * Interpreters
    run,
    foldTrace,

    -- * Channel ends
    Co (..),
    Contra (..),
    close,
  )
where

import Circuit.Traced
import Prelude hiding (id, (.))

#ifdef __GLASGOW_HASKELL__
import Control.Category
import Data.Bifunctor
import Data.Profunctor
#else
import Circuit.Classes
#endif

-- $setup
-- >>> import Control.Category ((>>>))
-- >>> import Data.Profunctor (dimap)
-- >>> import Prelude hiding (id, (.))

-- | The free traced monoidal category over base morphism @arr@ and tensor @t@,
-- in existential normal form.
--
-- Two constructors:
--
--   * 'Arr' — a plain base arrow.
--   * 'Knot' — a feedback loop with hidden channel @s@.
data Trace t arr a b where
  -- | A plain base arrow.
  --
  -- >>> run (Arr (+1) :: Trace (,) (->) Int Int) 5
  -- 6
  Arr :: arr a b -> Trace t arr a b
  -- | Tie a feedback loop. The tensor @t@ carries the hidden channel type @s@.
  --
  -- >>> run (Knot (\(acc, x) -> (x, acc)) :: Trace (,) (->) Int Int) 42
  -- 42
  Knot :: arr (t s a) (t s b) -> Trace t arr a b

-- | Channel plumbing for feedback fusion. Provides associativity and braiding
-- of the tensor @t@ at the arrow level.
class (Bifunctor t) => Channelled arr t where
  -- | Reassociate a nested channel to the right: @t (t s s') x -> t s (t s' x)@.
  assocC :: arr (t (t s s') x) (t s (t s' x))
  -- | Inverse reassociation: @t s (t s' x) -> t (t s s') x@.
  assocC' :: arr (t s (t s' x)) (t (t s s') x)
  -- | Swap the two channel positions, leaving the payload in place:
  -- @t s (t s' x) -> t s' (t s x)@.
  braidC :: arr (t s (t s' x)) (t s' (t s x))

-- | Cartesian channel plumbing.
instance Channelled (->) (,) where
  assocC ((s, s'), x) = (s, (s', x))
  assocC' (s, (s', x)) = ((s, s'), x)
  braidC (s, (s', x)) = (s', (s, x))

-- | Cocartesian channel plumbing.
instance Channelled (->) Either where
  assocC = coassoc'
  assocC' = coassoc
  braidC = braid
    where
      braid (Left x) = Right (Left x)
      braid (Right (Left y)) = Left y
      braid (Right (Right z)) = Right (Right z)

-- | Coassociativity for sums: @Either s (Either s' x) -> Either (Either s s') x@.
coassoc :: Either s (Either s' x) -> Either (Either s s') x
coassoc (Left s) = Left (Left s)
coassoc (Right (Left s')) = Left (Right s')
coassoc (Right (Right x)) = Right x

-- | Inverse coassociativity for sums.
coassoc' :: Either (Either s s') x -> Either s (Either s' x)
coassoc' (Left (Left s)) = Left s
coassoc' (Left (Right s')) = Right (Left s')
coassoc' (Right x) = Right (Right x)

-- | A traced circuit over plain functions with the cartesian tensor.
type Wire = Trace (,) (->)

-- | A traced circuit over plain functions with the cocartesian tensor.
type Step = Trace Either (->)

instance (Category arr, Traced arr t, Channelled arr t) => Category (Trace t arr) where
  id = Arr id
  Arr f . Arr g = Arr (f . g)
  Knot f . Arr g = Knot (f . untrace g)
  Arr f . Knot g = Knot (untrace f . g)
  Knot f . Knot g =
    Knot (assocC' . braidC . untrace f . braidC . untrace g . assocC)

instance (Profunctor arr, Bifunctor t) => Profunctor (Trace t arr) where
  dimap f g (Arr h) = Arr (dimap f g h)
  dimap f g (Knot h) = Knot (dimap (second f) (second g) h)
  lmap f (Arr h) = Arr (lmap f h)
  lmap f (Knot h) = Knot (lmap (second f) h)
  rmap g (Arr h) = Arr (rmap g h)
  rmap g (Knot h) = Knot (rmap (second g) h)

instance (Bifunctor t) => Functor (Trace t (->) a) where
  fmap f (Arr g) = Arr (f . g)
  fmap f (Knot g) = Knot (second f . g)

-- | Lift the 'Traced' class through 'Trace t'.
--
-- 'trace' hides a wire as a 'Knot'; 'untrace' exposes it.
instance (Category arr, Traced arr t, Channelled arr t) => Traced (Trace t arr) t where
  trace (Arr f) = Knot f
  trace (Knot f) = Knot (assocC' . f . assocC)
  untrace (Arr f) = Arr (untrace f)
  untrace (Knot f) = Knot (braidC . untrace f . braidC)

-- | Interpret a 'Trace' to a plain arrow.
--
-- This is the canonical fold out of the free traced monoidal category.
-- It calls the base arrow's 'trace' exactly once, in the 'Knot' case.
--
-- >>> run (Arr (+1) :: Trace (,) (->) Int Int) 5
-- 6
run :: Traced arr t => Trace t arr a b -> arr a b
run (Arr f) = f
run (Knot f) = trace f

-- | Universal fold from the free traced monoidal category.
--
-- Every interpreter out of 'Trace' is an instance of this fold.
-- 'run' is @foldTrace id@.
foldTrace ::
  (Traced arr' t) =>
  (forall x y. arr x y -> arr' x y) ->
  Trace t arr a b ->
  arr' a b
foldTrace h (Arr f) = h f
foldTrace h (Knot f) = trace (h f)

-- ---------------------------------------------------------------------------
-- Channel ends — the companion and conjoint of the identity functor.

-- | 'Co' is the companion of the identity functor in the proarrow equipment
-- over 'Trace'.  Covariant in @a@ (sits in the output position).
newtype Co arr t a = Co
  { -- | Run the companion, supplying the other end.
    runContra :: forall x. Contra arr t x -> Trace t arr x a
  }

-- | 'Contra' is the conjoint of the identity functor.  Contravariant in
-- @a@ (sits in the input position).
newtype Contra arr t a = Contra
  { -- | Run the conjoint, supplying the other end.
    runCo :: forall x. Co arr t x -> Trace t arr a x
  }

-- | Plug two channel ends together, producing a circuit from @a@ to @a@.
close :: Contra arr t a -> Co arr t a -> Trace t arr a a
close contra = runCo contra
