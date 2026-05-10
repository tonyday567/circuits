{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The Circuit GADT: free traced monoidal category.
--
-- `Circuit arr t a b` is the initial encoding of a traced monoidal category
-- over base arrow `arr` with tensor `t`. The three constructors encode:
--
--   - `Lift`: embedding of a base arrow (strict monoidal functor)
--   - `Compose`: sequential composition (category structure)
--   - `Knot`: feedback channel (trace structure)
--
-- = Encoding to Hyper
--
-- Two paths from Circuit to Hyper:
--
-- 1. 'toHyper' (flattening): @toHyper (Knot f) = lift (trace f)@.
--    Applies the 'Trace' instance to eliminate the knot, then lifts
--    the resulting plain function. Loop structure is lost.
--
-- 2. 'toHyperE' (structure-preserving for Either): encode the
--    Either-loop body as a self-referential Hyper using the
--    function-space trick. Unlike 'toHyper' (which flattens via
--    'trace'), 'toHyperE' preserves the loop structure — the Hyper
--    carries the feedback channel internally; 'run' ties the
--    recursive knot. Use 'runEither' to run from an initial input.
--
-- The `lower` function interprets any `Circuit` to a plain function via
-- the `Trace` instance on `t`.
module Circuit.Circuit
  ( -- * Circuit GADT
    Circuit (..),

    -- * Interpretation
    reify,
    lower,

    -- * Utilities
    push,
    toHyper,
    flatten,

    -- * Structure-preserving encodings
    toHyperE,
    runEither,

    -- * Symbolic operators
    (⊲),
    (↮),
    (↑),
    (↓),
  )
where

import Circuit.Hyper
  ( Hyper (..),
    run,
  )
import Circuit.Hyper qualified as Hyper
import Circuit.Traced
  ( Trace (..),
  )
import Control.Category (Category (..), id, (.))
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XBlockArguments -XLambdaCase
-- >>> import qualified Circuit.Hyper as Hyper

-- | Circuit arr t a b is the free traced monoidal category.
data Circuit arr t a b where
  -- | Lift embeds a base arrow (strict monoidal functor).
  Lift :: arr a b -> Circuit arr t a b
  -- | Compose performs sequential composition (category structure).
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  -- | Knot ties a feedback loop. The tensor t carries the channel type.
  Knot :: arr (t a b) (t a c) -> Circuit arr t b c

instance (Category arr) => Category (Circuit arr t) where
  id = Lift id
  (.) = Compose

instance Functor (Circuit (->) t a) where
  fmap f = Compose (Lift f)

instance (Trace (->) t) => Applicative (Circuit (->) t x) where
  pure a = Lift (const a)
  f <*> v = Lift $ \x -> reify f x (reify v x)

instance (Trace (->) t) => Monad (Circuit (->) t x) where
  m >>= k = Lift $ \x -> reify (k (reify m x)) x

-- | Push a plain function onto a Circuit.
--
-- >>> reify (push (+1) (Lift (*2) :: Circuit (->) (,) Int Int)) 5
-- 11
push :: arr b c -> Circuit arr t a b -> Circuit arr t a c
push f = Compose (Lift f)

-- | Interpret a Circuit to a plain function via the Trace instance.
--
-- This is the unique traced functor from the initial object (Circuit)
-- to the target category. The Mendler case (when a Loop appears on the
-- left of Compose) enforces the sliding axiom of traced monoidal categories.
--
-- >>> lower (Lift (+1) :: Circuit (->) (,) Int Int) 5
-- 6
lower :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
lower (Lift f) = f
lower (Compose (Knot f) g) = trace (f . untrace (lower g))
lower (Compose f g) = lower f . lower g
lower (Knot k) = trace k

-- | Alias for 'lower': interpret a Circuit as a plain function.
-- Used as the primary name for Circuit elimination to avoid conflict
-- with Hyper's elimination function.
reify :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
reify = lower

-- ---------------------------------------------------------------------------
-- Symbolic operators
-- ---------------------------------------------------------------------------

-- | Postfix synonym for 'Lift'.
infixr 9 ↑

(↑) :: arr a b -> Circuit arr t a b
(↑) = Lift

-- | Postfix synonym for 'lower'.
--
-- Because 'lower' returns a plain function, the postfix form
-- chains naturally via function application.
infixl 9 ↓

(↓) :: (Category arr, Trace arr t) => Circuit arr t a b -> arr a b
(↓) = lower

-- | Postfix synonym for 'Knot'.
infixr 9 ↮

(↮) :: arr (t a b) (t a c) -> Circuit arr t b c
(↮) = Knot

-- | Push / prepend a plain function to a Circuit.
infixr 8 ⊲

(⊲) :: arr b c -> Circuit arr t a b -> Circuit arr t a c
(⊲) = push

-- | Flatten a Hyper to a Circuit by observing it.
--
-- This is the forgetful map from the final encoding to the initial encoding.
-- All feedback structure is lost; only the observable behaviour remains.
flatten :: Hyper a b -> Circuit (->) (,) a b
flatten h = Lift (Hyper.lower h)

-- | Convert a Circuit to a Hyper (unfolding).
--
-- This is the unique traced functor from the initial object (Circuit)
-- to the final object (Hyper). The triangle `Hyper.lower . toHyper = reify` holds,
-- making this the map that respects the adjunction.
--
-- Note: @toHyper (Knot f) = lift (trace f)@ — the knot is flattened.
-- For a structure-preserving Either encoding, see 'toHyperE'.
--
-- >>> Hyper.lower (toHyper (Lift (+1) :: Circuit (->) (,) Int Int)) 5
-- 6
toHyper :: Circuit (->) (,) a b -> Hyper a b
toHyper (Lift f) = Hyper.lift f
toHyper (Compose f g) = toHyper f . toHyper g
toHyper (Knot f) = Hyper.lift (trace f)

-- ---------------------------------------------------------------------------
-- Structure-preserving Either → Hyper encoding
-- ---------------------------------------------------------------------------

-- | Encode an Either-loop as a self-referential Hyper.
--
-- Unlike 'toHyper' (which flattens the knot via 'trace'), this preserves
-- the loop structure inside the Hyper. @Left a@ feeds back;
-- @Right c@ terminates with output.
--
-- >>> runEither (\case Right n | n < 3 -> Left (n+1); Right n -> Right n; Left n | n < 3 -> Left (n+1); Left n -> Right n) (0 :: Int)
-- 3
toHyperE :: (Either a b -> Either a c) -> Hyper (Either a b -> c) (Either a b -> c)
toHyperE f = h
  where
    h = Hyper \k s ->
      case f s of
        Right c -> c
        Left a -> invoke k h (Left a)

-- | Run a toHyperE-encoded circuit from initial input @b@.
runEither :: (Either a b -> Either a c) -> b -> c
runEither f b = run (toHyperE f) (Right b)
