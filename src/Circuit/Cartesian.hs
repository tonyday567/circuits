{-# LANGUAGE CPP #-}

-- | Cartesian monoidal structure for the @(,)@ tensor.
--
-- Structural isomorphisms and rearrangements for pairing.
-- The dual module for @Either@ would be @Circuit.Cocartesian@.
module Circuit.Cartesian
  ( -- * Associativity
    assoc,
    assoc',

    -- * State wire morphology
    seed,
    absorb,
    release,
  )
where

-- ---------------------------------------------------------------------------
-- Associativity
-- ---------------------------------------------------------------------------

-- | Associator: @(a, (b, c)) -> ((a, b), c)@.
assoc :: (a, (b, c)) -> ((a, b), c)
assoc (a, (b, c)) = ((a, b), c)

-- | Inverse associator: @((a, b), c) -> (a, (b, c))@.
assoc' :: ((a, b), c) -> (a, (b, c))
assoc' ((a, b), c) = (a, (b, c))

-- ---------------------------------------------------------------------------
-- State wire morphology (for @(,)@)
-- ---------------------------------------------------------------------------

-- | Introduce a state wire alongside a payload.
seed :: s -> a -> (s, a)
seed s a = (s, a)

-- | Move a value from payload into state.
--
-- @absorb f = first (uncurry f) . assoc@
absorb :: (t -> s -> s') -> (s, (t, b)) -> (s', b)
absorb f (s, (t, b)) = (f t s, b)

-- | Move a value from state into payload.
--
-- @release f = assoc' . first f@
release :: (s -> (s', t)) -> (s, b) -> (s', (t, b))
release f (s, b) = let (s', t) = f s in (s', (t, b))
