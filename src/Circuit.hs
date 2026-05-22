-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- The main entry point. Re-exports all lowercase names from the submodules.
-- For notation conventions, see 'other/symbols.md'.
--
-- === usage
--
-- >>> :set -XGHC2024
-- >>> import Circuit
--
-- >>> let powers (ns, ()) = (1 : map (*2) ns, take 5 ns)
-- >>> trace powers () :: [Integer]
-- [1,2,4,8,16]
module Circuit
  ( -- * Circuit
    Circuit (..),
    Wire,
    Step,
    reify,
    ambientBy,

    -- * Braided
    Braided (..),
    ambient,

    -- * Cartesian
    assoc,
    assoc',
    seed,
    absorb,
    release,

    -- * Traced
    Trace (..),

    -- * Hyper
    Hyper (..),
    run,
    base,
    lift,
    lower,
    encode,
    encodeEither,
    runEither,
    flatten,
  )
where

import Circuit.Braided
  ( Braided (..),
    ambient,
  )
import Circuit.Cartesian
  ( absorb,
    assoc,
    assoc',
    release,
    seed,
  )
import Circuit.Circuit
  ( Circuit (..),
    Step,
    Wire,
    ambientBy,
    reify,
  )
import Circuit.Hyper
  ( Hyper (..),
    base,
    encode,
    encodeEither,
    flatten,
    lift,
    lower,
    run,
    runEither,
  )
import Circuit.Traced
  ( Trace (..),
  )
