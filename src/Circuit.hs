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
    ambient,

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

import Circuit.Circuit
  ( Circuit (..),
    Step,
    Wire,
    ambient,
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
