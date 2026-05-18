-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- The main entry point. Re-exports all lowercase names from the submodules.
-- For unicode symbols, import 'Circuit.Symbols'.
--
-- For most use cases, import submodules directly:
--
-- > import Circuit.Circuit (Circuit (..), reify)
-- > import Circuit.Hyper (Hyper (..), run, lower, encode, flatten)
-- > import Circuit.Traced (Trace (..))
--
-- For detailed design and theory, see @other/@.
-- For examples, see @examples/@.
module Circuit
  ( -- * Circuit
    Circuit (..),
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
