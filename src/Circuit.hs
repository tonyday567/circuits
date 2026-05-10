{-# LANGUAGE RankNTypes #-}

-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- The main entry point. For most use cases, import submodules directly:
--
-- > import Circuit.Circuit (Circuit (..), reify)
-- > import Circuit.Hyper (Hyper (..), run, lower)
-- > import Circuit.Traced (Trace (..))
--
-- For detailed design and theory, see @other/@.
-- For examples, see @examples/@.

module Circuit
  ( -- * Circuit (initial encoding)
    Circuit (..),
    reify,
    lower,
    push,
    toHyper,

    -- * Hyper (final encoding)
    Hyper (..),
    type (↬),
    run,
    base,
    lift,

    -- * Symbolic operators
    (⇸),
    (⊲),
    (↮),
    (⥁),
    (○),
    (↑),
    (↓),

    -- * Trace typeclass
    Trace (..),
    (↪),
    (↩),

    -- * Channel (coroutines)
    Producer,
    Consumer,
    Channel,
    unit,
    glue,
    prod,
    cons,
    yield,
    accept,

    -- * Structure-preserving encoding
    toHyperE,
    runEither,
  )
where

import Circuit.Circuit
  ( Circuit (..),
    reify,
    lower,
    push,
    toHyper,
    (⊲),
    (↮),
    (↑),
    (↓),
    toHyperE,
    runEither,
  )
import Circuit.Hyper
  ( Hyper (..),
    type (↬),
    run,
    base,
    lift,
    (⇸),
    (⥁),
    (○),
  )
import Circuit.Traced
  ( Trace (..),
    (↪),
    (↩),
  )
import Circuit.Channel
  ( Producer,
    Consumer,
    Channel,
    unit,
    glue,
    prod,
    cons,
    yield,
    accept,
  )
