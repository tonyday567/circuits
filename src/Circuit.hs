{-# LANGUAGE RankNTypes #-}

-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- The main entry point. For most use cases, import submodules directly:
--
-- > import Circuit.Circuit (Circuit (..), reify)
-- > import Circuit.Hyper (Hyper (..), run, lower)
-- > import Circuit.Traced (Trace (..))
--
-- For detailed design and theory, see @other\/narrative-arc.md@ and @other\/axioms-hyp.md@.
--
-- For proofs by example (Agent, Dual, Parser patterns, and more), see @examples/@.

module Circuit
  ( -- * Circuit (initial encoding)
    Circuit (..),
    reify,
    toHyper,
    hyperfy,

    -- * Hyper (final encoding)
    Hyper (..),
    run,
    base,
    lift,
    push,

    -- * Trace typeclass
    Trace (..),
    PromptTag,
    newPromptTag,
    prompt,
    control0,
  )
where

import Circuit.Circuit
  ( Circuit (..),
    reify,
    toHyper,
    hyperfy,
  )
import Circuit.Hyper
  ( Hyper (..),
    run,
    base,
    lift,
    push,
  )
import Circuit.Traced
  ( Trace (..),
    PromptTag,
    newPromptTag,
    prompt,
    control0,
  )
