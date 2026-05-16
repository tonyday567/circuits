{-# LANGUAGE RankNTypes #-}

-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- The main entry point. For most use cases, import submodules directly:
--
-- > import Circuit.Circuit (Circuit (..), reify)
-- > import Circuit.Hyper (Hyper (..), run, lower, encode, flatten)
-- > import Circuit.Traced (Trace (..))
--
-- === operator cheatsheet
--
-- @
-- name       symbol   module          meaning
-- ──────────────────────────────────────────────────
-- lift       (↑)      Circuit/Hyper   embed a plain arrow
-- compose    (⊙)      Circuit/Hyper   sequential composition
-- knot       (↮)      Circuit         feedback loop constructor
-- reify                Circuit         interpret to plain arrow
-- lower      (↓)      Hyper           observe hyperfunction
-- base       (○)      Hyper           constant continuation
-- push       (⊲)      both            prepend function
-- run        (⥁)      Hyper           tie self-referential knot
-- encode     (⇨)      Hyper           Circuit → Hyper
-- invoke     (⇸)      Hyper           apply continuation
-- trace      (↪)      Traced          close feedback loop
-- untrace    (↩)      Traced          open feedback loop
-- flatten              Hyper           Hyper → Circuit (lossy)
-- @
--
-- For detailed design and theory, see @other/@.
-- For examples, see @examples/@.
module Circuit
  ( -- * Circuit (initial encoding)
    Circuit (..),
    reify,
    lower,
    push,

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
    (⊙),

    -- * Trace typeclass
    Trace (..),
    (↪),
    (↩),

    -- * Encoding
    encode,
    (⇨),
    encodeEither,
    runEither,
    flatten,
  )
where

import Circuit.Circuit
  ( Circuit (..),
    push,
    reify,
    (↑),
    (↮),
    (⊲),
    (⊙),
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
    (⇨),
    (⇸),
    (○),
    (⥁),
    type (↬),
  )
import Circuit.Traced
  ( Trace (..),
    (↩),
    (↪),
  )
