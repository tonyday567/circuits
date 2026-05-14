{-# LANGUAGE RankNTypes #-}

-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- The main entry point. For most use cases, import submodules directly:
--
-- > import Circuit.Circuit (Circuit (..), reify)
-- > import Circuit.Hyper (Hyper (..), run, lower, encode, flatten)
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
    lower,
    push,
    reify,
    (↑),
    (↓),
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
