-- | Trace: free traced monoidal categories and hyperfunctions.
--
-- == Usage
--
-- @
-- import Trace
-- @
--
-- === Lazy feedback (knot-tying)
--
-- Use the @(,@) tensor to tie a lazy knot. The feedback value and output
-- are produced simultaneously.
--
-- >>> let powers (ns, ()) = (1 : map (*2) ns, take 5 ns)
-- >>> trace powers () :: [Integer]
-- [1,2,4,8,16]
--
-- === Iteration
--
-- Use the 'Either' tensor for loops that terminate.
--
-- >>> let step n = if n < 5 then Left (n + 1) else Right n
-- >>> trace (either step step) (0 :: Int)
-- 5
--
-- === Switching between representations
--
-- 'Trace' is the inspectable GADT form. 'Hyper' is the efficient final
-- encoding. Convert with 'encode' and 'reify'.
--
-- >>> lower (encode (Lift (+1) :: Trace (,) (->) Int Int)) 41
-- 42
--
-- == Overview
--
-- This library provides two representations of feedback:
--
-- * 'Trace' (in "Circuit.Trace") — the initial, inspectable GADT encoding.
-- * 'Hyper' (in "Circuit.Hyper") — the final, coinductive encoding.
--
-- The 'Traced' class (in "Circuit.Traced") abstracts the choice of tensor,
-- currently supporting lazy knots with @(,@) and iteration with 'Either'.
--
-- All braided, cartesian, and cocartesian structure, plus the general
-- 'ambientBy' state-threading combinator, lives in "Circuit.Monoidal".
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor pairing a feedback value with a payload
--   inside a 'Trace' (currently @(,@) or 'Either').
--
-- * __Feedback value__: The component that travels around the loop (first
--   parameter of the tensor in a 'Trace').
--
-- * __Payload__: The value being transformed and emitted (second parameter
--   of the tensor).
--
-- * __Feedback channel__: The path the feedback value takes when routed back
--   into the next step.
module Circuit
  (    -- * Trace
    Trace (..),
    Wire,
    Step,
    Co (..),
    Contra (..),
    close,
    reify,
    freeze,

    -- * Free
    Free,
    runFree,

    -- * Dagger (bimonoid + dagger)
    Monoid (..),
    Comonoid (..),
    Dagger (..),
    Bimonoid,
    transpose,

    -- * Net
    Net,
    upgrade,
    loom,
    melt,

    -- * Hyper
    Hyper (..),
    lift,
    lower,
    base,
    push,
    run,
    encode,
    encodeEither,
    encodeFree,
    runEither,
    flatten,

    -- * Monoidal
    Braided (..),
    ambient,
    assoc,
    assoc',
    seed,
    absorb,
    release,
    coassoc,
    coassoc',
    coseed,
    coabsorbL,
    coabsorbR,
    coreleaseL,
    coreleaseR,
    ambientBy,

    -- * Monoidal product
    MonoidalP (..),
  )
where

import Circuit.Trace
  ( Trace (..),
    Co (..),
    Contra (..),
    Step,
    Wire,
    close,
    freeze,
    reify,
  )
import Circuit.Dagger
  ( Bimonoid,
    Comonoid (..),
    Dagger (..),
    Monoid (..),
    transpose,
  )
import Circuit.Free
  ( Free,
    runFree,
  )
import Circuit.Hyper
  ( Hyper (..),
    base,
    encode,
    encodeEither,
    encodeFree,
    flatten,
    lift,
    lower,
    push,
    run,
    runEither,
  )
import Circuit.Monoidal
  ( Braided (..),
    MonoidalP (..),
    absorb,
    ambient,
    ambientBy,
    assoc,
    assoc',
    coabsorbL,
    coabsorbR,
    coassoc,
    coassoc',
    coreleaseL,
    coreleaseR,
    coseed,
    release,
    seed,
  )
import Circuit.Net
  ( Net,
    loom,
    melt,
    upgrade,
  )
import Circuit.Traced qualified as Traced
import Prelude hiding (Monoid)
