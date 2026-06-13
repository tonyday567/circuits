-- | Circuit: free traced monoidal categories and hyperfunctions.
--
-- == Usage
--
-- @
-- import Circuit
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
-- 'Circuit' is the inspectable GADT form. 'Hyper' is the efficient final
-- encoding. Convert with 'encode' and 'reify'.
--
-- >>> lower (encode (Lift (+1) :: Circuit (->) (,) Int Int)) 41
-- 42
--
-- >>> reify (Knot (Lift (\(acc, x) -> (x, acc))) :: Circuit (->) (,) Int Int) 0
-- 0
--
-- == Overview
--
-- This library provides two representations of feedback:
--
-- * 'Circuit' (in "Circuit.Circuit") — the initial, inspectable GADT encoding.
-- * 'Hyper' (in "Circuit.Hyper") — the final, coinductive encoding.
--
-- The 'Trace' class (in "Circuit.Traced") abstracts the choice of tensor,
-- currently supporting lazy knots with @(,@) and iteration with 'Either'.
--
-- All braided, cartesian, and cocartesian structure, plus the general
-- 'ambientBy' state-threading combinator, lives in "Circuit.Monoidal".
--
-- == Core Concepts
--
-- * __Tensor__ (@t@): The bifunctor pairing a feedback value with a payload
--   inside a 'Knot' (currently @(,@) or 'Either').
--
-- * __Feedback value__: The component that travels around the loop (first
--   parameter of the tensor in a 'Knot').
--
-- * __Payload__: The value being transformed and emitted (second parameter
--   of the tensor).
--
-- * __Feedback channel__: The path the feedback value takes when routed back
--   into the next step.
module Circuit
  ( -- * Circuit
    Circuit (..),
    Wire,
    Step,
    Co (..),
    Contra (..),
    close,
    reify,

    -- * Traced
    Trace (..),
    cellIO,

    -- * Dagger (bimonoid + duplex)
    Additive (..),
    Dup (..),
    Duplex (..),
    Linear,
    ViaNum (..),
    transposeDuplex,

    -- * Net
    Net,
    transpose,
    upgrade,
    runNet,
    forget,

    -- * Hyper
    Hyper (..),
    lift,
    lower,
    base,
    push,
    run,
    encode,
    encodeEither,
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

import Circuit.Circuit
  ( Circuit (..),
    Step,
    Wire,
    Co (..),
    Contra (..),
    close,
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
import Circuit.Traced
  ( Trace (..),
    cellIO,
  )
import Circuit.Dagger
  ( Additive (..),
    Dup (..),
    Duplex (..),
    Linear,
    ViaNum (..),
    transposeDuplex,
  )
import Circuit.Net
  ( Net,
    transpose,
    upgrade,
    runNet,
    forget,
  )
