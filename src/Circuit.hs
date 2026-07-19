-- | Trace: free traced monoidal categories and hyperfunctions.
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
-- 'Trace' is the inspectable GADT form. 'Hyper' is the efficient final
-- encoding. Convert with 'encode' and 'run'.
--
-- >>> observe (encode (Arr (+1) :: Trace (,) (->) Int Int)) 41
-- 42
--
-- == Overview
--
-- This library provides two representations of feedback:
--
-- * 'Trace' (in "Circuit.Trace") — the initial, inspectable GADT encoding.
-- * 'Hyper' (in "Circuit.Hyper") — the final, coinductive encoding.
--
-- The 'Traced' class (in "Circuit.Trace") abstracts the choice of tensor,
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
  ( -- * Trace
    Trace (..),
    Traced,
    -- | Close a feedback loop. See "Circuit.Trace".
    trace,
    -- | Open a feedback loop. See "Circuit.Trace".
    untrace,

    -- * Channel ends
    Out (..),
    In (..),
    Ends (..),
    close,
    prefixIn,
    suffixOut,
    HasUnit (..),

    -- * Boxes
    box,

    -- * Queues
    Queue (..),
    openSTM,
    openIO,
    openCollectSTM,
    openCollectIO,

    -- * Free
    Free,
    freeze,

    -- * Layer tower
    Layer (..),
    Cat2,
    NT,
    HNT,
    (:~>),
    (:~~>),
    lower,
    run,
    hmap,
    join,

    -- * Dagger (bimonoid + dagger)
    Monoid (..),
    Comonoid (..),
    Dagger (..),
    Bimonoid,
    transpose,

    -- * Mon
    Mon,

    -- * Net
    Net,
    enrich,
    melt,

    -- * Hyper
    Hyper (..),
    lift,
    observe,
    base,
    push,
    runHyper,
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
    Tensor (..),
    Action (..),
  )
where

import Circuit.Box
  ( box,
  )
import Circuit.Dagger
  ( Bimonoid,
    Comonoid (..),
    Dagger (..),
    Monoid (..),
    transpose,
  )
import Circuit.Ends
  ( Ends (..),
    HasUnit (..),
    In (..),
    Out (..),
    close,
    prefixIn,
    suffixOut,
  )
import Circuit.Free
  ( Free (..),
    freeze,
  )
import Circuit.Hyper
  ( Hyper (..),
    base,
    encode,
    encodeEither,
    encodeFree,
    flatten,
    lift,
    observe,
    push,
    runEither,
    runHyper,
  )
import Circuit.Layer
  ( Cat2,
    HNT,
    Layer (..),
    NT,
    hmap,
    join,
    lower,
    run,
    (:~>),
    (:~~>),
  )
import Circuit.Mon
import Circuit.Monoidal
import Circuit.Net
  ( Net,
    enrich,
    melt,
  )
import Circuit.Queue
  ( Queue (..),
    openCollectIO,
    openCollectSTM,
    openIO,
    openSTM,
  )
import Circuit.Classes (Ob)
import Circuit.Trace
  ( Trace (..),
    Traced,
  )
import Circuit.Trace qualified as Trace
import Prelude hiding (Monoid)

-- | Close a feedback loop. See "Circuit.Trace".
trace ::
  (Traced t arr, Ob arr a, Ob arr b, Ob arr c, Ob arr (t a b), Ob arr (t a c)) =>
  arr (t a b) (t a c) ->
  arr b c
trace = Trace.trace

-- | Open a feedback loop. See "Circuit.Trace".
untrace ::
  (Traced t arr, Ob arr a, Ob arr b, Ob arr c, Ob arr (t a b), Ob arr (t a c)) =>
  arr b c ->
  arr (t a b) (t a c)
untrace = Trace.untrace
