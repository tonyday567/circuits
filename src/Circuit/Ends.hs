{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Free channel ends over a base arrow, plus concrete box and queue helpers.
--
-- A channel has exactly two ends:
--
--   * @Out@ — the companion (read / emit end), covariant in the payload.
--   * @In@  — the conjoint (write / commit end), contravariant in the payload.
--
-- @Ends@ is the record that pairs one @In@ with one @Out@.  The ends are
-- defined purely in terms of the base arrow @arr@.
--
-- The companion and conjoint form an adjunction @In ⊣ Out@.
-- The unit @η@ is 'open', producing a matched pair; the counit @ε@ is
-- 'close', plugging the pair back together by feeding the @Out@ into the
-- @In@.
--
-- This module also provides the concrete helpers built on top of channel
-- ends:
--
--   * 'box' and 'boxAsymmetric' — embed an @Ends@ into a plain 'Loop'.
--   * 'Queue' strategies and STM / IO @Ends@ constructors ('openSTM',
--     'openIO').
module Circuit.Ends
  ( -- * Channel ends (bi-polar contract)
    Out (..),
    In (..),

    -- * Matched pair
    Ends (..),

    -- * Counit
    close,

    -- * Prefixing an action to an @In@
    prefixIn,

    -- * Suffixing an action to an @Out@
    suffixOut,

    -- * Build an @Ends@ from primitive actions
    ends,
    endsK,

    -- * Extract primitive actions from an @Ends@
    splay,

    -- * Unit ends (requires constant morphisms)
    HasUnit (..),

    -- * Boxes
    box,
    boxAsymmetric,

    -- * Queue strategies
    Queue (..),

    -- * STM @Ends@
    openSTM,

    -- * IO @Ends@
    openIO,
  )
where

import Circuit.Category (Category (..), Discrete (..), (.>))
import Circuit.Loop (Loop (..))
import Circuit.Tensor (Tensor (..), Unit)
import Control.Applicative
import Control.Arrow (Kleisli (..))
import Control.Concurrent.STM
import Control.Monad (void)
import Prelude hiding (id, (.))

-- $setup
-- >> :set -XTypeApplications
-- >> import Circuit.Category ((.>))
-- >> import Circuit.Ends
-- >> import Circuit.Layer (run)
-- >> import Control.Arrow (Kleisli(..), runKleisli)
-- >> import Control.Concurrent.STM (STM, atomically)

-- ---------------------------------------------------------------------------
-- Channel ends — the companion and conjoint of the identity functor.
-- ---------------------------------------------------------------------------

-- | @Out@ is the companion of the identity functor.  Covariant in @a@
-- (sits in the output position).
newtype Out arr a = Out
  { -- | Emit through the companion, supplying the other end.
    emit :: forall x. In arr x -> arr x a
  }

-- | @In@ is the conjoint of the identity functor.  Contravariant in
-- @a@ (sits in the input position).
newtype In arr a = In
  { -- | Commit through the conjoint, supplying the other end.
    commit :: forall x. Out arr x -> arr a x
  }

-- | A matched pair of channel ends: one @In@ and one @Out@.
--
-- This is the bi-polar communication contract.  The conjoint (@In@)
-- consumes payloads of type @a@; the companion (@Out@) produces payloads
-- of type @b@.  For symmetric channels such as queues @a = b@.
--
-- Together with 'prefixIn' and 'suffixOut', @Ends@ carries an /enriched/
-- profunctor structure over the base category @arr@: 'prefixIn' is the
-- left action of @arr@ on @In@ ends, and 'suffixOut' is the right action
-- of @arr@ on @Out@ ends.
data Ends arr a b = Ends
  { -- | Write end (producer), the conjoint.
    conjoint :: In arr a,
    -- | Read end  (consumer), the companion.
    companion :: Out arr b
  }

-- | Counit of the companion / conjoint adjunction.
--
-- Plug an @In@ and an @Out@ of the same payload type together to produce
-- a morphism of @arr@ from @a@ to @a@.
--
-- 'close' feeds the @Out@ into the @In@ end, producing a morphism
-- @arr a a@ from the paired payload type.
--
-- Yanking: for the unit ends from 'open',
-- @close (conjoint ends) (companion ends) = id@.
close :: In arr a -> Out arr a -> arr a a
close contra = commit contra

-- | Precompose an @arr@-morphism with an @In@ end.
--
-- Given @f :: arr a b@ and an @In@ end at type @b@, produce an @In@ end
-- at type @a@.  Running the resulting end first executes @f@ and then
-- commits through the original end.
--
-- This is the left (contravariant) action of the base category on @In@
-- ends.  Specialised to unit ends it is the canonical way to build
-- effectful write ends.
--
-- .> let endsU = open :: Ends (->) () ()
-- .> let inA = prefixIn (const ()) (conjoint endsU) :: In (->) Int
-- .> commit inA (companion endsU) 42
-- ()
prefixIn :: forall arr a b. (Discrete arr) => arr a b -> In arr b -> In arr a
prefixIn f i = In $ \(o :: Out arr x) -> withOb @arr @a $ withOb @arr @b $ withOb @arr @x $ f .> commit i o

-- | Postcompose an @arr@-morphism with an @Out@ end.
--
-- Given an @Out@ end at type @a@ and @g :: arr a b@, produce an @Out@
-- end at type @b@.  Running the resulting end first emits through the
-- original end and then executes @g@ on the emitted value.
--
-- This is the right (covariant) action of the base category on @Out@
-- ends.  Specialised to unit ends it is the canonical way to build
-- effectful read ends.
--
-- .> let endsU = open :: Ends (->) () ()
-- .> let outA = suffixOut (companion endsU) (const 42) :: Out (->) Int
-- .> emit outA (conjoint endsU) ()
-- 42
suffixOut :: forall arr a b. (Discrete arr) => Out arr a -> arr a b -> Out arr b
suffixOut o g = Out $ \(i :: In arr x) -> withOb @arr @x $ withOb @arr @a $ withOb @arr @b $ emit o i .> g

-- ---------------------------------------------------------------------------
-- Unit ends
-- ---------------------------------------------------------------------------

-- | Arrows that have unit channel ends for a given unit object @u@.
--
-- The unit ends are the identity-on-@u@ morphism split into its two
-- polar halves.  The companion is constant; the conjoint delegates to
-- the opposing companion.
--
-- These ends require the base arrow to support constant morphisms, so
-- they are captured by this class rather than being definable for all
-- arrows.
class (Category arr) => HasUnit u arr where
  -- | The monoidal unit as channel ends.
  --
  -- === Yank
  --
  -- >>> let ends = open :: Ends (->) () ()
  -- >>> close (conjoint ends) (companion ends) ()
  -- ()
  --
  -- === Unit plug
  --
  -- >>> let endsA = open :: Ends (->) () ()
  -- >>> let endsU = open :: Ends (->) () ()
  -- >>> commit (conjoint endsA) (companion endsU) ()
  -- ()
  -- >>> emit (companion endsA) (conjoint endsU) ()
  -- ()
  open :: Ends arr u u

-- | Build an @Ends@ from a write morphism and a read morphism.
--
-- @write :: arr a ()@ consumes the input payload and produces the unit;
-- @read :: arr () b@ consumes the unit and produces the output payload.
-- The unit ends wire the two halves together.
--
-- This is the canonical way to turn a pair of primitive channel actions
-- into a matched pair of @In@ and @Out@ ends.
--
-- Compositional spelling:
--
-- @
-- ends write receive =
--   Ends (prefixIn write (conjoint open)) (suffixOut (companion open) receive)
-- @
ends ::
  forall arr a b.
  (Discrete arr, HasUnit () arr) =>
  arr a () ->
  arr () b ->
  Ends arr a b
ends write receive =
  Ends
    (prefixIn write (conjoint open))
    (suffixOut (companion open) receive)

-- | Specialization of 'ends' for @Kleisli@ actions.
--
-- @write :: a -> m ()@ consumes the input payload; @receive :: m b@
-- produces the output payload. The unit handling is hidden inside the
-- @Kleisli@ wrappers.
endsK ::
  forall m a b.
  (Monad m) =>
  (a -> m ()) ->
  m b ->
  Ends (Kleisli m) a b
endsK write receive = ends (Kleisli write) (Kleisli $ const receive)

-- | Extract the primitive write and read actions from an @Ends@ by
-- plugging each end with the unit ends.
--
-- For an @Ends@ built with 'ends', this recovers the original
-- @write :: arr a ()@ and @receive :: arr () b@.
--
-- .> let e = ends (\() -> ()) (const (42 :: Int)) :: Ends (->) () Int
-- .> let (write, receive) = splay e
-- .> (write (), receive ())
-- ((),42)
splay ::
  forall arr a b.
  (HasUnit () arr) =>
  Ends arr a b ->
  (arr a (), arr () b)
splay e =
  ( commit (conjoint e) (companion (open :: Ends arr () ())),
    emit (companion e) (conjoint (open :: Ends arr () ()))
  )

-- | Unit ends for @(->)@ with unit @()@.
--
-- The companion is the constant function returning @()@; the conjoint
-- recursively emits through the supplied companion.
instance HasUnit () (->) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> const ()
      inU = In $ \o -> emit o inU

-- | Unit ends for @Kleisli@ @m@ with unit @()@.
--
-- Same shape as the @(->)@ instance, but the constant companion returns
-- @()@ in the monad.
instance (Monad m) => HasUnit () (Kleisli m) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> Kleisli $ \_ -> pure ()
      inU = In $ \o -> emit o inU

-- ---------------------------------------------------------------------------
-- Boxes
-- ---------------------------------------------------------------------------

-- | String-diagram boxes from channel ends.
--
-- A matched pair of free ends (@Ends@) is a box with one input wire and
-- one output wire.  The helpers below embed that box into a traced
-- monoidal category by unit-plugging the remaining two slots.

-- | Embed an @Ends@ into a plain @Loop t arr a b@.
--
-- Connects the two channel ends through the unit object, giving a plain
-- @Loop t arr a b@. This is the version most users expect: input on the
-- left, output on the right, with the unit plumbing hidden.
--
-- .> let e = ends (const ()) (const 42) :: Ends (->) () Int
-- .> run (box @(,) e) ()
-- 42
box ::
  forall t arr a b.
  (HasUnit (Unit t) arr, Ob arr a, Ob arr b, Ob arr (Unit t)) =>
  Ends arr a b ->
  Loop t arr a b
box ends' =
  Lift $
    commit (conjoint ends') (companion (open :: Ends arr (Unit t) (Unit t)))
      .> emit (companion ends') (conjoint (open :: Ends arr (Unit t) (Unit t)))

-- | Asymmetric box with units exposed on opposite sides.
--
-- Uses 'par' at the base arrow level and lifts the result with 'Lift'.
-- The input carries the unit on the right and the output carries the unit
-- on the left; most users will prefer the unit-normalised 'box'.
--
-- .> let e = ends (const ()) (const 42) :: Ends (->) () Int
-- .> run (boxAsymmetric @(,) e) ((), ())
-- ((),42)
boxAsymmetric ::
  forall t arr a b.
  (HasUnit (Unit t) arr, Tensor t arr) =>
  Ends arr a b ->
  Loop t arr (t a (Unit t)) (t (Unit t) b)
boxAsymmetric ends' =
  Lift $
    par
      (commit (conjoint ends') (companion open))
      (emit (companion ends') (conjoint open))

-- ---------------------------------------------------------------------------
-- Queue strategies and STM @Ends@
-- ---------------------------------------------------------------------------

-- | How messages are queued between producer and consumer.
data Queue a
  = -- | Unbounded FIFO queue.
    Unbounded
  | -- | Bounded FIFO with backpressure (write blocks when full).
    Bounded Int
  | -- | Single-slot buffer (write blocks when full).
    Single
  | -- | Single-slot buffer, overwrite-on-full.
    -- Write always succeeds; read empties.
    SwapQ
  | -- | Always holds the latest value (overwrites, never blocks).
    Latest a
  | -- | Like @Bounded@ but drops oldest when full.
    Newest Int
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- STM ends
-- ---------------------------------------------------------------------------

-- | Internal STM primitive for a queue strategy.
--
-- Returns the raw write/read actions used by 'openSTM'.  Not exported;
-- the canonical API is 'openSTM'.
endsSTM :: Queue a -> STM (a -> STM (), STM a)
endsSTM = \case
  Bounded n -> do
    q <- newTBQueue (fromIntegral n)
    pure (writeTBQueue q, readTBQueue q)
  Unbounded -> do
    q <- newTQueue
    pure (writeTQueue q, readTQueue q)
  Single -> do
    m <- newEmptyTMVar
    pure (putTMVar m, takeTMVar m)
  SwapQ -> do
    v <- newEmptyTMVar
    let write x = tryPutTMVar v x >>= \case True -> pure (); False -> void (swapTMVar v x)
    pure (write, takeTMVar v)
  Latest a -> do
    t <- newTVar a
    pure (writeTVar t, readTVar t)
  Newest n -> do
    q <- newTBQueue (fromIntegral n)
    let write x = writeTBQueue q x <|> (tryReadTBQueue q *> write x)
    pure (write, readTBQueue q)

-- ---------------------------------------------------------------------------
-- IO @Ends@
-- ---------------------------------------------------------------------------

-- | Open a queue strategy as STM @Ends@.
--
-- Allocates STM primitives and returns a matched pair of ends sharing
-- the same mutable channel.  Both ends live in 'STM', so you can compose
-- operations across channels in a single 'atomically' block.
--
-- === Unbounded
--
-- .> let endsU = open :: Ends (Kleisli STM) () ()
-- .> ends <- atomically (openSTM Unbounded :: STM (Ends (Kleisli STM) Int Int))
-- .> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 42
-- .> atomically $ runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 42
--
-- Multi-op compose in one 'atomically' (both writes + read):
--
-- .> ends <- atomically (openSTM Unbounded :: STM (Ends (Kleisli STM) Int Int))
-- .> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 1 >> runKleisli (commit (conjoint ends) (companion endsU)) 2 >> runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 1
--
-- 'close' recovers the value through the queue:
--
-- .> ends <- atomically (openSTM Unbounded :: STM (Ends (Kleisli STM) Int Int))
-- .> atomically $ runKleisli (close (conjoint ends) (companion ends)) 7
-- 7
--
-- === SwapQ (overwrite on write)
--
-- .> ends <- atomically (openSTM SwapQ :: STM (Ends (Kleisli STM) Int Int))
-- .> atomically $ runKleisli (commit (conjoint ends) (companion endsU)) 1 >> runKleisli (commit (conjoint ends) (companion endsU)) 2 >> runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 2
openSTM :: Queue a -> STM (Ends (Kleisli STM) a a)
openSTM q = do
  (write, read') <- endsSTM q
  pure (endsK write read')

-- | Open a queue strategy as IO @Ends@.
--
-- Like 'openSTM', but each primitive operation is wrapped in its own
-- 'atomically'.  You cannot batch multiple writes or a write-plus-read
-- into a single STM transaction; for that use 'openSTM' and wrap in
-- 'atomically' yourself.
--
-- .> let endsU = open :: Ends (Kleisli IO) () ()
-- .> ends <- openIO Unbounded :: IO (Ends (Kleisli IO) Int Int)
-- .> runKleisli (commit (conjoint ends) (companion endsU)) 42
-- .> runKleisli (emit (companion ends) (conjoint endsU)) ()
-- 42
openIO :: Queue a -> IO (Ends (Kleisli IO) a a)
openIO q = do
  e <- atomically (openSTM q)
  let (Kleisli write, Kleisli receive) = splay e
  pure (endsK (atomically . write) (atomically (receive ())))
