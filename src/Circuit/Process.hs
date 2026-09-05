{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Stateful stream processes: the unpointed 'Mealy' carrier and the
-- pointed 'Process' carrier.
--
-- @
-- data Mealy a b = forall s. Mealy (a -> s) (s -> a -> s) (s -> b)
-- data Process s a b = Process s (s -> a -> s) (s -> b)
-- @
--
-- 'Mealy' is the circuits-native carrier for streaming state machines: the
-- interface is a monomial @a -> b@ stream transformer and the initial state is
-- supplied by the first input. The underlying span-shaped carrier is
-- 'Circuit.Body.Body'.
--
-- * @inject@ converts the first input into an initial state.
-- * @step@ updates the state given the current input.
-- * @extract@ produces the output from the current state.
--
-- 'Process' is the same machine with the seed made explicit: the state type
-- @s@ is a parameter and every tick is uniform (state in, input in, state
-- out, output out). 'asMealy' forgets the seed, mapping a pointed process
-- to its unpointed shadow; 'Circuit.Machine.asProcess' and
-- 'Circuit.Machine.machineAsMealy' mediate the monomial corner with
-- polynomial machines.
--
-- This pair is intended to replace the hand-rolled state-machine arrow: stats
-- packages become boxes @Mealy a b@ / @Process s a b@, while the arrow itself
-- lives in the substrate next to 'Circuit.Trace' and 'Circuit.Net'.
--
-- The semantics are intentionally tied to the circuits substrate:
--
-- * 'scan' / 'scanProcess' are the reference runners over lists.
-- * 'scanStream' generalizes this to any 'Uncons' input and 'Cons' output.
-- * 'encodeList' maps a process into a stream-level 'Trace' 'Either' @(->)@ over
--   lists; the two runners are verified equivalent by oracle.
-- * The arrow-level 'Yank' Either instance is per-tick Conway/Elgot settle,
--   not cross-tick state feedback; see 'register' for the latter.
--
-- = Pointed systems
--
-- The pointed-machine view of a stateful morphism lives in 'Circuit.Machine',
-- which builds polynomial interfaces on top of this monomial carrier.
module Circuit.Process
  ( -- * Stream transformer (monomial special case)
    Mealy (..),

    -- * Pointed process (explicit seed)
    Process (..),
    asMealy,

    -- * Machine conversions
    asProcess,
    machineAsMealy,
    asProcessCell,
    processAsMachine,

    -- * Boundary machines
    markProcess,
    markMealy,
    scheduleAsProcess,

    -- * Channel-pole processes
    polesToProcess,
    runPoles,

    -- * Functorial plumbing
    before,
    after,
    parWith,
    parWith3,
    parWith4,

    -- * Runners
    scan,
    scanProcess,
    runProcess,
    finalProcess,
    scanStream,
    fold,
    foldProcess,
    foldStream,
    encodeList,
    encodeStream,

    -- * Mealy-style processes
    mealy,
    runMealy,
    runMealyStream,

    -- * Cross-tick feedback
    delay,
    register,

    -- * Body conversions and runners
    processToBody,
    mealyToSomeBody,
    bodyToMealy,
    runBody,
    runBodyCell,
  )
where

import Circuit.Bimonoid (Copy, CopyDiscard, Discard, Merge, MergeZero, Zero)
import Circuit.Bimonoid qualified as Bm
import Circuit.Body (Body (..))
import Circuit.Category (Category (..))
import Circuit.Equip (Boundary (..), Poles (..), UnitCell (..), unitCell)
import Circuit.Equip qualified as Poles
import Circuit.Machine (Machine, machine, machineMorphism, monoDir, monoIn, toEvalMachine)
import Circuit.Poly (Eval (..), Mono)
import Circuit.Shared (Pick (..), Schedule (..), Shared (..), chooseS)
import Circuit.Stream (Cons (..), Uncons (..))
import Circuit.Tensor (Action (..), Bias (..), Tensor (..), Unital (..))
import Circuit.Trace (Trace, base)
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Control.Applicative (liftA3)
import Data.Bifunctor (Bifunctor (..))
import Data.Maybe (fromMaybe)
import Data.These (These (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Process
-- >>> import Prelude hiding (id, (.))

-- | A stateful process from @a@ to @b@.
--
-- The existential state type @s@ is hidden; the observable interface is the
-- triple @inject / step / extract@. Keeping the triple as the primitive (rather
-- than fusing @extract@ into the step) preserves the streaming-statistics
-- invariant that the first output is @extract (inject x)@, before any step.
--
-- This is the input discharge of pointing: the initial state is created from
-- the first input. See 'Circuit.Equip.UnitCell' for the explicit discharge
-- and the taxonomy.
data Mealy a b where
  Mealy ::
    forall s a b.
    (a -> s) ->
    (s -> a -> s) ->
    (s -> b) ->
    Mealy a b

-- | A pointed process with an explicit seed.
--
-- This is the same data as 'Mealy' except the initial state @s0@ is exposed
-- rather than computed from the first input. Every tick is uniform: state in,
-- input in, state out, output out.
--
-- This is the explicit discharge of pointing — the seed as data. See
-- 'Circuit.Equip.UnitCell'.
data Process s a b = Process
  { processSeed :: s,
    processStep :: s -> a -> s,
    processExtract :: s -> b
  }

-- | Forget the explicit seed of a 'Process', yielding a 'Mealy' whose
-- first input creates the initial state via 'processStep'.
asMealy :: Process s a b -> Mealy a b
asMealy (Process s0 step extract) =
  Mealy (\a -> step s0 a) step extract
{-# INLINEABLE asMealy #-}

-- * Machine conversions

-- | Convert a monomial @(->)@ machine into a pointed process.
asProcess :: Machine (,) s (->) (Mono i o) -> s -> Process s i o
asProcess sys s0 = Process s0 step' extract'
  where
    step' s i = case toEvalMachine sys s of EP (EK _, EE f) -> f i
    extract' s = case toEvalMachine sys s of EP (EK o, EE _) -> o

-- | Convert a monomial @(->)@ machine into a process.
machineAsMealy :: Machine (,) s (->) (Mono i o) -> s -> Mealy i o
machineAsMealy sys s0 = asMealy (asProcess sys s0)

-- | Point a monomial machine with a 'Circuit.Equip.UnitCell' instead of a
-- bare seed.
--
-- Agrees with the ad-hoc seed runner:
--
-- >>> import Circuit.Machine (Machine, machine)
-- >>> import Circuit.Poly (Mono)
-- >>> import Circuit.Equip (unitCell)
-- >>> import Data.Void (absurd)
-- >>> let sys = machine (\case (_, Left v) -> absurd v; (s, Right i) -> (s + i, (s * 2, ()))) :: Machine (,) Int (->) (Mono Int Int)
-- >>> scanProcess (asProcess sys 3) [1, 2]
-- [8,12]
-- >>> scanProcess (asProcessCell sys (unitCell (const 3))) [1, 2]
-- [8,12]
asProcessCell :: Machine (,) s (->) (Mono i o) -> UnitCell (,) (->) s -> Process s i o
asProcessCell sys (UnitCell f) = asProcess sys (f ())

-- | Convert a pointed process into a monomial 'Machine' machine.
--
-- The position is read from the /new/ state — the process output of the
-- state after consuming the direction.  The state evolution agrees with
-- 'asProcess'; the observation is the one-tick shift of a machine built
-- directly with 'machine'.
--
-- >>> import Circuit.Machine (Machine, machineMorphism, machine)
-- >>> import Circuit.Poly (Mono)
-- >>> import Data.Void (absurd)
-- >>> let acc = Process 0 (+) (\x -> x) :: Process Int Int Int
-- >>> scanProcess acc [1, 2, 3]
-- [1,3,6]
-- >>> machineMorphism (processAsMachine acc) (0, Right 1)
-- (1,(1,()))
--
-- Round trip through 'asProcess': the transition is unchanged and the
-- position comes from the new state (@16 = 8 * 2@, not the pre-step @6@).
--
-- >>> let sys = machine (\case (s, Left v) -> absurd v; (s, Right i) -> (s + i, (s * 2, ()))) :: Machine (,) Int (->) (Mono Int Int)
-- >>> machineMorphism (processAsMachine (asProcess sys 3)) (3, Right 5)
-- (8,(16,()))
processAsMachine :: Process s i o -> Machine (,) s (->) (Mono i o)
processAsMachine pp =
  machine $ \(s, d) ->
    let s' = processStep pp s (monoDir d)
     in (s', (processExtract pp s', ()))
{-# INLINEABLE processAsMachine #-}

-- * Boundary machines

-- | Mark-driven halt combinator for pointed processes.
markProcess ::
  (k -> Bool) ->
  Process s a b ->
  Process (Either s s) (Boundary k a) (Maybe b)
markProcess isHalt (Process s0 step extract) =
  Process
    (Left s0)
    ( \case
        Left s -> \case
          Payload a -> Left (step s a)
          Mark k -> if isHalt k then Right s else Left s
        Right s -> const (Right s)
    )
    ( \case
        Left s -> Just (extract s)
        Right _ -> Nothing
    )

-- | Mark-driven halt combinator for processes.
markMealy ::
  (k -> Bool) ->
  Mealy a b ->
  Mealy (Boundary k a) (Maybe b)
markMealy isHalt (Mealy inject step extract) =
  Mealy
    ( \case
        Payload a -> Left (inject a)
        Mark k -> if isHalt k then Right () else Left (inject (error "markMealy: initial mark without payload"))
    )
    ( \case
        Left s -> \case
          Payload a -> Left (step s a)
          Mark k -> if isHalt k then Right () else Left s
        Right () -> const (Right ())
    )
    ( \case
        Left s -> Just (extract s)
        Right () -> Nothing
    )

-- | A schedule as a standalone mark machine.
--
-- 'Pick' is a mark alphabet: each step receipts which poles crossed the
-- medium, and the pick stream of a run is the run's decision transcript.
-- The seed is the shared channel's initial value — the explicit discharge
-- of pointing (see 'Circuit.Equip.UnitCell').
--
-- >>> import Circuit.Shared (Pick (..), Schedule (..))
-- >>> let alt = Schedule (\s -> (s + 1, if odd s then PickL else PickR))
-- >>> scanProcess (scheduleAsProcess 0 alt) [(), (), (), ()]
-- [PickL,PickR,PickL,PickR]
scheduleAsProcess :: s -> Schedule s -> Process s () Pick
scheduleAsProcess s0 sched =
  Process s0 (\s _ -> fst (chooseS sched s)) (\s -> snd (chooseS sched s))

-- * Channel-pole processes

-- | Build a pointed process from channel poles.
polesToProcess :: Poles s s (Body (,) s (->)) (Body (,) s (->)) a b -> s -> Process s a b
polesToProcess p s0 =
  let Body write = conjoint p
      Body receive = companion p
   in Process s0 (\s a -> fst (write (s, a))) (\s -> snd (receive (s, s)))

-- | Run channel poles over a list of inputs.
runPoles :: Poles s s (Body (,) s (->)) (Body (,) s (->)) a b -> s -> [a] -> [b]
runPoles p s0 xs = scanProcess (polesToProcess p s0) xs

-- * Functorial plumbing

-- | 'fmap' postcomposes a pure function on the output of a process.
instance Functor (Mealy a) where
  fmap f (Mealy i st ex) = Mealy i st (f . ex)
  {-# INLINEABLE fmap #-}

-- | 'pure' produces a constant process; '<*>' pairs states and applies the
-- left output to the right output.
instance Applicative (Mealy a) where
  pure b = Mealy (const ()) (\_ _ -> ()) (const b)
  {-# INLINEABLE pure #-}
  Mealy i1 st1 ex1 <*> Mealy i2 st2 ex2 =
    Mealy
      (\a -> (i1 a, i2 a))
      (\(s1, s2) a -> (st1 s1 a, st2 s2 a))
      (\(s1, s2) -> ex1 s1 (ex2 s2))
  {-# INLINEABLE (<*>) #-}

-- | Precompose a pure function before a process.
before :: Mealy b c -> (a -> b) -> Mealy a c
before (Mealy i st ex) f = Mealy (i . f) (\s a -> st s (f a)) ex
{-# INLINEABLE before #-}

-- | Postcompose a pure function after a process.
after :: Mealy a b -> (b -> c) -> Mealy a c
after (Mealy i st ex) f = Mealy i st (f . ex)
{-# INLINEABLE after #-}

-- | Run two processes on the same input and combine their outputs.
parWith :: (x -> y -> z) -> Mealy a x -> Mealy a y -> Mealy a z
parWith = liftA2
{-# INLINEABLE parWith #-}

-- | Run three processes on the same input and combine their outputs.
parWith3 :: (x -> y -> z -> w) -> Mealy a x -> Mealy a y -> Mealy a z -> Mealy a w
parWith3 = liftA3
{-# INLINEABLE parWith3 #-}

-- | Run four processes on the same input and combine their outputs.
parWith4 :: (w -> x -> y -> z -> r) -> Mealy a w -> Mealy a x -> Mealy a y -> Mealy a z -> Mealy a r
parWith4 f p1 p2 p3 p4 = liftA2 (\w (x, y, z) -> f w x y z) p1 (liftA3 (,,) p2 p3 p4)
{-# INLINEABLE parWith4 #-}

-- * Category

instance Category Mealy where
  id :: Mealy a a
  id = Mealy id const id
  {-# INLINE id #-}

  (.) :: Mealy b c -> Mealy a b -> Mealy a c
  Mealy i2 st2 ex2 . Mealy i1 st1 ex1 =
    Mealy
      (\a -> let s1 = i1 a in (s1, i2 (ex1 s1)))
      ( \(s1, s2) a ->
          let s1' = st1 s1 a
              s2' = st2 s2 (ex1 s1')
           in (s1', s2')
      )
      (\(_, s2) -> ex2 s2)
  {-# INLINE (.) #-}

-- Assoc / Slide / Strength / Yank for (,)
--
-- These instances make Mealy a traced monoidal category under the cartesian
-- tensor. The yank ties a lazy self-referential knot and is productive only
-- when the body is non-strict in the feedback channel. Strict accumulators
-- (e.g. moving averages) diverge under the (,) yank; use Either-trace 'run'
-- or the 'register' combinator for those.

instance Assoc (,) Mealy where
  assoc = Mealy id (\_ x -> x) (\(~((a, b), c)) -> (a, (b, c)))
  assoc' = Mealy id (\_ x -> x) (\(a, ~(b, c)) -> ((a, b), c))

instance Slide (,) Mealy where
  slide = Mealy id (\_ x -> x) (\(a, ~(b, c)) -> (b, (a, c)))

instance Strength (,) Mealy where
  strength (Mealy i st ex) =
    Mealy
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', st s b))
      (\(~(a, s)) -> (a, ex s))

instance Yank (,) Mealy where
  yank (Mealy i st ex) =
    Mealy
      (\b -> let s0 = i (a0, b); a0 = fst (ex s0) in s0)
      ( \s b ->
          let (s', _a) = fix (\ ~(s'', a') -> (st s (a', b), fst (ex s'')))
           in s'
      )
      (snd . ex)
    where
      fix f = let x = f x in x

-- Tensor / Action / Shared for (,)
--
-- These instances make @Mealy@ a cartesian monoidal category in its own
-- right, so it can serve as a base category for shared-medium fusion and
-- for @Trace (,) Mealy@.

instance Unital (,) Mealy where
  unitl = Mealy snd (\_ (_, a) -> a) id
  unitl' = Mealy id const ((),)
  unitr = Mealy fst (\_ (a, ()) -> a) id
  unitr' = Mealy id const (,())

instance Tensor (,) Mealy where
  tensor (Mealy i1 st1 ex1) (Mealy i2 st2 ex2) =
    Mealy
      (bimap i1 i2)
      (\(s1, s2) (a, c) -> (st1 s1 a, st2 s2 c))
      (bimap ex1 ex2)
  {-# INLINE tensor #-}

instance Action (,) Mealy where
  braid = Mealy id (const id) sw
    where
      sw (a, b) = (b, a)
  {-# INLINE braid #-}

-- | Cartesian shared fusion on processes.
--
-- The two processes share one feedback channel @s@. At each tick the schedule
-- chooses which body advances; the gated body's input is discarded and it does
-- not step. Each process is injected lazily on its first firing, so a body that
-- is never scheduled consumes no inputs and produces no outputs.
instance Shared (,) Mealy where
  sharedBy sched (Mealy iL stL exL) (Mealy iR stR exR) =
    Mealy inject step extract
    where
      inject (s, (a, c)) =
        let (s', pick) = chooseS sched s
         in runInject pick s' a c

      step (msL, msR, _, _) (sIn, (a, c)) =
        let (s', pick) = chooseS sched sIn
         in runStep pick msL msR s' a c

      extract (_, _, s, out) = (s, out)

      runInject pick s' a c = case pick of
        PickL ->
          let sL0 = iL (s', a)
              (s'', b) = exL sL0
           in (Just sL0, Nothing, s'', This b)
        PickR ->
          let sR0 = iR (s', c)
              (s'', d) = exR sR0
           in (Nothing, Just sR0, s'', That d)
        Both LeftFirst ->
          let sL0 = iL (s', a)
              (sMid, b) = exL sL0
              sR0 = iR (sMid, c)
              (sOut, d) = exR sR0
           in (Just sL0, Just sR0, sOut, These b d)
        Both RightFirst ->
          let sR0 = iR (s', c)
              (sMid, d) = exR sR0
              sL0 = iL (sMid, a)
              (sOut, b) = exL sL0
           in (Just sL0, Just sR0, sOut, These b d)

      runStep pick msL msR s' a c = case pick of
        PickL ->
          let sL = fromMaybe (iL (s', a)) msL
              sL' = stL sL (s', a)
              (s'', b) = exL sL'
           in (Just sL', msR, s'', This b)
        PickR ->
          let sR = fromMaybe (iR (s', c)) msR
              sR' = stR sR (s', c)
              (s'', d) = exR sR'
           in (msL, Just sR', s'', That d)
        Both LeftFirst ->
          let sL = fromMaybe (iL (s', a)) msL
              sL' = stL sL (s', a)
              (s'', b) = exL sL'
              sR = fromMaybe (iR (s'', c)) msR
              sR' = stR sR (s'', c)
              (s''', d) = exR sR'
           in (Just sL', Just sR', s''', These b d)
        Both RightFirst ->
          let sR = fromMaybe (iR (s', c)) msR
              sR' = stR sR (s', c)
              (s'', d) = exR sR'
              sL = fromMaybe (iL (s'', a)) msL
              sL' = stL sL (s'', a)
              (s''', b) = exL sL'
           in (Just sL', Just sR', s''', These b d)
  {-# INLINE sharedBy #-}

-- Assoc / Slide / Strength / Yank for Either
--
-- These instances make Mealy a traced monoidal category under the Either
-- tensor. The yank is per-tick Conway/Elgot settle: Right injects a value,
-- Left feeds intermediate state back within the same tick until Right exits.
-- This is the instance required by 'Net Either Mealy' knot bodies.

instance Assoc Either Mealy where
  assoc = Mealy id (\_ x -> x) assocEither
    where
      assocEither (Left (Left a)) = Left a
      assocEither (Left (Right b)) = Right (Left b)
      assocEither (Right c) = Right (Right c)
  assoc' = Mealy id (\_ x -> x) assocEither'
    where
      assocEither' (Left a) = Left (Left a)
      assocEither' (Right (Left b)) = Left (Right b)
      assocEither' (Right (Right c)) = Right c

instance Slide Either Mealy where
  slide = Mealy id (\_ x -> x) slideEither
    where
      slideEither (Left a) = Right (Left a)
      slideEither (Right (Left b)) = Left b
      slideEither (Right (Right c)) = Right (Right c)

instance Strength Either Mealy where
  strength (Mealy i st ex) =
    Mealy
      (\case Left a -> (Nothing, Left a); Right b -> let s0 = i b in (Just s0, Right (ex s0)))
      ( \(ms, _) -> \case
          Left a -> (ms, Left a)
          Right b -> case ms of
            Nothing -> let s0 = i b in (Just s0, Right (ex s0))
            Just s -> let s' = st s b in (Just s', Right (ex s'))
      )
      snd

instance Yank Either Mealy where
  yank (Mealy i st ex) = Mealy i' st' ex'
    where
      settle m = case ex m of
        Left s -> settle (st m (Left s))
        Right _ -> m

      i' a = settle (i (Right a))
      st' m a = settle (st m (Right a))
      ex' m = case ex m of
        Right b -> b
        Left _ -> error "Circuit.Process.Yank Either: unsettled state"

-- * Bimonoid instances (pointwise lift)

instance (Copy (->) a) => Copy Mealy a where
  copy = Mealy id (\_ x -> x) Bm.copy

instance Discard Mealy a where
  discard = Mealy id (\_ x -> x) (const ())

instance (Merge (->) a) => Merge Mealy a where
  plus = Mealy id (\_ x -> x) Bm.plus

instance (Zero (->) a) => Zero Mealy a where
  zero = Mealy id (\_ x -> x) Bm.zero

-- * Runners

-- | Run a process over any stream with an 'Uncons' coalgebra and build the
-- output with a 'Cons' algebra.
--
-- The first element seeds the hidden channel via @inject@; each subsequent
-- element steps it via @step@; each output is @extract@ of the current channel.
scanStream :: forall f a g b. (Uncons f a, Cons g b) => Mealy a b -> f -> g
scanStream (Mealy inject step extract) = goInit
  where
    nilG :: g
    nilG = consNil @g @b

    consG :: b -> g -> g
    consG = cons

    goInit f = case uncons f of
      That _ -> nilG
      This a -> let s0 = inject a in consG (extract s0) nilG
      These a rest -> let s0 = inject a in consG (extract s0) (go s0 rest)

    go s f = case uncons f of
      That _ -> nilG
      This a -> let s' = step s a in consG (extract s') nilG
      These a rest -> let s' = step s a in consG (extract s') (go s' rest)

-- | List specialization of 'scanStream'.
scan :: Mealy a b -> [a] -> [b]
scan = scanStream
{-# INLINE scan #-}

-- | Run a pointed process over a list, starting from its stored seed.
--
-- Output at each step is 'processExtract' of the state /after/ consuming the
-- input, matching the 'Mealy' semantics of 'scan'.
scanProcess :: Process s a b -> [a] -> [b]
scanProcess pp = go (processSeed pp)
  where
    go _ [] = []
    go s (a : as) =
      let s' = processStep pp s a
       in processExtract pp s' : go s' as
{-# INLINEABLE scanProcess #-}

-- | Run a pointed process over a list, producing the outputs /and/ the final
-- state in a single pass.
runProcess :: Process s a b -> [a] -> ([b], s)
runProcess pp xs = go (processSeed pp) xs []
  where
    go s [] acc = (reverse acc, s)
    go s (a : as) acc =
      let s' = processStep pp s a
       in go s' as (processExtract pp s' : acc)
{-# INLINEABLE runProcess #-}

-- | Final state after consuming a list of inputs.
finalProcess :: Process s a b -> [a] -> s
finalProcess pp = snd . runProcess pp
{-# INLINEABLE finalProcess #-}

-- | Run a process over a stream, returning the final output (if any).
foldStream :: (Uncons f a) => Mealy a b -> f -> Maybe b
foldStream (Mealy inject step extract) = goInit
  where
    goInit f = case uncons f of
      That _ -> Nothing
      This a -> Just (extract (inject a))
      These a rest -> Just (go (inject a) rest)

    go s f = case uncons f of
      That _ -> extract s
      This a -> extract (step s a)
      These a rest -> go (step s a) rest

-- | List specialization of 'foldStream'.
fold :: Mealy a b -> [a] -> Maybe b
fold = foldStream
{-# INLINE fold #-}

-- | Run a pointed process over a list, returning the final output (if any).
foldProcess :: Process s a b -> [a] -> Maybe b
foldProcess pp = go (processSeed pp)
  where
    go _ [] = Nothing
    go s [a] = Just (processExtract pp (processStep pp s a))
    go s (a : as) = go (processStep pp s a) as
{-# INLINEABLE foldProcess #-}

-- | Encode a process as a stream-level 'Trace' over arbitrary 'Uncons'/'Cons'
-- streams.
--
-- This is the definitional runner: 'scanStream' is 'Circuit.Syntax.eval'
-- composed with 'encodeStream'. The feedback channel carries
-- @(Maybe channel, remaining input, accumulated output)@.
encodeStream :: forall f a g b. (Uncons f a, Cons g b) => Mealy a b -> Trace Either (->) f g
encodeStream (Mealy inject step extract) = yank (base b)
  where
    Body b =
      Body $ \case
        Right f -> case uncons f of
          That _ -> Right nilG
          This a ->
            let ch0 = inject a
             in Left (Just ch0, nilF, [extract ch0])
          These a rest ->
            let ch0 = inject a
             in Left (Just ch0, rest, [extract ch0])
        Left (Nothing, _, _) -> error "encodeStream: feedback reached before first input"
        Left (Just ch, f, bs) -> case uncons f of
          That _ -> Right (foldl (flip consG) nilG bs)
          This a ->
            let ch' = step ch a
             in Left (Just ch', nilF, extract ch' : bs)
          These a rest ->
            let ch' = step ch a
             in Left (Just ch', rest, extract ch' : bs)

    nilF :: f
    nilF = nil @f @a

    nilG :: g
    nilG = consNil @g @b

    consG :: b -> g -> g
    consG = cons

-- | List specialization of 'encodeStream'.
encodeList :: Mealy a b -> Trace Either (->) [a] [b]
encodeList = encodeStream
{-# INLINE encodeList #-}

-- * Mealy-style processes

-- | Build a 'Mealy' from a Mealy-style step.
--
-- The output may depend on the current input. The channel internally stores the
-- most recent output so that the Machine-style 'Mealy' interface is preserved.
mealy :: ch -> (ch -> a -> (ch, Maybe b)) -> Mealy a (Maybe b)
mealy ch0 step = Mealy inject step' extract
  where
    inject a =
      let (ch, mb) = step ch0 a
       in (ch, mb)
    step' (ch, _) a =
      let (ch', mb') = step ch a
       in (ch', mb')
    extract = snd
{-# INLINEABLE mealy #-}

-- | Collect the emitted outputs of a 'Mealy (Maybe b)' over any stream.
runMealyStream :: forall f a g b. (Uncons f a, Cons g b) => Mealy a (Maybe b) -> f -> g
runMealyStream (Mealy inject step extract) = goInit
  where
    nilG :: g
    nilG = consNil @g @b

    consG :: b -> g -> g
    consG = cons

    emit ch rest = case extract ch of
      Nothing -> rest
      Just b -> consG b rest

    goInit f = case uncons f of
      That _ -> nilG
      This a -> let ch0 = inject a in emit ch0 nilG
      These a rest -> let ch0 = inject a in emit ch0 (go ch0 rest)

    go ch f = case uncons f of
      That _ -> nilG
      This a -> let ch' = step ch a in emit ch' nilG
      These a rest -> let ch' = step ch a in emit ch' (go ch' rest)

-- | List specialization of 'runMealyStream'.
runMealy :: Mealy a (Maybe b) -> [a] -> [b]
runMealy = runMealyStream
{-# INLINEABLE runMealy #-}

-- * Cross-tick feedback

-- | One-tick delay with an initial value.
--
-- Output is @s0@ on the first tick and the input from the previous tick
-- thereafter. This is the primitive that makes 'register' productive: the
-- feedback wire is observable one tick late.
delay :: s -> Mealy s s
delay s0 = Mealy (const s0) (const id) id

-- | Cross-tick register feedback.
--
-- Given an initial feedback value @s0@ and a process @Mealy (a, s) (b, s)@,
-- close the @s@ wire so that the @s@ produced at one tick is fed back as
-- input at the next tick. This is the productive, strict-accumulator-safe
-- analogue of the cartesian trace: the delay is explicit in the wiring
-- rather than implicit in a lazy knot.
--
-- Compare with the cartesian 'yank' on 'Mealy', which ties a lazy knot
-- and diverges for strict state; 'register' keeps strict state cells sound
-- by making the one-tick delay observable.
--
-- For bodies whose fixed-point is independent of the initial feedback value
-- (e.g. affine/stateless feedback such as @ewmaBody@), the same wiring can
-- be expressed by swapping the feedback wire into the active position,
-- applying 'strength' ('delay' s0), and tracing.
register :: s -> Mealy (a, s) (b, s) -> Mealy a b
register s0 (Mealy i st ex) = Mealy i' st' ex'
  where
    i' a = i (a, s0)
    st' s a = st s (a, snd (ex s))
    ex' s = fst (ex s)

-- * Body conversions

-- | Convert a pointed process into a cartesian body threading the state.
--
-- The body state is the process state and the output is the process output
-- of the state after consuming the input, so 'runBody' from the seed
-- reproduces 'scanProcess'.
--
-- >>> let acc = Process 0 (+) (\x -> x) :: Process Int Int Int
-- >>> runBody (processToBody acc) 0 [1, 2, 3]
-- [1,3,6]
processToBody :: Process s a b -> Body (,) s (->) a b
processToBody pp =
  Body $ \(s, a) ->
    let s' = processStep pp s a
     in (s', processExtract pp s')
{-# INLINEABLE processToBody #-}

-- | Eliminate a 'Mealy' by exposing its hidden state as a cartesian body.
--
-- The continuation receives the seeding function ('Mealy' inject) together
-- with the body threading the hidden state: 'runBody' seeded by
-- @inject a0@ reproduces 'scan' after its first output.
--
-- >>> let acc = Process 0 (+) (\x -> x) :: Process Int Int Int
-- >>> scan (asMealy acc) [0, 1, 2, 3]
-- [0,1,3,6]
-- >>> mealyToSomeBody (asMealy acc) (\inj b -> runBody b (inj 0) [1, 2, 3])
-- [1,3,6]
mealyToSomeBody :: Mealy a b -> (forall s. (a -> s) -> Body (,) s (->) a b -> r) -> r
mealyToSomeBody (Mealy inject step extract) k =
  k inject (Body $ \(s, a) -> let s' = step s a in (s', extract s'))
{-# INLINEABLE mealyToSomeBody #-}

-- | View a cartesian body as a 'Mealy'.
--
-- The body state @s@ becomes the process state, paired with the most recent
-- output so that the Machine-style @extract@ can be defined.
bodyToMealy :: Body (,) s (->) a b -> s -> Mealy a b
bodyToMealy (Body f) s0 = Mealy inject step extract
  where
    inject a = f (s0, a)
    step (s, _) a' = f (s, a')
    extract = snd
{-# INLINEABLE bodyToMealy #-}

-- | Run a cartesian body over a list of inputs.
runBody :: Body (,) s (->) a b -> s -> [a] -> [b]
runBody body s0 = scan (bodyToMealy body s0)
{-# INLINEABLE runBody #-}

-- | Run a body from a 'Circuit.Equip.UnitCell' instead of a bare seed.
--
-- Agrees with the ad-hoc seed runner:
--
-- >>> import Circuit.Body (Body (..))
-- >>> import Circuit.Equip (unitCell)
-- >>> let adder = Body (\(s, a) -> (s + a, s)) :: Body (,) Int (->) Int Int
-- >>> runBody adder 3 [1, 2, 3]
-- [3,4,6]
-- >>> runBodyCell adder (unitCell (const 3)) [1, 2, 3]
-- [3,4,6]
runBodyCell :: Body (,) s (->) a b -> UnitCell (,) (->) s -> [a] -> [b]
runBodyCell body (UnitCell f) = runBody body (f ())
