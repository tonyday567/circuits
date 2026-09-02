{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A pointed stateful process from @a@ to @b@.
--
-- @
-- data Process a b = forall s. Process (a -> s) (s -> a -> s) (s -> b)
-- @
--
-- 'Process' is the circuits-native carrier for streaming state machines: the
-- interface is a monomial @a -> b@ stream transformer and the initial state is
-- supplied by the first input. The underlying span-shaped carrier is
-- 'Circuit.Body.Body'.
--
-- * @inject@ converts the first input into an initial state.
-- * @step@ updates the state given the current input.
-- * @extract@ produces the output from the current state.
--
-- This is intended to replace the hand-rolled state-machine arrow: stats
-- packages become boxes @Process a b@, while the arrow itself lives in the
-- substrate next to 'Circuit.Trace' and 'Circuit.Net'.
--
-- The semantics are intentionally tied to the circuits substrate:
--
-- * 'scan' is the reference runner over lists.
-- * 'scanStream' generalizes this to any 'Uncons' input and 'Cons' output.
-- * 'encodeList' maps a process into a stream-level 'Trace' 'Either' @(->)@ over
--   lists; the two runners are verified equivalent by oracle.
-- * The arrow-level 'Yank' Either instance is per-tick Conway/Elgot settle,
--   not cross-tick state feedback; see 'register' for the latter.
--
-- = Pointed systems
--
-- The pointed-Moore view of a stateful morphism lives in 'Circuit.Moore', which
-- builds polynomial interfaces on top of this monomial carrier.
module Circuit.Process
  ( -- * Stream transformer (monomial special case)
    Process (..),

    -- * Pointed process (explicit seed)
    PProcess (..),
    asProcess,

    -- * Moore conversions
    asPProcess,
    mooreAsProcess,

    -- * Boundary machines
    markPProcess,
    markProcess,

    -- * Channel-pole processes
    polesToPProcess,
    runPoles,

    -- * Functorial plumbing
    before,
    after,
    parWith,
    parWith3,
    parWith4,

    -- * Runners
    scan,
    scanPProcess,
    runPProcess,
    finalPProcess,
    scanStream,
    fold,
    foldPProcess,
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
    bodyToProcess,
    runBody,
  )
where

import Circuit.Bimonoid (Copy, CopyDiscard, Discard, Merge, MergeZero, Zero)
import Circuit.Bimonoid qualified as Bm
import Circuit.Body (Body (..))
import Circuit.Boundary (Boundary (..))
import Circuit.Category (Category (..))
import Circuit.Moore (Moore, monoDir, monoIn, mooreMorphism, toEvalMoore)
import Circuit.Poles (Poles)
import Circuit.Poles qualified as Poles
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
data Process a b where
  Process ::
    forall s a b.
    (a -> s) ->
    (s -> a -> s) ->
    (s -> b) ->
    Process a b

-- | A pointed process with an explicit seed.
--
-- This is the same data as 'Process' except the initial state @s0@ is exposed
-- rather than computed from the first input. Every tick is uniform: state in,
-- input in, state out, output out.
data PProcess s a b = PProcess
  { pprocessSeed :: s,
    pprocessStep :: s -> a -> s,
    pprocessExtract :: s -> b
  }

-- | Forget the explicit seed of a 'PProcess', yielding a 'Process' whose
-- first input creates the initial state via 'pprocessStep'.
asProcess :: PProcess s a b -> Process a b
asProcess (PProcess s0 step extract) =
  Process (\a -> step s0 a) step extract
{-# INLINEABLE asProcess #-}

-- * Moore conversions

-- | Convert a monomial @(->)@ Moore machine into a pointed process.
asPProcess :: Moore (,) s (->) (Mono i o) -> s -> PProcess s i o
asPProcess sys s0 = PProcess s0 step' extract'
  where
    step' s i = case toEvalMoore sys s of EP (EK _, EE f) -> f i
    extract' s = case toEvalMoore sys s of EP (EK o, EE _) -> o

-- | Convert a monomial @(->)@ Moore machine into a process.
mooreAsProcess :: Moore (,) s (->) (Mono i o) -> s -> Process i o
mooreAsProcess sys s0 = asProcess (asPProcess sys s0)

-- * Boundary machines

-- | Mark-driven halt combinator for pointed processes.
markPProcess ::
  (k -> Bool) ->
  PProcess s a b ->
  PProcess (Either s s) (Boundary k a) (Maybe b)
markPProcess isHalt (PProcess s0 step extract) =
  PProcess
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
markProcess ::
  (k -> Bool) ->
  Process a b ->
  Process (Boundary k a) (Maybe b)
markProcess isHalt (Process inject step extract) =
  Process
    ( \case
        Payload a -> Left (inject a)
        Mark k -> if isHalt k then Right () else Left (inject (error "markProcess: initial mark without payload"))
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

-- * Channel-pole processes

-- | Build a pointed process from channel poles.
polesToPProcess :: Poles (Body (,) s (->)) a b -> s -> PProcess s a b
polesToPProcess p s0 =
  let (Body write, Body receive) = Poles.splay0 p
   in PProcess s0 (\s a -> fst (write (s, a))) (\s -> snd (receive (s, ())))

-- | Run channel poles over a list of inputs.
runPoles :: Poles (Body (,) s (->)) a b -> s -> [a] -> [b]
runPoles p s0 xs = scanPProcess (polesToPProcess p s0) xs

-- * Functorial plumbing

-- | 'fmap' postcomposes a pure function on the output of a process.
instance Functor (Process a) where
  fmap f (Process i st ex) = Process i st (f . ex)
  {-# INLINEABLE fmap #-}

-- | 'pure' produces a constant process; '<*>' pairs states and applies the
-- left output to the right output.
instance Applicative (Process a) where
  pure b = Process (const ()) (\_ _ -> ()) (const b)
  {-# INLINEABLE pure #-}
  Process i1 st1 ex1 <*> Process i2 st2 ex2 =
    Process
      (\a -> (i1 a, i2 a))
      (\(s1, s2) a -> (st1 s1 a, st2 s2 a))
      (\(s1, s2) -> ex1 s1 (ex2 s2))
  {-# INLINEABLE (<*>) #-}

-- | Precompose a pure function before a process.
before :: Process b c -> (a -> b) -> Process a c
before (Process i st ex) f = Process (i . f) (\s a -> st s (f a)) ex
{-# INLINEABLE before #-}

-- | Postcompose a pure function after a process.
after :: Process a b -> (b -> c) -> Process a c
after (Process i st ex) f = Process i st (f . ex)
{-# INLINEABLE after #-}

-- | Run two processes on the same input and combine their outputs.
parWith :: (x -> y -> z) -> Process a x -> Process a y -> Process a z
parWith = liftA2
{-# INLINEABLE parWith #-}

-- | Run three processes on the same input and combine their outputs.
parWith3 :: (x -> y -> z -> w) -> Process a x -> Process a y -> Process a z -> Process a w
parWith3 = liftA3
{-# INLINEABLE parWith3 #-}

-- | Run four processes on the same input and combine their outputs.
parWith4 :: (w -> x -> y -> z -> r) -> Process a w -> Process a x -> Process a y -> Process a z -> Process a r
parWith4 f p1 p2 p3 p4 = liftA2 (\w (x, y, z) -> f w x y z) p1 (liftA3 (,,) p2 p3 p4)
{-# INLINEABLE parWith4 #-}

-- * Category

instance Category Process where
  id :: Process a a
  id = Process id const id
  {-# INLINE id #-}

  (.) :: Process b c -> Process a b -> Process a c
  Process i2 st2 ex2 . Process i1 st1 ex1 =
    Process
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
-- These instances make Process a traced monoidal category under the cartesian
-- tensor. The yank ties a lazy self-referential knot and is productive only
-- when the body is non-strict in the feedback channel. Strict accumulators
-- (e.g. moving averages) diverge under the (,) yank; use Either-trace 'run'
-- or the 'register' combinator for those.

instance Assoc (,) Process where
  assoc = Process id (\_ x -> x) (\(~((a, b), c)) -> (a, (b, c)))
  assoc' = Process id (\_ x -> x) (\(a, ~(b, c)) -> ((a, b), c))

instance Slide (,) Process where
  slide = Process id (\_ x -> x) (\(a, ~(b, c)) -> (b, (a, c)))

instance Strength (,) Process where
  strength (Process i st ex) =
    Process
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', st s b))
      (\(~(a, s)) -> (a, ex s))

instance Yank (,) Process where
  yank (Process i st ex) =
    Process
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
-- These instances make @Process@ a cartesian monoidal category in its own
-- right, so it can serve as a base category for shared-medium fusion and
-- for @Trace (,) Process@.

instance Unital (,) Process where
  unitl = Process snd (\_ (_, a) -> a) id
  unitl' = Process id const ((),)
  unitr = Process fst (\_ (a, ()) -> a) id
  unitr' = Process id const (,())

instance Tensor (,) Process where
  tensor (Process i1 st1 ex1) (Process i2 st2 ex2) =
    Process
      (bimap i1 i2)
      (\(s1, s2) (a, c) -> (st1 s1 a, st2 s2 c))
      (bimap ex1 ex2)
  {-# INLINE tensor #-}

instance Action (,) Process where
  braid = Process id (const id) sw
    where
      sw (a, b) = (b, a)
  {-# INLINE braid #-}

-- | Cartesian shared fusion on processes.
--
-- The two processes share one feedback channel @s@. At each tick the schedule
-- chooses which body advances; the gated body's input is discarded and it does
-- not step. Each process is injected lazily on its first firing, so a body that
-- is never scheduled consumes no inputs and produces no outputs.
instance Shared (,) Process where
  sharedBy sched (Process iL stL exL) (Process iR stR exR) =
    Process inject step extract
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
-- These instances make Process a traced monoidal category under the Either
-- tensor. The yank is per-tick Conway/Elgot settle: Right injects a value,
-- Left feeds intermediate state back within the same tick until Right exits.
-- This is the instance required by 'Net Either Process' knot bodies.

instance Assoc Either Process where
  assoc = Process id (\_ x -> x) assocEither
    where
      assocEither (Left (Left a)) = Left a
      assocEither (Left (Right b)) = Right (Left b)
      assocEither (Right c) = Right (Right c)
  assoc' = Process id (\_ x -> x) assocEither'
    where
      assocEither' (Left a) = Left (Left a)
      assocEither' (Right (Left b)) = Left (Right b)
      assocEither' (Right (Right c)) = Right c

instance Slide Either Process where
  slide = Process id (\_ x -> x) slideEither
    where
      slideEither (Left a) = Right (Left a)
      slideEither (Right (Left b)) = Left b
      slideEither (Right (Right c)) = Right (Right c)

instance Strength Either Process where
  strength (Process i st ex) =
    Process
      (\case Left a -> (Nothing, Left a); Right b -> let s0 = i b in (Just s0, Right (ex s0)))
      ( \(ms, _) -> \case
          Left a -> (ms, Left a)
          Right b -> case ms of
            Nothing -> let s0 = i b in (Just s0, Right (ex s0))
            Just s -> let s' = st s b in (Just s', Right (ex s'))
      )
      snd

instance Yank Either Process where
  yank (Process i st ex) = Process i' st' ex'
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

instance (Copy (->) a) => Copy Process a where
  copy = Process id (\_ x -> x) Bm.copy

instance Discard Process a where
  discard = Process id (\_ x -> x) (const ())

instance (Merge (->) a) => Merge Process a where
  plus = Process id (\_ x -> x) Bm.plus

instance (Zero (->) a) => Zero Process a where
  zero = Process id (\_ x -> x) Bm.zero

-- * Runners

-- | Run a process over any stream with an 'Uncons' coalgebra and build the
-- output with a 'Cons' algebra.
--
-- The first element seeds the hidden channel via @inject@; each subsequent
-- element steps it via @step@; each output is @extract@ of the current channel.
scanStream :: forall f a g b. (Uncons f a, Cons g b) => Process a b -> f -> g
scanStream (Process inject step extract) = goInit
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
scan :: Process a b -> [a] -> [b]
scan = scanStream
{-# INLINE scan #-}

-- | Run a pointed process over a list, starting from its stored seed.
--
-- Output at each step is 'pprocessExtract' of the state /after/ consuming the
-- input, matching the 'Process' semantics of 'scan'.
scanPProcess :: PProcess s a b -> [a] -> [b]
scanPProcess pp = go (pprocessSeed pp)
  where
    go _ [] = []
    go s (a : as) =
      let s' = pprocessStep pp s a
       in pprocessExtract pp s' : go s' as
{-# INLINEABLE scanPProcess #-}

-- | Run a pointed process over a list, producing the outputs /and/ the final
-- state in a single pass.
runPProcess :: PProcess s a b -> [a] -> ([b], s)
runPProcess pp xs = go (pprocessSeed pp) xs []
  where
    go s [] acc = (reverse acc, s)
    go s (a : as) acc =
      let s' = pprocessStep pp s a
       in go s' as (pprocessExtract pp s' : acc)
{-# INLINEABLE runPProcess #-}

-- | Final state after consuming a list of inputs.
finalPProcess :: PProcess s a b -> [a] -> s
finalPProcess pp = snd . runPProcess pp
{-# INLINEABLE finalPProcess #-}

-- | Run a process over a stream, returning the final output (if any).
foldStream :: (Uncons f a) => Process a b -> f -> Maybe b
foldStream (Process inject step extract) = goInit
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
fold :: Process a b -> [a] -> Maybe b
fold = foldStream
{-# INLINE fold #-}

-- | Run a pointed process over a list, returning the final output (if any).
foldPProcess :: PProcess s a b -> [a] -> Maybe b
foldPProcess pp = go (pprocessSeed pp)
  where
    go _ [] = Nothing
    go s [a] = Just (pprocessExtract pp (pprocessStep pp s a))
    go s (a : as) = go (pprocessStep pp s a) as
{-# INLINEABLE foldPProcess #-}

-- | Encode a process as a stream-level 'Trace' over arbitrary 'Uncons'/'Cons'
-- streams.
--
-- This is the definitional runner: 'scanStream' is 'Circuit.Syntax.eval'
-- composed with 'encodeStream'. The feedback channel carries
-- @(Maybe channel, remaining input, accumulated output)@.
encodeStream :: forall f a g b. (Uncons f a, Cons g b) => Process a b -> Trace Either (->) f g
encodeStream (Process inject step extract) = yank (base b)
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
encodeList :: Process a b -> Trace Either (->) [a] [b]
encodeList = encodeStream
{-# INLINE encodeList #-}

-- * Mealy-style processes

-- | Build a 'Process' from a Mealy-style step.
--
-- The output may depend on the current input. The channel internally stores the
-- most recent output so that the Moore-style 'Process' interface is preserved.
mealy :: ch -> (ch -> a -> (ch, Maybe b)) -> Process a (Maybe b)
mealy ch0 step = Process inject step' extract
  where
    inject a =
      let (ch, mb) = step ch0 a
       in (ch, mb)
    step' (ch, _) a =
      let (ch', mb') = step ch a
       in (ch', mb')
    extract = snd
{-# INLINEABLE mealy #-}

-- | Collect the emitted outputs of a 'Process (Maybe b)' over any stream.
runMealyStream :: forall f a g b. (Uncons f a, Cons g b) => Process a (Maybe b) -> f -> g
runMealyStream (Process inject step extract) = goInit
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
runMealy :: Process a (Maybe b) -> [a] -> [b]
runMealy = runMealyStream
{-# INLINEABLE runMealy #-}

-- * Cross-tick feedback

-- | One-tick delay with an initial value.
--
-- Output is @s0@ on the first tick and the input from the previous tick
-- thereafter. This is the primitive that makes 'register' productive: the
-- feedback wire is observable one tick late.
delay :: s -> Process s s
delay s0 = Process (const s0) (const id) id

-- | Cross-tick register feedback.
--
-- Given an initial feedback value @s0@ and a process @Process (a, s) (b, s)@,
-- close the @s@ wire so that the @s@ produced at one tick is fed back as
-- input at the next tick. This is the productive, strict-accumulator-safe
-- analogue of the cartesian trace: the delay is explicit in the wiring
-- rather than implicit in a lazy knot.
--
-- Compare with the cartesian 'yank' on 'Process', which ties a lazy knot
-- and diverges for strict state; 'register' keeps strict state cells sound
-- by making the one-tick delay observable.
--
-- For bodies whose fixed-point is independent of the initial feedback value
-- (e.g. affine/stateless feedback such as @ewmaBody@), the same wiring can
-- be expressed by swapping the feedback wire into the active position,
-- applying 'strength' ('delay' s0), and tracing.
register :: s -> Process (a, s) (b, s) -> Process a b
register s0 (Process i st ex) = Process i' st' ex'
  where
    i' a = i (a, s0)
    st' s a = st s (a, snd (ex s))
    ex' s = fst (ex s)

-- * Body conversions

-- | View a cartesian body as a 'Process'.
--
-- The body state @s@ becomes the process state, paired with the most recent
-- output so that the Moore-style @extract@ can be defined.
bodyToProcess :: Body (,) s (->) a b -> s -> Process a b
bodyToProcess (Body f) s0 = Process inject step extract
  where
    inject a = f (s0, a)
    step (s, _) a' = f (s, a')
    extract = snd
{-# INLINEABLE bodyToProcess #-}

-- | Run a cartesian body over a list of inputs.
runBody :: Body (,) s (->) a b -> s -> [a] -> [b]
runBody body s0 = scan (bodyToProcess body s0)
{-# INLINEABLE runBody #-}
