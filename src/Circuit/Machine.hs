{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Input-seeded machines, their fused ticks, and pure tape runners.
--
-- 'Body' factors a machine into first-input initialisation, visible-channel
-- commit, and post-commit emit. 'MooreT' seals the channel; 'Moore' also
-- fixes observation to 'Const'. 'Step' is the corresponding fused tick and
-- 'Poles' is the memoryless write/read corner.
--
-- The runners consume an input tape and emit only after a commit. They do
-- not synthesise an input-independent birth state. Alternative leg shapes,
-- optic conversions, and cross-lane circuit conversions are demonstrated in
-- @circuits-examples@, in @Example.BodyZoo@.
module Circuit.Machine
  ( Step (..),
    Body (..),
    Cell (..),
    Mealy,
    Moore,
    MooreP,
    MooreT (..),
    Poles (..),
    close,
    unclose,
    polesK,
    pipe,
    iomap,
    MergeNat (..),
    fuse,
    moore,
    before,
    delay,
    scanT,
    scan,
    fold,
    scanProcess,
    foldProcess,
  )
where

import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Poly (Dir, Poly, Pos)
import Circuit.Step (Step (..))
import Circuit.Tensor (Const (..), SemiTensor (..), Symmetric (..), Tensor, Unit, Unital (..), unConst)
import Circuit.Traced (Assoc (..), OuterSwap (..), Strength (..), Trace (..), Unfold (..), (:.) (..))
import Data.Bifunctor (Bifunctor (..))
import Data.These (These (..), these)
import Prelude hiding (id, init, (.))

-- $setup
-- >>> import Circuit.Machine
-- >>> import Circuit.Tensor (Const (..), unConst)
-- >>> import Circuit.Traced (trace)

-- | The fused machine: a given seed leg at the tensor's unit, and one
-- iterating 'Step'. 'Mealy' is the diagonal.
data Cell t t' ch ch' arr i o = Cell
  { seed :: arr (Unit t) ch,
    step :: Step t t' ch ch' arr i o
  }

type Mealy t ch arr i o = Cell t t ch ch arr i o

data Body t t' ch ch' arr i o = Body
  { init :: arr i ch,
    commit :: arr (t ch i) ch',
    emit :: arr ch' (t' ch' o)
  }

-- | The 'Body' corner with the target grammar sealed to 'Const': emit
-- reads the channel to a bare output.
type Moore t ch arr i o = Body t Const ch ch arr i o

-- | A machine hung on a polynomial interface: directions in, positions out.
type MooreP t ch arr (p :: Poly) = Moore t ch arr (Dir p) (Pos p)

-- | The channel existentially hidden — the price of machines as arrows
-- of one 'Category'. Composition merges two different channels into a
-- pair nobody names; build-and-run never needs the seal.
data MooreT t arr i o = forall ch. MooreT (Moore t ch arr i o)

-- | The factored body fused into a single tick — 'init' is not part of
-- the tick, so it is out of scope here. Total and gate-free: 'emit'
-- reads the freshly written channel, so no copy is owed. There is no
-- inverse: an unfuse would have 'emit' regenerate the output from the
-- channel alone, blind to the tick input, short of widening the channel
-- past what 'init' can seed.
fuse :: (Category arr) => Body t t' ch ch' arr i o -> Step t t' ch ch' arr i o
fuse (Body _ k p) = Step (p . k)

-- | The memoryless machine: 'Body' at the @(Const, Const)@ corner,
-- spelt as its own record so the legs stay arr-general — erasing the
-- 'Const' grammar is an @(->)@-only map. 'init' and 'commit' share the
-- type @arr i ch@ but not the job: 'init' fires tick one, 'commit' the
-- rest. With no channel slot in the tick source, nothing carries across
-- a tick.
data Poles ch arr i o = Poles
  { init :: arr i ch,
    commit :: arr i ch,
    emit :: arr ch o
  }

-- | The one-shot close: fire tick one — 'init', then 'emit'.
close :: (Category arr) => Poles ch arr i o -> arr i o
close (Poles j _ o) = j .> o

-- | A plain arrow as 'Poles', trivially middled.
unclose :: (Category arr) => arr i o -> Poles o arr i o
unclose f = Poles f f id

-- | 'Poles' over a Kleisli arrow: the write effect, then the read.
polesK :: (a -> m ()) -> m b -> Poles () (K m) a b
polesK write receive = Poles (K write) (K write) (K $ const receive)

-- | One-shot pipeline: the first pair's 'emit' crosses into the
-- second's tick-one write.
pipe :: (Category arr) => Poles ch1 arr a b -> Poles ch2 arr b c -> Poles ch1 arr a c
pipe (Poles j1 k1 o1) (Poles j2 _ o2) = Poles j1 k1 (o1 .> j2 .> o2)

-- | Precompose both write legs, postcompose the read leg.
iomap :: (Category arr) => arr i' i -> arr o o' -> Poles ch arr i o -> Poles ch arr i' o'
iomap f g (Poles j k o) = Poles (f .> j) (f .> k) (o .> g)

-- payload, and the law is naturality itself —
-- @mergeNat . tensor f f = f . mergeNat@. The machine Category's
-- identity spends it: the commit leg folds (stale channel, fresh
-- input) so the fresh tick wins. Distinct from MergeT — mergeT is
-- per-carrier (Int merges by addition); mergeNat is functor-level.
class (Tensor t arr) => MergeNat t arr where
  mergeNat :: arr (t a a) a

instance MergeNat (,) (->) where
  mergeNat = snd
  {-# INLINE mergeNat #-}

instance MergeNat Either (->) where
  mergeNat = either id id
  {-# INLINE mergeNat #-}

instance MergeNat These (->) where
  mergeNat = these id id (\_ i -> i)
  {-# INLINE mergeNat #-}

instance (MergeNat t (->)) => Category (MooreT t (->)) where
  id = MooreT (Body id mergeNat Const)
  {-# INLINE id #-}

  MooreT (Body j2 k2 e2) . MooreT (Body j1 k1 e1) =
    MooreT (Body j k e)
    where
      j i = let c1 = j1 i in (c1, j2 (unConst (e1 c1)))
      k x = let c1' = k1 (tensor fst id x) in (c1', k2 (tensor snd (const (unConst (e1 c1'))) x))
      e = Const . unConst . e2 . snd
  {-# INLINE (.) #-}

-- | The curried builder for the cartesian sealed machine: init, step,
-- extract.
moore :: (a -> s) -> (s -> a -> s) -> (s -> b) -> MooreT (,) (->) a b
moore i st ex = MooreT (Body i (uncurry st) (Const . ex))

instance Functor (MooreT (,) (->) a) where
  fmap f (MooreT (Body i k o)) = MooreT (Body i k (Const . f . unConst . o))
  {-# INLINEABLE fmap #-}

instance Applicative (MooreT (,) (->) a) where
  pure b = moore (const ()) (\_ _ -> ()) (const b)
  {-# INLINEABLE pure #-}
  MooreT (Body i1 k1 o1) <*> MooreT (Body i2 k2 o2) =
    moore
      (\a -> (i1 a, i2 a))
      (\(s1, s2) a -> (k1 (s1, a), k2 (s2, a)))
      (\(s1, s2) -> unConst (o1 s1) (unConst (o2 s2)))
  {-# INLINEABLE (<*>) #-}

-- These instances make @MooreT (,) (->)@ a traced monoidal category
-- under the cartesian tensor — the trace ties a lazy self-referential
-- knot and is productive only when the body is non-strict in the
-- feedback channel. Strict accumulators diverge: the knot has no seed
-- and demands the channel before the body can produce it.

instance Assoc (,) (MooreT (,) (->)) where
  assoc = moore id (\_ x -> x) (\(~((a, b), c)) -> (a, (b, c)))
  assoc' = moore id (\_ x -> x) (\(a, ~(b, c)) -> ((a, b), c))

instance OuterSwap (,) (MooreT (,) (->)) where
  outerSwap = moore id (\_ x -> x) (\(a, ~(b, c)) -> (b, (a, c)))

instance Strength (,) (MooreT (,) (->)) where
  strength (MooreT (Body i k o)) =
    moore
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', k (s, b)))
      (\(~(a, s)) -> (a, unConst (o s)))

instance Trace (,) (MooreT (,) (->)) where
  trace (MooreT (Body i k o)) =
    moore
      (\b -> let s0 = i (a0, b); a0 = fst (unConst (o s0)) in s0)
      ( \s b ->
          let (s', _a) = fix (\ ~(s'', a') -> (k (s, (a', b)), fst (unConst (o s''))))
           in s'
      )
      (snd . unConst . o)
    where
      fix f = let x = f x in x

instance Unital (,) (MooreT (,) (->)) where
  unitl = moore snd (\_ (_, a) -> a) id
  unitl' = moore id (\_ x -> x) ((),)
  unitr = moore fst (\_ (a, ()) -> a) id
  unitr' = moore id (\_ x -> x) (,())

instance SemiTensor (,) (MooreT (,) (->)) where
  tensor (MooreT (Body i1 k1 o1)) (MooreT (Body i2 k2 o2)) =
    moore
      (bimap i1 i2)
      (\(s1, s2) (a, c) -> (k1 (s1, a), k2 (s2, c)))
      (bimap (unConst . o1) (unConst . o2))
  {-# INLINE tensor #-}

-- | 'Tensor' for 'MooreT' is the conjunction: 'Unital' plus this
-- 'SemiTensor'.
instance Tensor (,) (MooreT (,) (->))

instance Symmetric (,) (MooreT (,) (->)) where
  braid = moore id (const id) sw
    where
      sw (a, b) = (b, a)
  {-# INLINE braid #-}

-- | Precompose the machine with a pure map on the input.
before :: MooreT (,) (->) b c -> (a -> b) -> MooreT (,) (->) a c
before (MooreT (Body i k o)) f =
  MooreT (Body (i . f) (\(s, a) -> k (s, f a)) o)
{-# INLINEABLE before #-}

-- | One tick of delay: the channel holds the previous input.
delay :: s -> MooreT (,) (->) s s
delay s0 = moore (\a -> (s0, a)) (\(_, prev) a -> (prev, a)) fst

-- | Input-list elimination: each step injects the input through the
-- tensor's own left unit — memoryless at Either, That-biased at These.
scanT :: (Tensor t (->)) => MooreT t (->) i o -> [i] -> [o]
scanT (MooreT (Body j k e)) = \case
  [] -> []
  (i : is) -> let c = j i in unConst (e c) : go c is
  where
    go _ [] = []
    go c (i : is) = let c' = k (tensor (const c) id (unitl' i)) in unConst (e c') : go c' is

-- | The visible-channel scan: the body's legs compiled to one generator
-- over the @(Maybe ch, tape)@ channel — the 'Nothing' channel is the
-- seed station, 'init' firing inside the loop — run at the uncons
-- grammar (@Maybe :. (,)@): emit per step, halt omits.
--
-- >>> let sumM = Body id (uncurry (+)) Const :: Moore (,) Int (->) Int Int
-- >>> scanProcess sumM [1,2,3,4]
-- [1,3,6,10]
-- >>> scanProcess sumM []
-- []
scanProcess :: Moore (,) s (->) a b -> [a] -> [b]
scanProcess (Body j k e) as = unfold gen (Nothing, as)
  where
    gen (_, []) = Nest Nothing
    gen (ms, a : rest) =
      let s' = case ms of
            Nothing -> j a
            Just s -> k (s, a)
       in Nest (Just ((Just s', rest), unConst (e s')))

-- | The sealed 'scanProcess': the channel hidden behind 'MooreT'.
--
-- Each output is one post-commit tick: the first tick uses 'init', later
-- ticks use 'commit'.
--
-- >>> let sumM = moore id (\s i -> s + i) id
-- >>> scan sumM [1,2,3]
-- [1,3,6]
--
-- Trace closes the body's post-commit feedback channel on each tick. Here
-- the feedback is the powers-of-two stream, observed three elements at a
-- time:
--
-- >>> let powers = trace (moore (const []) (\_ (a, ()) -> 1 : map (* 2) a) (\s -> (s, take 3 s)))
-- >>> scan powers [(), (), ()]
-- [[],[1,2,4],[1,2,4]]
scan :: MooreT (,) (->) a b -> [a] -> [b]
scan (MooreT m) = scanProcess m

-- | The sealed 'foldProcess': the channel hidden behind 'MooreT'.
fold :: MooreT (,) (->) a b -> [a] -> Maybe b
fold (MooreT m) = foldProcess m

-- | The visible-channel fold: the same @(Maybe ch, tape)@ channel and
-- seed discipline as 'scanProcess', run at the maybe-one grammar
-- (@Maybe :. Either@) — nothing emitted per step, the answer at the
-- tape's end, 'Nothing' on the empty tape.
--
-- >>> let sumM = Body id (uncurry (+)) Const :: Moore (,) Int (->) Int Int
-- >>> foldProcess sumM [1,2,3,4]
-- Just 10
-- >>> foldProcess sumM []
-- Nothing
foldProcess :: Moore (,) s (->) a b -> [a] -> Maybe b
foldProcess (Body j k e) as = unfold gen (Nothing, as)
  where
    gen (Nothing, []) = Nest Nothing
    gen (Just s, []) = Nest (Just (Right (unConst (e s))))
    gen (ms, a : rest) =
      let s' = case ms of
            Nothing -> j a
            Just s -> k (s, a)
       in Nest (Just (Left (Just s', rest)))
