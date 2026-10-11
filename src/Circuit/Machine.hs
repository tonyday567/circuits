{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | The machine layer: the tick, the machines built on it, and the
-- runners that drive them.
--
-- A 'Step' is one tick: an arrow from the grammared source @t ch i@ to
-- the grammared target @t' ch' o@. A machine pairs an initial step with
-- the iterating tick, in two spellings. 'Cell' keeps the tick fused and
-- seeds the channel from the tensor's unit. 'Body' factors the tick
-- through the channel — 'commit' writes it, 'emit' reads the freshly
-- written value — and seeds from the first input. 'Moore' is 'Body'
-- with the target grammar sealed to 'Const'; 'MooreT' hides the channel
-- existentially and carries the machine 'Category'. 'Poles' is the
-- memoryless corner, where the channel never carries across a tick.
module Circuit.Machine
  ( -- * the tick
    Step (..),
    fuse,

    -- * machines
    Cell (..),
    Mealy,
    MealyT (..),
    Body (..),
    Moore,
    MooreT (..),
    MealyP,
    MooreP,

    -- * the memoryless corner
    Poles (..),
    close,
    unclose,
    polesK,
    compose,
    iomap,

    -- * the natural merge
    MergeNat (..),

    -- * builders
    moore,
    before,
    delay,
    register,
    processOf,

    -- * runners
    scanT,
    scan,
    fold,
    scanProcess,
    foldProcess,

    -- * bridges
    bodyBiK,
    bodyAsLens,
    lensAsBody,
    closedToGenerator,

    -- * coiteration
    Unfold (..),
  )
where

import Circuit.Category (BiK (..), Category (..), K (..), (.>))
import Circuit.Poly (Dir, Lens, Poly, Pos, applyLens, lens)
import Circuit.Tensor (Action (..), Const (..), SemiTensor (..), Tensor, Unit, Unital (..), unConst)
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..), (<|))
import Data.These (These (..), these)
import Prelude hiding (id, init, (.))

-- | One tick of a machine: the arrow from the grammared source
-- @t ch i@ to the grammared target @t' ch' o@. Composition needs the
-- diagonal — the channel and grammar the tick writes must be the ones
-- the next tick reads.
newtype Step t t' ch ch' arr i o = Step {run :: arr (t ch i) (t' ch' o)}

instance (Category arr) => Category (Step t t ch ch arr) where
  id :: forall a. Step t t ch ch arr a a
  id = Step id
  {-# INLINE id #-}

  (.) :: forall a b c. Step t t ch ch arr b c -> Step t t ch ch arr a b -> Step t t ch ch arr a c
  Step g . Step f = Step (g . f)
  {-# INLINE (.) #-}

-- | The fused machine: a given seed leg at the tensor's unit, and one
-- iterating 'Step'. 'Mealy' is the diagonal; 'MealyT' seals the
-- channel existentially.
data Cell t t' ch ch' arr i o = Cell
  { seed :: arr (Unit t) ch,
    step :: Step t t' ch ch' arr i o
  }

type Mealy t ch arr i o = Cell t t ch ch arr i o

data MealyT t arr i o = forall ch. MealyT (Mealy t ch arr i o)

-- | The factored machine: 'init' seeds the channel from the first
-- input, 'commit' writes the channel from the grammared tick, and
-- 'emit' reads the freshly written channel into the target grammar.
-- Because 'emit' reads @ch'@ post-commit, the output carries no direct
-- entanglement with this tick's input — the Moore discipline.
data Body t t' ch ch' arr i o = Body
  { init :: arr i ch,
    commit :: arr (t ch i) ch',
    emit :: arr ch' (t' ch' o)
  }

-- | The 'Body' corner with the target grammar sealed to 'Const': emit
-- reads the channel to a bare output.
type Moore t ch arr i o = Body t Const ch ch arr i o

-- | The channel existentially hidden — the price of machines as arrows
-- of one 'Category'. Composition merges two different channels into a
-- pair nobody names; build-and-run never needs the seal.
data MooreT t arr i o = forall ch. MooreT (Moore t ch arr i o)

-- | A machine whose interface is a polynomial: directions in,
-- positions out.
type MooreP t ch arr (p :: Poly) = Moore t ch arr (Dir p) (Pos p)

-- | The fused counterpart of 'MooreP'.
type MealyP t ch arr (p :: Poly) = Mealy t ch arr (Dir p) (Pos p)

-- | The factored body fused into a single tick — 'init' is not part of
-- the tick, so it is out of scope here. Total and gate-free: 'emit'
-- reads the freshly written channel, so no copy is owed.
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

-- | One-shot composition: the first pair's 'emit' crosses into the
-- second's tick-one write.
compose :: (Category arr) => Poles ch1 arr a b -> Poles ch2 arr b c -> Poles ch1 arr a c
compose (Poles j1 k1 o1) (Poles j2 _ o2) = Poles j1 k1 (o1 .> j2 .> o2)

-- | Precompose both write legs, postcompose the read leg.
iomap :: (Category arr) => arr i' i -> arr o o' -> Poles ch arr i o -> Poles ch arr i' o'
iomap f g (Poles j k o) = Poles (f .> j) (f .> k) (o .> g)

-- | The natural merge of the tensor's diagonal: one arrow for every
-- payload, and the law is naturality itself —
-- @mergeNat . tensor f f = f . mergeNat@. The machine Category's
-- identity spends it: the commit leg folds (stale channel, fresh
-- input) so the fresh tick wins. Distinct from MergeT — plusT is
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
-- under the cartesian tensor — the yank ties a lazy self-referential
-- knot and is productive only when the body is non-strict in the
-- feedback channel. Strict accumulators diverge under the @(,)@ yank;
-- use 'register' for those.

instance Assoc (,) (MooreT (,) (->)) where
  assoc = moore id (\_ x -> x) (\(~((a, b), c)) -> (a, (b, c)))
  assoc' = moore id (\_ x -> x) (\(a, ~(b, c)) -> ((a, b), c))

instance Slide (,) (MooreT (,) (->)) where
  slide = moore id (\_ x -> x) (\(a, ~(b, c)) -> (b, (a, c)))

instance Strength (,) (MooreT (,) (->)) where
  strength (MooreT (Body i k o)) =
    moore
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', k (s, b)))
      (\(~(a, s)) -> (a, unConst (o s)))

instance Yank (,) (MooreT (,) (->)) where
  yank (MooreT (Body i k o)) =
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

instance Action (,) (MooreT (,) (->)) where
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

-- | Feed a strict machine its own previous output as a second channel —
-- the strict-body alternative to the lazy 'yank' knot.
register :: s -> MooreT (,) (->) (a, s) (b, s) -> MooreT (,) (->) a b
register s0 (MooreT (Body i k o)) =
  moore (\a -> i (a, s0)) (\s a -> k (s, (a, snd (unConst (o s))))) (fst . unConst . o)

-- | Replace a machine's seed leg: the new 'init' injects the input
-- through the given arrow into 'commit'. The body's own init is
-- discarded.
processOf :: (Category arr) => arr a (t s a) -> Moore t s arr a b -> Moore t s arr a b
processOf e (Body _ k o) = Body (e .> k) k o

-- | Input-list elimination: each step injects the input through the
-- tensor's own left unit — memoryless at Either, That-biased at These.
scanT :: (Tensor t (->)) => MooreT t (->) i o -> [i] -> [o]
scanT (MooreT (Body j k e)) = \case
  [] -> []
  (i : is) -> let c = j i in unConst (e c) : go c is
  where
    go _ [] = []
    go c (i : is) = let c' = k (tensor (const c) id (unitl' i)) in unConst (e c') : go c' is

-- | The visible-channel scan: run a 'Moore' body down an input list,
-- emitting after each commit.
scanProcess :: Moore (,) s (->) a b -> [a] -> [b]
scanProcess (Body c k o) = \case
  [] -> []
  (a : as) -> let s0 = c a in unConst (o s0) : go s0 as
  where
    go s (a : as) = let s' = k (s, a) in unConst (o s') : go s' as
    go _ [] = []

scan :: MooreT (,) (->) a b -> [a] -> [b]
scan (MooreT m) = scanProcess m

fold :: MooreT (,) (->) a b -> [a] -> Maybe b
fold (MooreT m) = foldProcess m

-- | The visible-channel fold: run a 'Moore' body down an input list,
-- answering only the final emit.
foldProcess :: Moore (,) s (->) a b -> [a] -> Maybe b
foldProcess (Body c k o) = \case
  [] -> Nothing
  (a : as) -> Just (go (c a) as)
  where
    go s (a : as) = go (k (s, a)) as
    go s [] = unConst (o s)

-- | The 'BiK' bridge: a body's commit/emit legs as one BiK arrow. The
-- seed leg is not part of the arrow.
bodyBiK :: Body (,) t' s s (->) i o -> BiK ((,) s) (t' s) i o
bodyBiK (Body _ k p) = BiK (p . k)

-- | The lens bridge: a body's commit/emit legs as a lens — 'init' is
-- out of scope; a lens has no seed station. Diagonal: the view leg
-- reads the tick-start channel, the commit leg writes it, and only at
-- @ch' ~ ch@ do the two share a carrier.
bodyAsLens :: Body (,) Const ch ch (->) i o -> Lens ch ch o i
bodyAsLens (Body _ k e) = lens (unConst . e) (curry k)

-- | A lens plus a seeding is a body: the lens supplies the commit/emit
-- legs, the caller supplies 'init'.
lensAsBody :: (i -> ch) -> Lens ch ch o i -> Body (,) Const ch ch (->) i o
lensAsBody j m = Body j (\(s, i) -> snd (applyLens m s) i) (Const . fst . applyLens m)

-- | The closed branch as a generator coalgebra: input closed at the
-- tensor's unit, the tick's two legs chained into one arrow on the
-- channel. The body's 'init' is the seed of a run, not of the coalgebra
-- — 'unfold' supplies that — so it is out of scope here.
closedToGenerator :: (Tensor t arr) => Body t t ch ch arr (Unit t) b -> arr ch (t ch b)
closedToGenerator (Body _ k p) = unitr' .> k .> p

class
  (Category arr) =>
  Unfold (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type)
  where
  type Nu t arr b

  unfold :: arr ch (t ch b) -> arr ch (Nu t arr b)

instance Unfold (,) (->) where
  type Nu (,) (->) b = [b]
  unfold g = go
    where
      go ch = case g ch of (ch', b) -> b : go ch'

instance Unfold Either (->) where
  type Nu Either (->) b = b
  unfold g = yank (either g g)

instance Unfold These (->) where
  type Nu These (->) b = NonEmpty b
  unfold g = go
    where
      go ch = case g ch of
        This ch' -> go ch'
        That b -> b :| []
        These ch' b -> b <| go ch'
