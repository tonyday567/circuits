{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The machine layer: machines over a channel, and the runners that
-- drive them.
--
-- The tick itself — 'Step', re-exported here — lives in
-- "Circuit.Step": one arrow from the grammared source @t ch i@ to the
-- grammared target @t' ch' o@, the shared currency of this lane and the
-- traced lane. A machine pairs an initial step with the iterating tick,
-- in two spellings. 'Cell' keeps the tick fused and seeds the channel
-- from the tensor's unit. 'Body' factors the tick through the channel —
-- 'commit' writes it, 'emit' reads the freshly written value — and
-- seeds from the first input. 'Moore' is 'Body' with the target grammar
-- sealed to 'Const'; 'MooreT' hides the channel existentially and
-- carries the machine 'Category'. 'Poles' is the memoryless corner,
-- where the channel never carries across a tick. The bundles — 'FoldBody',
-- 'TheseBody', 'EitherBody', 'LensBody', 'OpticBody', 'ProfunctorBody' — are the partial decompositions:
-- each names a live-leg pattern, and each fuse lands it back in a
-- 'Step'. Coiteration — 'Unfold', 'Nu', the partial grammars — lives in
-- "Circuit.Traced", beside 'trace'.
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
    pipe,
    iomap,

    -- * the bundles
    FoldBody (..),
    TheseBody (..),
    EitherBody (..),
    LensBody (..),
    OpticBody (..),
    ProfunctorBody (..),
    fuseFoldBody,
    fuseTheseBody,
    fuseEitherBody,
    fuseLensBody,
    fuseOpticBody,
    fuseProfunctorBody,
    unfuseEitherBody,
    unfuseTheseBody,

    -- * the natural merge
    MergeNat (..),

    -- * builders
    moore,
    before,
    delay,
    feedback,
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
    lensBodyAsLens,
    lensAsLensBody,
    lensBodyToOptic,
    opticToLensBody,
    lensAsOptic,
    opticAsLens,
    closedToGenerator,
    mealyToKnot,
    mooreToKnot,
    traceToMoore,
  )
where

import Circuit.Bimonoid (Copy (..))
import Circuit.Category (BiK (..), Category (..), K (..), (.>))
import Circuit.Poly (Dir, Lens, Poly, Pos, applyLens, lens)
import Circuit.Step (Step (..))
import Circuit.Syntax (evalInto)
import Circuit.Tensor (Cocartesian (..), Const (..), ConstInject (..), SemiTensor (..), Symmetric (..), Tensor, TheseElim (..), Unit, Unital (..), innerSwap, unConst)
import Circuit.Trace (FreeTrace, Knot (..))
import Circuit.Traced (Assoc (..), OuterSwap (..), Strength (..), Trace (..), Unfold (..), (:.) (..))
import Data.Bifunctor (Bifunctor (..))
import Data.These (These (..), these)
import Prelude hiding (id, init, (.))

-- $setup
-- >>> import Circuit.Machine
-- >>> import Circuit.Poly (applyLens)
-- >>> import Circuit.Tensor (Const (..), unConst)
-- >>> import Circuit.Trace (Knot (..), FreeTrace)
-- >>> import qualified Circuit.Syntax as S
-- >>> import Data.These (These (..), these)

-- | The fused machine: a given seed leg at the tensor's unit, and one
-- iterating 'Step'. 'Mealy' is the diagonal; 'MealyT' seals the
-- channel existentially.
data Cell t t' ch ch' arr i o = Cell
  { seed :: arr (Unit t) ch,
    step :: Step t t' ch ch' arr i o
  }

type Mealy t ch arr i o = Cell t t ch ch arr i o

data MealyT t arr i o = forall ch. MealyT (Mealy t ch arr i o)

-- | 'MealyT' is a category under the same structural conditions as
-- 'Circuit.Trace.Knot': composition pairs channels and sequences steps.
-- The seed of a composite is the tensor of the two seeds at the unit.
instance forall t arr. (Tensor t arr, Strength t arr) => Category (MealyT t arr) where
  id = MealyT (Cell (unitl' @t) id)
  MealyT (Cell seed2 (Step g)) . MealyT (Cell seed1 (Step f)) =
    MealyT (Cell (unitl' @t .> tensor seed1 seed2) (Step (assoc .> outerSwap .> strength f .> outerSwap .> strength g .> assoc')))

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
-- reads the freshly written channel, so no copy is owed. There is no
-- inverse: an unfuse would have 'emit' regenerate the output from the
-- channel alone, blind to the tick input, short of widening the channel
-- past what 'init' can seed. The universal splits are the source-side
-- ones ('unfuseEitherBody', 'unfuseTheseBody').
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

-- * the bundles

-- | The strict-fold bundle: a seed at the tensor's unit, a commit leg
-- writing the channel, and a bare extract. 'fuseFoldBody' is the tick;
-- 'begin' is not part of it.
data FoldBody t ch arr i o = FoldBody
  { begin :: arr (Unit t) ch,
    step :: arr (t ch i) ch,
    extract :: arr ch o
  }

-- | The 'These' source-split: one leg per presence pattern. Total, and
-- an isomorphism at the 'These' source — every arrow out of
-- @These ch i@ is uniquely a triple — so 'unfuseTheseBody' inverts
-- 'fuseTheseBody' on the nose.
data TheseBody t' ch ch' arr i o = TheseBody
  { chLeg :: arr ch (t' ch' o),
    iLeg :: arr i (t' ch' o),
    bothLeg :: arr (ch, i) (t' ch' o)
  }

-- | The 'Either' source-split with an explicit collapse. 'collapse' is
-- the identity at @t ~ Either@ — the machine it names; at other tensors
-- it must pick a side and is lossy.
data EitherBody t t' ch ch' arr i o = EitherBody
  { chLeg :: arr ch (t' ch' o),
    iLeg :: arr i (t' ch' o),
    collapse :: arr (t ch i) (Either ch i)
  }

-- | The parallel-legs tick (the lens body): 'set' is the commit corner,
-- 'view' the emit corner reading the tick-start channel — pre-set,
-- where 'Body's emit reads the channel post-commit. The getter/putter
-- split pays a copy of the channel; the 'OpticBody' split pays none in
-- the fuse — a copy is owed only inside a 'focus' whose output and
-- residual share part of the channel.
data LensBody t ch ch' arr i o = LensBody
  { set :: arr (t ch i) ch',
    view :: arr ch o
  }

-- | The residual decomposition of a tick: 'focus' splits the tick-start
-- channel into a residual and the output; 'rebuild' consumes the residual
-- and the tick input into the new channel. The residual is existential —
-- the coend of the optic representation — so bodies that differ by sliding
-- an arrow across the residual are the same tick. Residual-first, so the
-- fuse is one 'innerSwap' at any symmetric tensor: lenses at @(,)@,
-- prisms at 'Either', and a 'These' corner. The fuse owes no copy; any
-- copy is owed inside 'focus', when the residual and the output share
-- part of the channel.
data OpticBody t ch ch' arr i o
  = forall r. OpticBody (arr ch (t r o)) (arr (t r i) ch')

-- | The profunctor-shaped bundle: a pre-compose leg, the nuclear hom
-- 'pmap' — the catalogue's only grammar-free, interface-free leg — and
-- a post-compose leg. The non-uniqueness (outerSwap an automorphism across
-- the pmap|post boundary) is the coend of the profunctor
-- representation theorem; the residual pair @(ch, ch')@ is what a
-- forall would seal.
data ProfunctorBody t ch ch' arr i o = ProfunctorBody
  { pre :: arr (t ch i) ch,
    pmap :: arr ch ch',
    post :: arr ch' o
  }

-- | Fuse a 'FoldBody' into one tick: commit and extract pair at the @(,)@
-- target. Requires 'Copy' on the channel and the cartesian tensor to
-- duplicate the new channel for the extract leg.
--
-- >>> let sb = FoldBody (const 0) (\(c, i) -> c + i) (* 2) :: FoldBody (,) Int (->) Int Int
-- >>> case fuseFoldBody sb of Step f -> f (3, 4 :: Int)
-- (7,14)
fuseFoldBody :: (Tensor (,) arr, Copy arr ch) => FoldBody t ch arr i o -> Step t (,) ch ch arr i o
fuseFoldBody (FoldBody _ k e) = Step (k .> copy .> tensor id e)

-- | Fuse a 'TheseBody' into one tick: the three legs are the 'These'
-- eliminator. Requires 'TheseElim' on the base arrow.
--
-- >>> let tb = TheseBody Left Right (\(c, i) -> Right (c + i)) :: TheseBody Either Int Int (->) Int Int
-- >>> let Step f = fuseTheseBody tb
-- >>> [f (This 5), f (That 5), f (These 3 4)]
-- [Left 5,Right 5,Right 7]
fuseTheseBody :: (TheseElim arr) => TheseBody t' ch ch' arr i o -> Step These t' ch ch' arr i o
fuseTheseBody (TheseBody ch i b) = Step (theseElim ch i b)

-- | Fuse an 'EitherBody' into one tick: 'collapse' to 'Either', then the
-- legs. Requires 'Cocartesian Either' on the base arrow.
--
-- >>> let sb = EitherBody (Left . (* 10)) (Right . (+ 1)) id :: EitherBody Either Either Int Int (->) Int Int
-- >>> let Step f = fuseEitherBody sb
-- >>> [f (Left 5), f (Right 5)]
-- [Left 50,Right 6]
fuseEitherBody :: (Cocartesian Either arr) => EitherBody Either t' ch ch' arr i o -> Step Either t' ch ch' arr i o
fuseEitherBody (EitherBody ch i c) = Step (c .> elim ch i)

-- | Fuse an 'LensBody' into one tick: the parallel legs land at the @(,)@
-- target — 'set' writes the channel while 'view' reads the tick-start
-- channel, pre-set. Routes through the residual decomposition —
-- 'lensBodyToOptic', then 'fuseOpticBody' — so the copy owed is of the
-- channel alone.
--
-- >>> let lb = LensBody (\(c, i) -> c + i) (* 2) :: LensBody (,) Int Int (->) Int Int
-- >>> case fuseLensBody lb of Step f -> f (3, 4 :: Int)
-- (7,6)
fuseLensBody :: (Symmetric (,) arr, OuterSwap (,) arr, Copy arr ch) => LensBody (,) ch ch' arr i o -> Step (,) (,) ch ch' arr i o
fuseLensBody = fuseOpticBody . lensBodyToOptic

-- | Fuse an 'OpticBody' into one tick at any symmetric tensor: focus,
-- swap the output past the input, rebuild.
--
-- >>> let ob = OpticBody (\c -> (c, c * 2)) (\(c, i) -> c + i) :: OpticBody (,) Int Int (->) Int Int
-- >>> case fuseOpticBody ob of Step f -> f (3, 4 :: Int)
-- (7,6)
-- >>> let pr = OpticBody (\c -> if c > 0 then Right (c * 10) else Left c) (either id negate) :: OpticBody Either Int Int (->) Int Int
-- >>> case fuseOpticBody pr of Step f -> [f (Left 3), f (Left (-2)), f (Right 5)]
-- [Right 30,Left (-2),Left (-5)]
fuseOpticBody :: (Symmetric t arr, OuterSwap t arr) => OpticBody t ch ch' arr i o -> Step t t ch ch' arr i o
fuseOpticBody (OpticBody f b) = Step (tensor f id .> innerSwap .> tensor b id)

-- | Fuse a 'ProfunctorBody' into one tick at the 'Const' target: pre, pmap,
-- post, then the 'Const' injection. Requires 'ConstInject' on the base
-- arrow.
--
-- >>> let pb = ProfunctorBody (\(c, i) -> c + i) (* 10) (+ 1) :: ProfunctorBody (,) Int Int (->) Int Int
-- >>> case fuseProfunctorBody pb of Step f -> unConst (f (3, 4 :: Int))
-- 71
fuseProfunctorBody :: (ConstInject arr) => ProfunctorBody t ch ch' arr i o -> Step t Const ch ch' arr i o
fuseProfunctorBody (ProfunctorBody a n o) = Step (a .> n .> o .> constIn)

-- | The 'Either' source-split is universal: every arrow out of
-- @Either ch i@ is uniquely its pair of legs, so a tick at the
-- 'Either' source is exactly an 'EitherBody' with 'collapse' the identity.
-- Inverse to 'fuseEitherBody' — the round trip is witnessed exhaustively in
-- "Axioma.Machine".
--
-- >>> let g = either (Left . (* 2)) (Right . (+ 1)) :: Either Int Int -> Either Int Int
-- >>> let Step h = fuseEitherBody (unfuseEitherBody (Step g))
-- >>> [h (Left 3), h (Right 3)] == [g (Left 3), g (Right 3)]
-- True
unfuseEitherBody :: Step Either t' ch ch' (->) i o -> EitherBody Either t' ch ch' (->) i o
unfuseEitherBody (Step f) = EitherBody (f . Left) (f . Right) id

-- | The 'These' source-split is universal: a tick at the 'These'
-- source is exactly a 'TheseBody'. Inverse to 'fuseTheseBody' — the round trip
-- is witnessed exhaustively in "Axioma.Machine".
--
-- >>> let g = these Left Right (\c i -> Right (c + i)) :: These Int Int -> Either Int Int
-- >>> let Step h = fuseTheseBody (unfuseTheseBody (Step g))
-- >>> [h (This 3), h (That 3), h (These 3 4)] == [g (This 3), g (That 3), g (These 3 4)]
-- True
unfuseTheseBody :: Step These t' ch ch' (->) i o -> TheseBody t' ch ch' (->) i o
unfuseTheseBody (Step f) = TheseBody (f . This) (f . That) (f . uncurry These)

-- | The natural merge of the tensor's diagonal: one arrow for every
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
-- feedback channel. Strict accumulators diverge under the @(,)@ trace;
-- use 'feedback' for those.

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

-- | Feed a strict machine its own previous output as a second channel —
-- the strict-body alternative to the lazy 'trace' knot.
feedback :: s -> MooreT (,) (->) (a, s) (b, s) -> MooreT (,) (->) a b
feedback s0 (MooreT (Body i k o)) =
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

-- | The parallel-legs body as a lens. 'view' is the getter (it reads the
-- tick-start channel); 'set' is the putter (it consumes the old channel
-- and the input to produce the new channel). At the diagonal @ch' ~ ch@
-- this is the ordinary lens on the channel; off-diagonal it is a lens
-- whose source position is @ch@ and source direction is @ch'@.
--
-- >>> let lb = LensBody (\(c, i) -> c + i) (* 2) :: LensBody (,) Int Int (->) Int Int
-- >>> let (v, put) = applyLens (lensBodyAsLens lb) 3 in (v, put 4)
-- (6,7)
lensBodyAsLens :: LensBody (,) ch ch' (->) i o -> Lens ch ch' o i
lensBodyAsLens (LensBody s v) = lens v (curry s)

-- | A lens as a parallel-legs body: the lens supplies the pre-set view
-- and the commit leg; the target grammar is @(,)@ because the body
-- exposes both the new channel and the output.
lensAsLensBody :: Lens ch ch' o i -> LensBody (,) ch ch' (->) i o
lensAsLensBody m = LensBody (\(s, i) -> snd (applyLens m s) i) (fst . applyLens m)

-- | Getter/putter into residual form: the residual is the whole channel,
-- and the copy is of the channel alone.
lensBodyToOptic :: (Tensor (,) arr, Copy arr ch) => LensBody (,) ch ch' arr i o -> OpticBody (,) ch ch' arr i o
lensBodyToOptic (LensBody s v) = OpticBody (copy .> tensor id v) s

-- | Residual form back to getter/putter: runs 'focus' on both legs.
-- At @(->)@ only; arr-general would need 'Discard' on @o@ and on the
-- residual.
opticToLensBody :: OpticBody (,) ch ch' (->) i o -> LensBody (,) ch ch' (->) i o
opticToLensBody (OpticBody f b) = LensBody (\(c, i) -> b (fst (f c), i)) (snd . f)

-- | The canonical residual: @r ~ i -> ch'@ — the paper's forward
-- direction, the hom from the tick input to the new channel.
lensAsOptic :: Lens ch ch' o i -> OpticBody (,) ch ch' (->) i o
lensAsOptic m = OpticBody (\c -> let (o, k) = applyLens m c in (k, o)) (\(k, i) -> k i)

-- | Residual form back to a 'Lens': the getter is the output half of
-- 'focus', the putter feeds the residual half and the tick input to
-- 'rebuild'. This runs 'focus' twice — once for the getter, once per
-- put; a store-form constructor in "Circuit.Poly" would call it once.
opticAsLens :: OpticBody (,) ch ch' (->) i o -> Lens ch ch' o i
opticAsLens (OpticBody f b) = lens (snd . f) (\c i -> b (fst (f c), i))

-- | The closed branch as a generator coalgebra: input closed at the
-- tensor's unit, the tick's two legs chained into one arrow on the
-- channel. The body's 'init' is the seed of a run, not of the coalgebra
-- — 'unfold' supplies that — so it is out of scope here.
closedToGenerator :: (Tensor t arr) => Body t t ch ch arr (Unit t) b -> arr ch (t ch b)
closedToGenerator (Body _ k p) = unitr' .> k .> p

-- * Machine / FreeTrace bridges

-- | A sealed Mealy machine is a 'Knot' plus a seed leg. Dropping the seed
-- gives the knot body; the channel type is the machine's hidden channel.
--
-- >>> let win = Cell (const []) (Step (\(ns, i) -> (i : ns, take 3 (i : ns))))
-- >>> S.run (mealyToKnot (MealyT win :: MealyT (,) (->) Int [Int])) 7
-- [7,7,7]
mealyToKnot :: MealyT t arr i o -> Knot t arr i o
mealyToKnot (MealyT (Cell _ (Step f))) = Knot f

-- | A cartesian Moore machine factors into a Mealy-style step by exposing
-- the freshly written channel alongside the output. The initial 'init'
-- leg is not part of the static knot; it belongs to the runner.
--
-- >>> let double = MooreT (Body (const 0) (\(_, i) -> i) (Const . (* 2)))
-- >>> S.run (mooreToKnot double) 5
-- 10
mooreToKnot :: MooreT (,) (->) i o -> Knot (,) (->) i o
mooreToKnot (MooreT (Body _ k o)) = Knot (\(s, i) -> (k (s, i), unConst (o (k (s, i)))))

-- | Fold free traced syntax into 'MooreT (,) (->)': a base arrow becomes
-- a Moore machine whose state is the input, overwritten each tick;
-- composition and trace use the existing 'MooreT' traced-category
-- structure.
--
-- >>> scan (traceToMoore (S.Lift (+ 1) :: FreeTrace (,) (->) Int Int)) [1, 2, 3]
-- [2,3,4]
traceToMoore :: FreeTrace (,) (->) a b -> MooreT (,) (->) a b
traceToMoore = evalInto (\f -> MooreT (Body id snd (\s -> Const (f s))))
