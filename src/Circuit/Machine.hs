{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Traditional Moore and Mealy machines, plus runners for 'InitCell'.
-- 'MooreT' and 'MealyT' seal the channel; their 'Poly' aliases fix the
-- interface by positions and directions. A runner supplies the schedule:
-- 'runInitCell' drives its initial channel on the first input only, while the
-- traditional Moore runners retain their established lifecycle.
module Circuit.Machine
  ( Mealy,
    MealyT (..),
    MealyP,
    Moore (..),
    MooreP,
    MooreT (..),
    MergeNat (..),
    moore,
    before,
    delay,
    runInitCell,
    runM,
    scanT,
    scan,
    fold,
    scanProcess,
    foldProcess,
  )
where

import Circuit.Body (Channel (..), InitCell (..))
import Circuit.Category (Category (..), K (..), (.>))
import Circuit.Poly (Dir, Poly, Pos)
import Circuit.Step (Cell (..), Step (..))
import Circuit.Stream (Cons (..), Uncons (..))
import Circuit.Tensor (Const (..), SemiTensor (..), Symmetric (..), Tensor, Unital (..))
import Circuit.Traced (Assoc (..), OuterSwap (..), Strength (..), Trace (..), Unfold (..), (:.) (..))
import Data.Bifunctor (Bifunctor (..))
import Data.These (These (..), these)
import Prelude hiding (id, init, (.))

-- $setup
-- >>> import Circuit.Machine
-- >>> import Circuit.Traced (trace)

-- | The diagonal 'Cell'.
type Mealy t ch arr i o = Cell t t ch ch arr i o

-- | A Mealy machine with its channel existentially hidden.
data MealyT t arr i o = forall ch. MealyT (Mealy t ch arr i o)

-- | Composition pairs channels and sequences steps; composite seeds are
-- tensors at the unit.
instance forall t arr. (Tensor t arr, Strength t arr) => Category (MealyT t arr) where
  id = MealyT (Cell (unitl' @t) id)
  MealyT (Cell seed2 (Step g)) . MealyT (Cell seed1 (Step f)) =
    MealyT (Cell (unitl' @t .> tensor seed1 seed2) (Step (assoc .> outerSwap .> strength f .> outerSwap .> strength g .> assoc')))

-- | A Mealy machine on a polynomial interface.
type MealyP t ch arr (p :: Poly) = Mealy t ch arr (Dir p) (Pos p)

-- | First-input initialisation, commit, and post-commit observation.
data Moore t ch arr i o = Moore
  { init :: arr i ch,
    commit :: arr (t ch i) ch,
    emit :: arr ch o
  }

-- | A Moore machine on a polynomial interface.
type MooreP t ch arr (p :: Poly) = Moore t ch arr (Dir p) (Pos p)

-- | A Moore machine with its channel existentially hidden.
data MooreT t arr i o = forall ch. MooreT (Moore t ch arr i o)

-- | Fresh-input merging used by sealed Moore composition. The law is
-- naturality: @mergeNat . tensor f f = f . mergeNat@.
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
  id = MooreT (Moore id mergeNat id)
  {-# INLINE id #-}

  MooreT (Moore i2 c2 e2) . MooreT (Moore i1 c1 e1) =
    MooreT (Moore i c e)
    where
      i x = let ch1 = i1 x in (ch1, i2 (e1 ch1))
      c x = let ch1' = c1 (tensor fst id x) in (ch1', c2 (tensor snd (const (e1 ch1')) x))
      e = e2 . snd
  {-# INLINE (.) #-}

-- | The curried builder for the cartesian sealed machine: init, step,
-- extract.
moore :: (a -> s) -> (s -> a -> s) -> (s -> b) -> MooreT (,) (->) a b
moore i st ex = MooreT (Moore i (uncurry st) ex)

instance Functor (MooreT (,) (->) a) where
  fmap f (MooreT (Moore i c e)) = MooreT (Moore i c (f . e))
  {-# INLINEABLE fmap #-}

instance Applicative (MooreT (,) (->) a) where
  pure b = moore (const ()) (\_ _ -> ()) (const b)
  {-# INLINE pure #-}
  MooreT (Moore i1 c1 e1) <*> MooreT (Moore i2 c2 e2) =
    moore
      (\a -> (i1 a, i2 a))
      (\(s1, s2) a -> (c1 (s1, a), c2 (s2, a)))
      (\(s1, s2) -> e1 s1 (e2 s2))
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
  strength (MooreT (Moore i c e)) =
    moore
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', c (s, b)))
      (\(~(a, s)) -> (a, e s))

instance Trace (,) (MooreT (,) (->)) where
  trace (MooreT (Moore i c e)) =
    moore
      (\b -> let s0 = i (a0, b); a0 = fst (e s0) in s0)
      ( \s b ->
          let (s', _a) = fix (\ ~(s'', a') -> (c (s, (a', b)), fst (e s'')))
           in s'
      )
      (snd . e)
    where
      fix f = let x = f x in x

instance Unital (,) (MooreT (,) (->)) where
  unitl = moore snd (\_ (_, a) -> a) id
  unitl' = moore id (\_ x -> x) ((),)
  unitr = moore fst (\_ (a, ()) -> a) id
  unitr' = moore id (\_ x -> x) (,())

instance SemiTensor (,) (MooreT (,) (->)) where
  tensor (MooreT (Moore i1 c1 e1)) (MooreT (Moore i2 c2 e2)) =
    moore
      (bimap i1 i2)
      (\(s1, s2) (a, c) -> (c1 (s1, a), c2 (s2, c)))
      (bimap e1 e2)
  {-# INLINE tensor #-}

instance Tensor (,) (MooreT (,) (->))

instance Symmetric (,) (MooreT (,) (->)) where
  braid = moore id (const id) sw
    where
      sw (a, b) = (b, a)
  {-# INLINE braid #-}

-- | Precompose the machine with a pure map on the input.
before :: MooreT (,) (->) b c -> (a -> b) -> MooreT (,) (->) a c
before (MooreT (Moore i c e)) f =
  MooreT (Moore (i . f) (\(s, a) -> c (s, f a)) e)
{-# INLINEABLE before #-}

-- | One tick of delay: the channel holds the previous input.
delay :: s -> MooreT (,) (->) s s
delay s0 = moore (\a -> (s0, a)) (\(_, prev) a -> (prev, a)) fst

-- | Run an initial channel exactly once on the first input, then run the
-- recurrent body on every later input. The first observation uses the initial
-- channel's emit leg; later observations use the body's emit leg. The initial
-- post-input channel is the body's pre-input channel by type equality. Empty
-- input drives neither channel. Every output retains its emit leg's channel
-- package, and the runner carries only the commit-produced channel forward.
runInitCell :: forall t t' ch m i o. (Monad m, Tensor t (K m)) => InitCell t t' ch (K m) i o -> [i] -> m [t' ch o]
runInitCell (InitCell (Channel initialCommit initialEmit) (Channel recurCommit recurEmit)) = \case
  [] -> pure []
  input : rest -> do
    channel <- runK initialCommit (Const input)
    emitted <- runK initialEmit channel
    (emitted :) <$> go channel rest
  where
    go _ [] = pure []
    go channel (input : rest) = do
      channel' <- runK (unitl' .> tensor (K (const (pure channel))) id .> recurCommit) input
      emitted <- runK recurEmit channel'
      (emitted :) <$> go channel' rest

-- | Stream elimination: the first input uses 'init', later inputs use
-- 'commit', and every observation follows that transition. Each commit
-- injects the input through the tensor's own left unit.
--
-- >>> let sumM = Moore id (uncurry (+)) id :: Moore (,) Int (->) Int Int
-- >>> runM sumM ([1,2,3,4] :: [Int]) :: [Int]
-- [1,3,6,10]
-- >>> runM sumM ([] :: [Int]) :: [Int]
-- []
runM :: forall t is i os o ch. (Tensor t (->), Uncons is i, Cons os o) => Moore t ch (->) i o -> is -> os
runM (Moore i c e) = go Nothing
  where
    go previous is = case uncons is of
      That _ -> consNil @os @o
      This input -> tick previous input (nil @is @i)
      These input rest -> tick previous input rest
    tick previous input rest =
      let channel = advance previous input
       in cons (e channel) (go (Just channel) rest)
    advance previous input = case previous of
      Nothing -> i input
      Just channel -> c (tensor (const channel) id (unitl' input))

-- | Input-list elimination at any tensor.
scanT :: (Tensor t (->)) => MooreT t (->) i o -> [i] -> [o]
scanT (MooreT m) = runM m

-- | The visible-channel scan at @(,)@.
scanProcess :: Moore (,) s (->) a b -> [a] -> [b]
scanProcess = runM

-- | The sealed 'scanProcess'.
--
-- >>> let sumM = moore id (\s i -> s + i) id
-- >>> scan sumM [1,2,3]
-- [1,3,6]
--
-- Trace closes the body's post-commit feedback channel on each tick:
--
-- >>> let powers = trace (moore (const []) (\_ (a, ()) -> 1 : map (* 2) a) (\s -> (s, take 3 s)))
-- >>> scan powers [(), (), ()]
-- [[],[1,2,4],[1,2,4]]
scan :: MooreT (,) (->) a b -> [a] -> [b]
scan (MooreT m) = scanProcess m

-- | The sealed 'foldProcess'.
fold :: MooreT (,) (->) a b -> [a] -> Maybe b
fold (MooreT m) = foldProcess m

-- | The visible-channel fold: no output per step, only the answer at the
-- tape's end. The empty tape produces 'Nothing'.
--
-- >>> let sumM = Moore id (uncurry (+)) id :: Moore (,) Int (->) Int Int
-- >>> foldProcess sumM [1,2,3,4]
-- Just 10
-- >>> foldProcess sumM []
-- Nothing
foldProcess :: Moore (,) s (->) a b -> [a] -> Maybe b
foldProcess (Moore i c e) as = unfold gen (Nothing, as)
  where
    gen (Nothing, []) = Nest Nothing
    gen (Just s, []) = Nest (Just (Right (e s)))
    gen (ms, a : rest) =
      let s' = case ms of
            Nothing -> i a
            Just s -> c (s, a)
       in Nest (Just (Left (Just s', rest)))
