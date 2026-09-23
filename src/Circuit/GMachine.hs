{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Circuit.GMachine
  ( Cell (..),
    Body (..),
    MonoBody,
    monoIn,
    monoDir,
    fuse,
    unfuse,
    Machine (..),
    monoMachine,
    Poles (..),
    Point (..),
    Cap (..),
    capT,
    close,
    unclose,
    copycat,
    peek,
    poke,
    polesOf,
    cellOf,
    Process (..),
    processOf,
    processFromSeed,
    Moore,
    pattern Moore,
    asMoore,
    before,
    after,
    delay,
    register,
    scanProcess,
    scan,
    fold,
    foldProcess,
    scanThese,
    Cocell,
    cocell,
    pair,
    closedToGenerator,
    Unfold (..),
    cellAsLens,
    lensAsCell,
    cellAsEval,
    evalAsCell,
  )
where

import Circuit.Bimonoid (CopyT (..), Discard (..), DiscardT (..))
import Circuit.Category (Category (..), Op (..), (.>))
import Circuit.Poly (Dir, Eval (..), Lens, Mono, Poly, Pos, applyLens, lens, monoDir, monoIn)
import Circuit.Tensor (Action (..), Tensor (..), Unit, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..), toList, (<|))
import Data.These (These (..))
import Data.Void (Void)
import Prelude hiding (id, (.))

data Cell (t :: Type -> Type -> Type) ch (arr :: Type -> Type -> Type) i o = Cell
  { consume :: arr (t ch i) ch,
    produce :: arr ch o
  }

newtype Body t ch arr a b = Body {morphism :: arr (t ch a) (t ch b)}

instance (Category arr) => Category (Body t ch arr) where
  id :: forall a. Body t ch arr a a
  id = Body id
  {-# INLINE id #-}

  (.) :: forall a b c. Body t ch arr b c -> Body t ch arr a b -> Body t ch arr a c
  Body g . Body f = Body (g . f)
  {-# INLINE (.) #-}

fuse ::
  forall t s arr a b.
  (CopyT t arr (t s a), DiscardT t arr a) =>
  Cell t s arr a b ->
  Body t s arr a b
fuse (Cell k o) =
  Body (tensor k (o . unitr . tensor id (discardT @t)) . copyT)

unfuse ::
  forall s arr a b.
  (Tensor (,) arr, Discard arr s, Discard arr b) =>
  Body (,) s arr a b ->
  Cell (,) (s, b) arr a b
unfuse (Body f) = Cell (tensor projFst id .> f) projSnd
  where
    projFst :: arr (s, b) s
    projFst = unitr . tensor id discard
    projSnd :: arr (s, b) b
    projSnd = unitl . tensor discard id

type MonoBody t s arr i o = Body t s arr (Either Void i) (o, ())

newtype Machine (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) (p :: Poly) = Machine
  {machineCell :: Cell t s arr (Dir p) (Pos p)}

monoMachine ::
  (Tensor t arr, Unital (,) arr, Unital Either arr) =>
  Cell t s arr i o ->
  Machine t s arr (Mono i o)
monoMachine (Cell k o) =
  Machine (Cell (tensor id unitl .> k) (o .> unitr'))

data Poles ch arr a b = Poles
  { commit :: arr a ch,
    observe :: arr ch b
  }

newtype Point t arr ch = Point
  { runPoint :: arr (Unit t) ch
  }

newtype Cap t arr ch = Cap
  { runCap :: arr ch (Unit t)
  }

capT :: forall t arr ch. (DiscardT t arr ch) => Cap t arr ch
capT = Cap (discardT @t)

close :: (Category arr) => Poles ch arr a b -> arr a b
close (Poles c o) = c .> o

unclose :: (Category arr) => arr a b -> Poles b arr a b
unclose f = Poles f id

copycat :: (Category arr) => Poles ch arr ch ch
copycat = unclose id

peek :: (Category arr) => Point t arr s -> Cell t s arr a b -> arr (Unit t) b
peek pt (Cell _ o) = runPoint pt .> o

poke :: (Tensor t arr) => Point t arr s -> Cell t s arr a b -> arr a s
poke pt (Cell k _) = unitl' .> tensor (runPoint pt) id .> k

polesOf ::
  (Tensor t arr) =>
  Point t arr ch ->
  Machine t ch arr p ->
  Poles ch arr (Dir p) (Pos p)
polesOf pt (Machine c@(Cell _ o)) = Poles (poke pt c) o

cellOf :: (Tensor t arr) => Cap t arr ch -> Poles ch arr a b -> Cell t ch arr a b
cellOf (Cap cap) (Poles w r) =
  Cell (tensor cap id .> unitl .> w) r

data Process t s arr a b = Process
  { commit :: arr a s,
    cell :: Cell t s arr a b
  }

processOf :: (Category arr) => arr a (t s a) -> Cell t s arr a b -> Process t s arr a b
processOf e (Cell k o) = Process (e .> k) (Cell k o)

processFromSeed :: s -> Cell (,) s (->) a b -> Process (,) s (->) a b
processFromSeed s0 (Cell k o) = Process (\a -> k (s0, a)) (Cell k o)

data Moore a b = forall s. Moore_ (a -> s) (Cell (,) s (->) a b)

pattern Moore ::
  (a -> s) ->
  (s -> a -> s) ->
  (s -> b) ->
  Moore a b
pattern Moore i st ex <- Moore_ i (Cell (curry -> st) ex)
  where
    Moore i st ex = Moore_ i (Cell (uncurry st) ex)

{-# COMPLETE Moore #-}

asMoore :: Process (,) s (->) a b -> Moore a b
asMoore (Process i c) = Moore_ i c

instance Functor (Moore a) where
  fmap f (Moore_ i (Cell k o)) = Moore_ i (Cell k (f . o))
  {-# INLINEABLE fmap #-}

instance Category Moore where
  id :: Moore a a
  id = Moore_ id (Cell snd id)
  {-# INLINE id #-}

  (.) :: Moore b c -> Moore a b -> Moore a c
  Moore_ i2 (Cell k2 o2) . Moore_ i1 (Cell k1 o1) =
    Moore_ inject (Cell step extract)
    where
      inject a = let s1 = i1 a in (s1, i2 (o1 s1))
      step ((s1, s2), a) = let s1' = k1 (s1, a) in (s1', k2 (s2, o1 s1'))
      extract (_, s2) = o2 s2
  {-# INLINE (.) #-}

before :: Moore b c -> (a -> b) -> Moore a c
before (Moore i st ex) f = Moore (i . f) (\s a -> st s (f a)) ex
{-# INLINEABLE before #-}

after :: Moore a b -> (b -> c) -> Moore a c
after (Moore i st ex) f = Moore i st (f . ex)
{-# INLINEABLE after #-}

instance Applicative (Moore a) where
  pure b = Moore (const ()) (\_ _ -> ()) (const b)
  {-# INLINEABLE pure #-}
  Moore i1 st1 ex1 <*> Moore i2 st2 ex2 =
    Moore
      (\a -> (i1 a, i2 a))
      (\(s1, s2) a -> (st1 s1 a, st2 s2 a))
      (\(s1, s2) -> ex1 s1 (ex2 s2))
  {-# INLINEABLE (<*>) #-}

-- These instances make Moore a traced monoidal category under the
-- cartesian tensor, ported from the incumbent
-- "Circuit.Process" — the yank ties a lazy self-referential knot and
-- is productive only when the body is non-strict in the feedback
-- channel. Strict accumulators diverge under the @(,)@ yank; use
-- 'register' for those.

instance Assoc (,) Moore where
  assoc = Moore id (\_ x -> x) (\(~((a, b), c)) -> (a, (b, c)))
  assoc' = Moore id (\_ x -> x) (\(a, ~(b, c)) -> ((a, b), c))

instance Slide (,) Moore where
  slide = Moore id (\_ x -> x) (\(a, ~(b, c)) -> (b, (a, c)))

instance Strength (,) Moore where
  strength (Moore i st ex) =
    Moore
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', st s b))
      (\(~(a, s)) -> (a, ex s))

instance Yank (,) Moore where
  yank (Moore i st ex) =
    Moore
      (\b -> let s0 = i (a0, b); a0 = fst (ex s0) in s0)
      ( \s b ->
          let (s', _a) = fix (\ ~(s'', a') -> (st s (a', b), fst (ex s'')))
           in s'
      )
      (snd . ex)
    where
      fix f = let x = f x in x

instance Unital (,) Moore where
  unitl = Moore snd (\_ (_, a) -> a) id
  unitl' = Moore id (\_ x -> x) ((),)
  unitr = Moore fst (\_ (a, ()) -> a) id
  unitr' = Moore id (\_ x -> x) (,())

instance Tensor (,) Moore where
  tensor (Moore i1 st1 ex1) (Moore i2 st2 ex2) =
    Moore
      (bimap i1 i2)
      (\(s1, s2) (a, c) -> (st1 s1 a, st2 s2 c))
      (bimap ex1 ex2)
  {-# INLINE tensor #-}

instance Action (,) Moore where
  braid = Moore id (const id) sw
    where
      sw (a, b) = (b, a)
  {-# INLINE braid #-}

delay :: s -> Moore s s
delay s0 = Moore (\a -> (s0, a)) (\(_, prev) a -> (prev, a)) fst

register :: s -> Moore (a, s) (b, s) -> Moore a b
register s0 (Moore i st ex) = Moore (\a -> i (a, s0)) (\s a -> st s (a, snd (ex s))) (fst . ex)

scanProcess :: Process (,) s (->) a b -> [a] -> [b]
scanProcess (Process c (Cell k o)) = \case
  [] -> []
  (a : as) -> let s0 = c a in o s0 : go s0 as
  where
    go s (a : as) = let s' = k (s, a) in o s' : go s' as
    go _ [] = []

scan :: Moore a b -> [a] -> [b]
scan (Moore_ i c) = scanProcess (Process i c)

fold :: Moore a b -> [a] -> Maybe b
fold (Moore_ i c) = foldProcess (Process i c)

foldProcess :: Process (,) s (->) a b -> [a] -> Maybe b
foldProcess (Process c (Cell k o)) = \case
  [] -> Nothing
  (a : as) -> Just (go (c a) as)
  where
    go s (a : as) = go (k (s, a)) as
    go s [] = o s

scanThese :: forall s a b. Process (,) s (->) a b -> [a] -> [b]
scanThese (Process c (Cell k o)) = \case
  [] -> []
  (a : as) -> toList (unfold gen (Nothing, a, as))
  where
    gen :: (Maybe s, a, [a]) -> These (Maybe s, a, [a]) b
    gen (ms, a, rest) =
      let s' = case ms of
            Nothing -> c a
            Just s -> k (s, a)
       in case rest of
            [] -> That (o s')
            (a' : rest') -> These (Just s', a', rest') (o s')

type Cocell t ch arr a b = Cell t ch (Op arr) a b

cocell :: arr b ch -> arr ch (t ch a) -> Cocell t ch arr a b
cocell o s = Cell (Op s) (Op o)

pair ::
  forall t chP chC arr a x b.
  (Action t arr, Assoc t arr, DiscardT t arr chP) =>
  Cocell t chP arr a x ->
  Cell t chC arr a b ->
  Cell t (t chP chC) arr (Unit t) b
pair (Cell pk _) (Cell k o) = Cell consumeP produceP
  where
    produceP :: arr (t chP chC) b
    produceP = tensor (discardT @t) o .> unitl
    consumeP :: arr (t (t chP chC) (Unit t)) (t chP chC)
    consumeP = unitr .> tensor (runOp pk) idC .> assoc .> tensor idP (braid .> k)
    idP :: arr chP chP
    idP = id
    idC :: arr chC chC
    idC = id

closedToGenerator ::
  forall t ch arr b.
  (CopyT t arr (t ch (Unit t)), DiscardT t arr (Unit t)) =>
  Cell t ch arr (Unit t) b ->
  arr ch (t ch b)
closedToGenerator c = unitr' .> morphism (fuse c)

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

cellAsLens :: Cell (,) s (->) i o -> Lens s s o i
cellAsLens (Cell k o) = lens o (curry k)

lensAsCell :: Lens s s o i -> Cell (,) s (->) i o
lensAsCell m = Cell (\(s, i) -> snd (applyLens m s) i) (fst . applyLens m)

cellAsEval :: Cell (,) s (->) i o -> s -> Eval (Mono i o) s
cellAsEval (Cell k o) s = EP (EK (o s), EE (\i -> k (s, i)))

evalAsCell :: (s -> Eval (Mono i o) s) -> Cell (,) s (->) i o
evalAsCell f =
  Cell
    (\(s, i) -> case f s of EP (_, EE g) -> g i)
    (\s -> case f s of EP (EK o, _) -> o)
