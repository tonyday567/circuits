{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Circuit.GMachine
  ( Cell (..),
    Body (..),
    CellD (..),
    BodyTT (..),
    cellAsBody,
    cellAsBodyTT,
    bodyTTAsCell,
    cellDAsBodyTT,
    bodyTTAsCellD,
    bodyAsBodyTT,
    bodyTTAsBody,
    Stratum (..),
    ChannelA,
    MonoBody,
    monoIn,
    monoDir,
    fuse,
    unfuse,
    Machine (..),
    Poles (..),
    Point (..),
    Cap (..),
    capT,
    close,
    unclose,
    copycat,
    poles0,
    polesK,
    splay0,
    compose,
    imap,
    iomap,
    omap,
    peek,
    poke,
    polesOf,
    cellOf,
    processOf,
    processFromSeed,
    GMoore (..),
    GMooreT (..),
    TensorSchedule (..),
    scanT,
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
    observe',
    cellAsLens,
    lensAsCell,
    cellAsEval,
    evalAsCell,
  )
where

import Circuit.Bimonoid (CopyT (..), Discard (..), DiscardT (..))
import Circuit.Category (Category (..), K (..), Op (..), (.>))
import Circuit.Poly (Dir, Eval (..), Lens, Mono, Poly, Pos, applyLens, lens, monoDir, monoIn)
import Circuit.Tensor (Action (..), Const (..), SemiTensor (..), Tensor, Unit, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..), toList, (<|))
import Data.These (These (..), these)
import Data.Void (Void)
import Prelude hiding (id, init, read, (.))

data Cell (t :: Type -> Type -> Type) ch (arr :: Type -> Type -> Type) i o = Cell
  { absorb :: arr (t ch i) ch,
    observe :: arr ch o
  }

data Body (t :: Type -> Type -> Type) ch (arr :: Type -> Type -> Type) i o = Body
  { consume :: arr (t ch i) ch,
    produce :: arr ch (t ch o)
  }

-- | The @(Const, t)@ corner of the 'Body' rectangle: absorb bare, emit
-- grammared.
--
-- The rectangle is spanned by which legs carry the channel grammar.
-- 'Cell' is the @(t, Const)@ corner — 'absorb' takes the grammared
-- @t ch i@, 'observe' emits bare @o@; the @(Const, Const)@ corner is the
-- closed machine, a plain @arr i o@ with no channel at all; the @(t, t)@
-- diagonal is 'Body', with 'Stratum' the fully fused spelling.
--
-- 'expunge' commits passively from the input alone — no history, the
-- @Const@ row — and it is the write leg of 'Poles'. 'imbue' is the
-- produce of 'Body' — the channel update rides out in the emit package
-- @arr ch (t ch o)@.
--
-- Memoryless BY CONSTRUCTION: 'expunge' never sees the channel, so it
-- cannot thread state, and @imbue@'s update is emitted (logging) but
-- never carried forward into the next step. If threading is wanted, the
-- record to use is 'Body' with 'produce'.
--
-- At @t = 'Either'@, @imbue@'s package carries completion: 'Left' =
-- evolve, 'Right' = done — the exit constructor that the observe of
-- 'Cell', @arr ch o@ with no constructors, cannot say. The witnesses
-- live in "Axioma.GMachine".
data CellD (t :: Type -> Type -> Type) ch (arr :: Type -> Type -> Type) i o = CellD
  { expunge :: arr i ch,
    imbue :: arr ch (t ch o)
  }

-- | The general two-legged machine: 'consume' takes the input grammar
-- @t ch i@, 'produce' emits the output grammar @t' ch o@ — the record
-- the corner family factors through. 'Cell' is the @(t, Const)@ corner,
-- 'CellD' the @(Const, t)@ corner, 'Body' the @(t, t)@ diagonal, and
-- @(Const, Const)@ the closed machine; see 'CellD' for the corner
-- reading.
--
-- Two free tensors do not compose (@t' ch b@ cannot feed @t ch b@), so
-- the 'Category' lives on the diagonal — this record says the mixed
-- corners without composing them.
--
-- The lifts to and from the corner records land at @arr = (->)@:
-- wrapping and unwrapping the 'Const' grammar is a pure map, and the
-- library has no general pure lift into @arr@ (the story is collected
-- on the arr card, out of scope here).
data BodyTT (t :: Type -> Type -> Type) (t' :: Type -> Type -> Type) ch (arr :: Type -> Type -> Type) i o = BodyTT
  { consume :: arr (t ch i) ch,
    produce :: arr ch (t' ch o)
  }

-- Cell to the update package: copy-gated, the same price fuse pays.
cellAsBody :: (CopyT t arr ch) => Cell t ch arr i o -> Body t ch arr i o
cellAsBody (Cell k p) = Body k (copyT .> tensor id p)

-- The corner isomorphisms at the (->) corner — each direction names
-- its corner in the term. The general-arr spelling needs a pure lift
-- into arr the library does not have; the round trips are witnessed in
-- "Axioma.GMachine".
cellAsBodyTT :: Cell t ch (->) i o -> BodyTT t Const ch (->) i o
cellAsBodyTT (Cell k p) = BodyTT k (Const . p)

bodyTTAsCell :: BodyTT t Const ch (->) i o -> Cell t ch (->) i o
bodyTTAsCell (BodyTT k p) = Cell k (\c -> case p c of Const o -> o)

cellDAsBodyTT :: CellD t ch (->) i o -> BodyTT Const t ch (->) i o
cellDAsBodyTT (CellD x g) = BodyTT (\(Const i) -> x i) g

bodyTTAsCellD :: BodyTT Const t ch (->) i o -> CellD t ch (->) i o
bodyTTAsCellD (BodyTT k g) = CellD (\i -> k (Const i)) g

bodyAsBodyTT :: Body t ch (->) i o -> BodyTT t t ch (->) i o
bodyAsBodyTT (Body k p) = BodyTT k p

bodyTTAsBody :: BodyTT t t ch (->) i o -> Body t ch (->) i o
bodyTTAsBody (BodyTT k p) = Body k p

newtype Stratum t ch arr i o = Stratum {morphism :: arr (t ch i) (t ch o)}

type ChannelA ch arr i o = Stratum (,) ch arr i o

instance (Category arr) => Category (Stratum t ch arr) where
  id :: forall a. Stratum t ch arr a a
  id = Stratum id
  {-# INLINE id #-}

  (.) :: forall a b c. Stratum t ch arr b c -> Stratum t ch arr a b -> Stratum t ch arr a c
  Stratum g . Stratum f = Stratum (g . f)
  {-# INLINE (.) #-}

fuse ::
  forall t s arr a b.
  (CopyT t arr (t s a), DiscardT t arr a) =>
  Cell t s arr a b ->
  Stratum t s arr a b
fuse (Cell k o) =
  Stratum (tensor k (o . unitr . tensor id (discardT @t)) . copyT)

unfuse ::
  forall s arr i o.
  (Tensor (,) arr, Discard arr s, Discard arr o) =>
  ChannelA s arr i o ->
  Cell (,) (s, o) arr i o
unfuse (Stratum f) = Cell (tensor projFst id .> f) projSnd
  where
    projFst :: arr (s, o) s
    projFst = unitr . tensor id discard
    projSnd :: arr (s, o) o
    projSnd = unitl . tensor discard id

type MonoBody t s arr i o = Stratum t s arr (Either Void i) (o, ())

newtype Machine (t :: Type -> Type -> Type) s (arr :: Type -> Type -> Type) (p :: Poly) = Machine
  {machineCell :: Cell t s arr (Dir p) (Pos p)}

data Poles ch arr a b = Poles
  { write :: arr a ch,
    read :: arr ch b
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

poles0 :: arr a () -> arr () b -> Poles () arr a b
poles0 = Poles

polesK :: (a -> m ()) -> m b -> Poles () (K m) a b
polesK write receive = Poles (K write) (K $ const receive)

splay0 :: Poles () arr a b -> (arr a (), arr () b)
splay0 (Poles c o) = (c, o)

compose :: (Category arr) => Poles ch1 arr a b -> Poles ch2 arr b c -> Poles ch1 arr a c
compose (Poles c1 o1) (Poles c2 o2) = Poles c1 (o1 .> c2 .> o2)

iomap :: (Category arr) => arr a' a -> arr b b' -> Poles ch arr a b -> Poles ch arr a' b'
iomap f g (Poles c o) = Poles (f .> c) (o .> g)

imap :: (Category arr) => arr a' a -> Poles ch arr a b -> Poles ch arr a' b
imap f (Poles c o) = Poles (f .> c) o

omap :: (Category arr) => arr b b' -> Poles ch arr a b -> Poles ch arr a b'
omap g (Poles c o) = Poles c (o .> g)

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

processOf :: (Category arr) => arr a (t s a) -> Cell t s arr a b -> GMoore t s arr a b
processOf e (Cell k o) = GMoore (e .> k) (Cell k o)

processFromSeed :: s -> Cell (,) s (->) a b -> GMoore (,) s (->) a b
processFromSeed s0 (Cell k o) = GMoore (\a -> k (s0, a)) (Cell k o)

data GMoore (t :: Type -> Type -> Type) ch (arr :: Type -> Type -> Type) i o = GMoore
  { init :: arr i ch,
    cell :: Cell t ch arr i o
  }

data GMooreT (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) i o
  = forall ch.
    GMooreT (GMoore t ch arr i o)

-- The constructor grammar of t priced as one method.
-- Law: echoFold . tensor f f = f . echoFold
class (Tensor t arr) => TensorSchedule t arr where
  echoFold :: arr (t a a) a

instance TensorSchedule (,) (->) where
  echoFold = snd
  {-# INLINE echoFold #-}

instance TensorSchedule Either (->) where
  echoFold = either id id
  {-# INLINE echoFold #-}

instance TensorSchedule These (->) where
  echoFold = these id id (\_ i -> i)
  {-# INLINE echoFold #-}

instance (TensorSchedule t (->)) => Category (GMooreT t (->)) where
  id = GMooreT (GMoore id (Cell echoFold id))
  {-# INLINE id #-}
  GMooreT (GMoore j2 (Cell k2 e2)) . GMooreT (GMoore j1 (Cell k1 e1)) =
    GMooreT (GMoore j (Cell k e))
    where
      j i = let c1 = j1 i in (c1, j2 (e1 c1))
      k x = let c1' = k1 (tensor fst id x) in (c1', k2 (tensor snd (const (e1 c1')) x))
      e = e2 . snd
  {-# INLINE (.) #-}

-- Moore is the cartesian specialisation of the existential machine: the
-- same existential channel, the same run semantics, one spelling.
type Moore = GMooreT (,) (->)

pattern Moore ::
  (a -> s) ->
  (s -> a -> s) ->
  (s -> b) ->
  Moore a b
pattern Moore i st ex <- GMooreT (GMoore i (Cell (curry -> st) ex))
  where
    Moore i st ex = GMooreT (GMoore i (Cell (uncurry st) ex))

{-# COMPLETE Moore #-}

asMoore :: GMoore (,) s (->) a b -> Moore a b
asMoore (GMoore i c) = GMooreT (GMoore i c)

instance Functor (GMooreT (,) (->) a) where
  fmap f (GMooreT (GMoore i (Cell k o))) = GMooreT (GMoore i (Cell k (f . o)))
  {-# INLINEABLE fmap #-}

before :: Moore b c -> (a -> b) -> Moore a c
before (Moore i st ex) f = Moore (i . f) (\s a -> st s (f a)) ex
{-# INLINEABLE before #-}

after :: Moore a b -> (b -> c) -> Moore a c
after (Moore i st ex) f = Moore i st (f . ex)
{-# INLINEABLE after #-}

instance Applicative (GMooreT (,) (->) a) where
  pure b = Moore (const ()) (\_ _ -> ()) (const b)
  {-# INLINEABLE pure #-}
  Moore i1 st1 ex1 <*> Moore i2 st2 ex2 =
    Moore
      (\a -> (i1 a, i2 a))
      (\(s1, s2) a -> (st1 s1 a, st2 s2 a))
      (\(s1, s2) -> ex1 s1 (ex2 s2))
  {-# INLINEABLE (<*>) #-}

-- These instances make @GMooreT (,) (->)@ — 'Moore' — a traced monoidal
-- category under the cartesian tensor, ported from the retired Process
-- module — the yank ties a lazy self-referential knot and is productive
-- only when the body is non-strict in the feedback channel. Strict
-- accumulators diverge under the @(,)@ yank; use 'register' for those.

instance Assoc (,) (GMooreT (,) (->)) where
  assoc = Moore id (\_ x -> x) (\(~((a, b), c)) -> (a, (b, c)))
  assoc' = Moore id (\_ x -> x) (\(a, ~(b, c)) -> ((a, b), c))

instance Slide (,) (GMooreT (,) (->)) where
  slide = Moore id (\_ x -> x) (\(a, ~(b, c)) -> (b, (a, c)))

instance Strength (,) (GMooreT (,) (->)) where
  strength (Moore i st ex) =
    Moore
      (\(~(a, b)) -> (a, i b))
      (\(~(_, s)) (~(a', b)) -> (a', st s b))
      (\(~(a, s)) -> (a, ex s))

instance Yank (,) (GMooreT (,) (->)) where
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

instance Unital (,) (GMooreT (,) (->)) where
  unitl = Moore snd (\_ (_, a) -> a) id
  unitl' = Moore id (\_ x -> x) ((),)
  unitr = Moore fst (\_ (a, ()) -> a) id
  unitr' = Moore id (\_ x -> x) (,())

instance SemiTensor (,) (GMooreT (,) (->)) where
  tensor (Moore i1 st1 ex1) (Moore i2 st2 ex2) =
    Moore
      (bimap i1 i2)
      (\(s1, s2) (a, c) -> (st1 s1 a, st2 s2 c))
      (bimap ex1 ex2)
  {-# INLINE tensor #-}

-- | 'Tensor' for 'GMooreT' is the conjunction: 'Unital' (GMachine) plus
-- this 'SemiTensor'.
instance Tensor (,) (GMooreT (,) (->))

instance Action (,) (GMooreT (,) (->)) where
  braid = Moore id (const id) sw
    where
      sw (a, b) = (b, a)
  {-# INLINE braid #-}

delay :: s -> Moore s s
delay s0 = Moore (\a -> (s0, a)) (\(_, prev) a -> (prev, a)) fst

register :: s -> Moore (a, s) (b, s) -> Moore a b
register s0 (Moore i st ex) = Moore (\a -> i (a, s0)) (\s a -> st s (a, snd (ex s))) (fst . ex)

-- Input-list elimination: each step injects the input through the
-- tensor's own left unit — memoryless at Either, That-biased at These.
scanT :: (TensorSchedule t (->)) => GMooreT t (->) i o -> [i] -> [o]
scanT (GMooreT (GMoore j (Cell k e))) = \case
  [] -> []
  (i : is) -> let c = j i in e c : go c is
  where
    go _ [] = []
    go c (i : is) = let c' = k (tensor (const c) id (unitl' i)) in e c' : go c' is

scanProcess :: GMoore (,) s (->) a b -> [a] -> [b]
scanProcess (GMoore c (Cell k o)) = \case
  [] -> []
  (a : as) -> let s0 = c a in o s0 : go s0 as
  where
    go s (a : as) = let s' = k (s, a) in o s' : go s' as
    go _ [] = []

scan :: Moore a b -> [a] -> [b]
scan (GMooreT (GMoore i c)) = scanProcess (GMoore i c)

fold :: Moore a b -> [a] -> Maybe b
fold (GMooreT (GMoore i c)) = foldProcess (GMoore i c)

foldProcess :: GMoore (,) s (->) a b -> [a] -> Maybe b
foldProcess (GMoore c (Cell k o)) = \case
  [] -> Nothing
  (a : as) -> Just (go (c a) as)
  where
    go s (a : as) = go (k (s, a)) as
    go s [] = o s

scanThese :: forall s a b. GMoore (,) s (->) a b -> [a] -> [b]
scanThese (GMoore c (Cell k o)) = \case
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
  (Action t arr, DiscardT t arr chP) =>
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

-- | The eliminator consuming @(s, i)@, reflecting the input immediately
-- — the honest answer to input-blindness at the eliminator level.
-- Provisional name, standing until the haddock pass.
--
-- Variance account, pinned: the observation leg @arr ch o@ never mentions
-- the input, pre or post, by construction — the type has no slot for it.
-- A pre-step eliminator built on that leg therefore outputs a value that
-- provably ignores the current input; that is the old 'Moore' reading.
-- @observe'@ closes the gap in one step — absorb, then observe — so the
-- input is reflected immediately.
observe' :: Cell (,) s (->) i o -> (s, i) -> o
observe' (Cell k o) (s, i) = o (k (s, i))

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
