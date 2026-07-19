---
name: tambara
description: Tambara equipment over Trace — vertical/horizontal swaps, free Tambara, Trace to lens families
tags: ['category-theory', 'tambara', 'equipment', 'optics', 'experimental']
---
# tambara ⟜ free moves, free Tambara, Trace → lenses

> **Design-only / exploratory.** Local types for `FreeTamb` / `Optic` / lens
> families live in this card. Promote to `src/` only when a consumer wants
> them as API. Builds on [proequip.md](proequip.md), [proarrow.md](proarrow.md),
> and Bartosz Milewski, [*Tambara Equipment*](https://bartoszmilewski.com/2026/07/11/tambara-equipment/)
> (July 2026). Local archive: `~/self/external/bartosz/06-tambara-equipment.md`.
>
> Repl-verified against `cabal repl circuits` (lazy `(,)` residuals only —
> forcing a self-tied residual is a black hole; see [patterns](../../../other/haskell-agent/buff/patterns.md)).

Slogan (Bartosz / Stroiński):

> **Tambara modules : monoidal functors :: profunctors : functors.**

Goal of this card: get *moves* under your fingers. Swap things on the
vertical edge and the horizontal edge independently, and watch what
stays fixed. Then walk the direct path from `Trace` / `Knot` to the
classical lens family.

```haskell
-- $setup
-- >>> import Circuit
-- >>> import qualified Circuit.Trace as T
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Category
-- >>> import Data.Bifunctor (first, second, bimap)
-- >>> import Data.Profunctor (Profunctor (..), dimap)
```

---

## 0. The chessboard

Double category of the Tambara equipment (self-action case for Circuit):

```
                    horizontal  (Tambara / channel / "relation")
                 ─────────────────────────────────────────────►
               │
   vertical    │     ·············· 2-cell (Cell / Knot) ·············
  (monoidal    │
   functor /   │
   transform)  ▼
```

| edge | what you swap | Circuit instance |
|------|---------------|------------------|
| **horizontal** | how two ends talk (the channel / profunctor) | `Trace` body, `These` token, `Co`/`Contra`, free Tambara residual |
| **vertical** | how you reindex ends (action-preserving map) | `dimap` / `Arr f` / `ambient` / monoidal `f` on companions |
| **2-cell** | a square relating both | `Knot`, `Cell f g h j`, unit/counit of open/close |

Equipment slogan in one line: every vertical arrow has a **companion**
(horizontal forward) and a **conjoint** (horizontal backward), and the
unit/counit cells yank.

Under Circuit's self-action (`Act m x = t m x`), every hom is already
Tambara: `leftAct = second = untrace`-on-payload. So Trace already sits
in **Tam**, not just **Prof** — free of charge.

---

## 1. Local kit (paste once)

Not in the library yet. Names match Bartosz's post.

```haskell
-- action-compatible profunctor (left action only; same act both sides)
class (Profunctor j) => Tambara t j where
  leftAct :: j a b -> j (t m a) (t m b)

instance Tambara (,) (->) where
  leftAct = second

instance Tambara Either (->) where
  leftAct = second   -- right / fmap on Either

-- lift / restrict a horizontal arrow along a pair of vertical maps
newtype Lift f g j a c = Lift { unLift :: j (f a) (g c) }

instance (Profunctor j, Functor f, Functor g) => Profunctor (Lift f g j) where
  dimap l r (Lift j) = Lift (dimap (fmap l) (fmap r) j)

-- 2-cell: natural map from H into the lift of J
type Cell f g h j = forall a c. h a c -> j (f a) (g c)

-- companion / conjoint of a (monoidal) functor f
type Companion f = Lift f Identity (->)   -- B(f, 1)
type Conjoint  f = Lift Identity f (->)   -- B(1, f)

-- free Tambara (left adjoint to forget action)
data FreeTamb t j s u where
  FreeTamb :: (s -> t m x) -> j x y -> (t m y -> u) -> FreeTamb t j s u

-- representable "focus" profunctor Θ_ab
data Rep a b x y = Rep (x -> a) (b -> y)

-- optic = free Tambara on Rep (existential residual)
data Optic t s u a b where
  Optic :: (s -> t m a) -> (t m b -> u) -> Optic t s u a b

-- classical families (product / coproduct / list)
type Lens     s t a b = Optic (,)     s t a b
type Prism    s t a b = Optic Either  s t a b
type Traversal s t a b = s -> ([b] -> t, [a])   -- poly action, Yoneda-reduced
```

Yoneda reductions you can keep in your pocket:

```
Optic (,) s t a b
  ≅  ∃m. (s → (m, a), (m, b) → t)
  ≅  s → (a, b → t)                 -- "get + residual put"
  ≅  classical Lens s t a b

Optic Either s t a b
  ≅  ∃m. (s → Either m a, Either m b → t)
  ≅  classical Prism (match / build)

Traversal (list stand-in for poly)
  ≅  s → ([b] → t, [a])
```

---

## 2. Horizontal swaps — change the channel, keep the ends

Same vertical edges (`id`), different horizontal arrows.

### 2a. Hom as Tambara

```haskell
-- leftAct on (->) is second — payload transform under a frozen residual
-- >>> leftAct @(,) (+1) (True, 10)
-- (True,11)
-- >>> leftAct @Either (+1) (Right 10)
-- Right 11
-- >>> leftAct @Either (+1) (Left "skip")
-- Left "skip"
```

Horizontal move: product residual holds *and* transforms; coproduct residual
is a *choice* — only the focused branch sees the map. That is already the
lens/prism distinction at the level of `leftAct`.

### 2b. Co / Contra — companion & conjoint of `id`

```haskell
-- open / close are η / ε of Contra ⊣ Co (see Circuit.Ends.Unit)
-- >>> let ends = open
-- >>> run (close (conjoint ends) (companion ends)) ()
-- ()
```

Spider lemma (equipment):

```
Knot body  ≅  open >>> body' >>> close
```

Horizontal content is the channel; vertical content is identity. Plugging
with `close` is the counit 2-cell.

### 2c. FreeTamb as a horizontal arrow you can re-act

```haskell
-- re-act a FreeTamb: enlarge the residual (Bartosz leftAct)
reactFree :: FreeTamb (,) j s u -> FreeTamb (,) j (n, s) (n, u)
reactFree (FreeTamb get j put) =
  FreeTamb
    (\(n, s) -> let (m, x) = get s in ((n, m), x))
    j
    (\((n, m), y) -> (n, put (m, y)))

-- a trivial FreeTamb on the hom
homFree :: FreeTamb (,) (->) Int Bool
homFree = FreeTamb (\s -> ((), s)) even (\((), b) -> b)

-- >>> let FreeTamb g j p = reactFree homFree
-- >>> p (first ("tag"++) (g ("x", 2)))
-- ("tagx",True)
```

Horizontal move: grow the residual. The focus map `j` is untouched —
exactly "change the channel scaffolding, keep the fibre transform."

---

## 3. Vertical swaps — change the ends, keep the channel shape

Same horizontal class, different monoidal reindexing.

### 3a. `dimap` / `Arr` on a Knot — vertical composition of the 2-cell

```haskell
-- residual is unit; irrefutable pattern so the knot wire is never forced
k :: T.Trace (,) (->) Int Int
k = T.Knot (\ ~(_, n) -> ((), n + 1))

-- dimap on Knot threads second through the channel (tightening)
-- body sees (*2) n = 6, emits 7, then (+10) → 17
-- >>> run (dimap (*2) (+10) k) 3
-- 17
```

Vertical move: transform what sits on the *outside* of the square. The
channel type and loop law stay put. (Forcing a `(,)` residual that
depends on itself is a black hole — keep feedback productive; that is
exactly why optic residuals are plain data and Knot residuals are not.)

### 3b. `ambient` — monoidal vertical "tag with state"

```haskell
-- ambient :: Trace t arr a b -> Trace t arr (t s a) (t s b)
-- state slides past Knot via braid (yanking)
step :: T.Trace (,) (->) Int Int
step = T.Arr (+1)

-- >>> run (ambient step) ("ctx", 41)
-- ("ctx",42)
```

`ambient` is the vertical arrow "tensor with a fixed wire." Its companion
would be a state-aware channel end (generalised `Co`); its conjoint the
dual. Today's `open` is only the `id` case.

### 3c. Companion of a non-id vertical (sketch)

Bartosz:

```haskell
type Companion f = Lift f Identity (->)   -- ⟨a,b⟩ ↦ B(f a, b)
type Conjoint  f = Lift Identity f (->)   -- ⟨b,a⟩ ↦ B(b, f a)
```

For `f = (s,)` (state tag; monoidal w.r.t. product action):

```haskell
-- Companion (s,)  ≅  (s, a) → b     "read state, produce b"
-- Conjoint  (s,)  ≅  a → (s, b)     "write state, produce b"
-- unit/counit cells are curry/uncurry + eval — the IntHom of the post
```

Play move: keep the *same* horizontal plumbing (`open`/`close` shape),
swap `f` from `Identity` to `(s,)` and watch the end types pick up state.
That is the vertical slot the equipment exists to open.

### 3d. Swap the *action* (product ↔ coproduct)

Two 0-cells of Tam you already run:

| actegory | tensor | vertical monoidal maps | horizontal Tambara |
|----------|--------|------------------------|--------------------|
| cartesian | `(,)` | `ambient`, braid, `par` | residual holds |
| cocartesian | `Either` | `right` / `untrace`, cocartesian slide | residual chooses |

```haskell
-- same "focus transform" (+1), different action
-- >>> leftAct @(,)    (+1) (True,  10)
-- (True,11)
-- >>> leftAct @Either (+1) (Right 10)
-- Right 11
```

Vertical-in-the-large: a monoidal functor between these two actegories
would be a *map of universes* (iteration ↔ streaming). Rare as a total
function; common as a *protocol* (run an `Either` loop and stream
partial results on a `(,)` channel). That is future card material —
name it so you notice when you build one.

---

## 4. Orthogonal play — zip-style (from proequip)

Recall the foldH zip: two horizontal folds, one vertical combine.

```
horizontal:  foldH xs  .  foldH ys     -- channel token is the profunctor
vertical:    combine / id              -- element map, slots open
```

`foldH ys These _` is a conjoint (pure supply). Swap the vertical
`combine` without touching the horizontal pipeline → `zipWith`. That is
the *feeling* to train: horizontal composition is plumbing; vertical is
payload; yanking says they commute when the cells are equipment cells.

In Trace language the same orthogonality is:

```
horizontal composition  =  (.) / (>>>) on Trace
vertical composition    =  dimap / ambient / untrace-sliding
2-cell                  =  Knot (tightening = Category cases)
```

---

## 5. Direct path: Trace → free Tambara → lens families

One ladder. Each rung is a type equality (up to Yoneda / packing).

### Rung 1 — `Knot` is an open channel

```haskell
-- Knot :: arr (t m b) (t m c) -> Trace t arr b c
-- hidden residual m, payload b → c
```

Operational: open a wire of type `m`, run a body that may use it, close.

### Rung 2 — spider: ends as companion/conjoint of `id`

```haskell
-- open  :: a -> (Co arr t a, Contra arr t a)     -- η
-- close :: Contra arr t a -> Co arr t a -> Trace t arr a a   -- ε
--
-- Knot body  ≅  open seed >>> body' >>> close
```

Still Trace. Ends travel independently; `close` is the counit 2-cell.

### Rung 3 — free Tambara packs the residual

```haskell
-- FreeTamb t j s u =
--   ∃ m x y.  (s → t m x) × j x y × (t m y → u)
```

Read left-to-right: **view into an action context**, **do a horizontal
step**, **put back**. When `j = (->)`, this is "open residual, map
payload, close" — the same story as `Knot`/`untrace` without forcing
the residual to be *feedback*. Feedback is the special case where put's
`m` is wired back into get's `m` by `trace`.

```haskell
-- from a plain function under a residual to FreeTamb on (->)
asFree :: (s -> (m, a)) -> ((m, b) -> t) -> (a -> b) -> FreeTamb (,) (->) s t
asFree get put f = FreeTamb get f put
```

### Rung 4 — focus = representable `Rep a b`

```haskell
-- Θ_ab x y = (x → a) × (b → y)
-- Optic t s u a b = FreeTamb t (Rep a b) s u
--                ≅ ∃m. (s → t m a) × (t m b → u)
```

The horizontal step collapses to "get the focus / put the focus." No
arbitrary `j` left — only the optic residual.

```haskell
toOptic :: FreeTamb t (Rep a b) s u -> Optic t s u a b
toOptic (FreeTamb get (Rep xa by) put) =
  Optic (second xa . get) (put . second by)
  -- with t = (,) ; general t needs Bifunctor second
```

For product, specialise:

```haskell
toLens :: FreeTamb (,) (Rep a b) s t -> Lens s t a b
toLens (FreeTamb get (Rep xa by) put) =
  Optic (\s -> let (m, x) = get s in (m, xa x))
        (\(m, b) -> put (m, by b))
```

### Rung 5 — Yoneda: classical lens packing

```haskell
-- ∃m. (s → (m, a), (m, b) → t)  ≅  s → (a, b → t)

fromClassical :: (s -> (a, b -> t)) -> Lens s t a b
fromClassical f = Optic
  (\s -> let (a, k) = f s in (k, a))      -- residual = the putter
  (\(k, b) -> k b)

toClassical :: Lens s t a b -> (s -> (a, b -> t))
toClassical (Optic get put) = \s ->
  let (m, a) = get s
  in  (a, \b -> put (m, b))
```

Worked example — `_1` on a pair:

```haskell
_1 :: Lens (a, c) (b, c) a b
_1 = fromClassical (\(a, c) -> (a, \b -> (b, c)))

-- view
view :: Lens s s a a -> s -> a
view l s = fst (toClassical l s)

-- set
set :: Lens s t a b -> b -> s -> t
set l b s = snd (toClassical l s) b

-- >>> view _1 ("hi", 99 :: Int)
-- "hi"
-- >>> set _1 "yo" ("hi", 99 :: Int)
-- ("yo",99)
```

### Rung 6 — families by swapping the *action* (horizontal 0-cell)

Same optic packing; different `t`:

```haskell
-- Lens:  product residual holds context
-- (equivalent packing: Optic (\(a,c) -> (c,a)) (\(c,b) -> (b,c)))

-- Prism: coproduct residual is "not this constructor"
_Just :: Prism (Maybe a) (Maybe b) a b
_Just = Optic
  (\s -> case s of Just a -> Right a; Nothing -> Left ())
  (\case Left () -> Nothing; Right b -> Just b)

preview :: Prism s s a a -> s -> Maybe a
preview (Optic get _) s = case get s of
  Right a -> Just a
  Left _  -> Nothing

review :: Prism s t a b -> b -> t
review (Optic _ put) b = put (Right b)

-- >>> preview _Just (Just (3 :: Int))
-- Just 3
-- >>> preview _Just (Nothing :: Maybe Int)
-- Nothing
-- >>> review _Just (7 :: Int)
-- Just 7

-- Traversal: poly / list residual (Yoneda-reduced)
each :: Traversal [a] [b] a b
each xs = (id, xs)   -- putter rebuilds the list; gets all focuses

overT :: Traversal s t a b -> (a -> b) -> s -> t
overT tr f s = let (put, as) = tr s in put (map f as)

-- >>> overT each (+1) [1,2,3 :: Int]
-- [2,3,4]
```

### Rung 7 — where `trace` sits on the ladder

| construct | residual | feedback? | optic reading |
|-----------|----------|-----------|---------------|
| `Arr f` | none | no | pure vertical map |
| `untrace f` | open wire, not closed | no | optic get without put (or put = id) |
| `Knot body` | hidden `m`, closed by `trace` | **yes** | optic whose put residual is wired to get |
| `open`/`close` | ends of residual, externally plugged | optional | unit/counit cells; spider form of Knot |
| `Optic t` | existential `m`, caller-owned | no | free Tambara on `Rep` — **lens family** |
| `FreeTamb t j` | existential `m`, arbitrary horizontal `j` | no | optic with a general fibre step |

**Punchline:** a lens is a *Trace-shaped packing that refuses to close
the residual as feedback*. `Knot` closes it with `trace`. Optics leave
it existential so the caller (or a larger optic) owns the context. Free
Tambara is the common generalisation; `Rep` specialises to lens
families; choice of action `t` picks the family (lens / prism /
traversal / …).

Diagram:

```
  Trace / Knot                 free Tambara Φj
       │                            │
       │ spider                     │ j := Rep a b
       ▼                            ▼
  open / close  ─────────────►   Optic t s t a b
       │                            │
       │ refuse feedback            │ t := (,) | Either | poly
       │ keep residual ∃m           ▼
       └─────────────────────►  Lens / Prism / Traversal
```

---

## 6. Drill — five moves to internalise

Paste, swap one thing, predict the type, run.

1. **Horizontal residual grow** — `reactFree` on a FreeTamb; focus map fixed.
2. **Vertical payload map** — `dimap f g` on a `Knot`; channel fixed.
3. **Vertical state tag** — `ambient` around an `Arr`; compare to companion of `(s,)`.
4. **Action swap** — same focus `(+1)` under `leftAct @(,)` vs `leftAct @Either`.
5. **Close or don't** — same `(get, put)` pair as `Optic (,) …` *and* as a
   `Knot` body via `trace (\(m,a) -> let b = f a in (m,b))`. One is a lens
   step; one is a feedback circuit. Same residual, different 2-cell.

```haskell
-- same residual packing, two 2-cells — irrefutable so Knot can close
getPutLazy :: (Int, Bool) -> (Int, Bool)
getPutLazy ~(_, b) = (0, not b)

asLensStep :: Lens (Int, Bool) (Int, Bool) Bool Bool
asLensStep = Optic id getPutLazy
-- residual is data the caller owns

asKnot :: T.Trace (,) (->) Bool Bool
asKnot = T.Knot getPutLazy
-- residual is feedback; put's m is wired to get's m by trace

-- >>> snd (toClassical asLensStep (0, False)) True
-- (0,False)
-- >>> run asKnot False
-- True
```

Operational heart of the Trace/optics split: **feedback residual must be
productive (lazy / coinductive); optic residual is plain data the caller
owns.** Same packing, different 2-cell.

---

## 7. What to promote later

| idea | card status | promote when |
|------|-------------|--------------|
| `Tambara t j` / `leftAct` | local class | a second consumer besides optics |
| `FreeTamb` / `Optic` | local data | circuits-optics or optics interop |
| companion of monoidal `f` | sketch | state-aware ends beyond `open` |
| monoidal functors `(,)` ↔ `Either` | named, unwritten | a real protocol needs both universes |
| equipment axioms for Trace | open lemma ([proarrow.md](proarrow.md)) | formal verification pass |

---

## 8. Breadcrumb (extends proequip)

1. foldH / push / zip — two composition layers  
2. Cell / Knot as 2-cell — Trace is a double category  
3. Strong + Costrong on Hom — Trace is already equipment-shaped ([proarrow.md](proarrow.md))  
4. **Tambara** — horizontals are action-compatible; verticals monoidal  
5. **Co/Contra = companion/conjoint of id**; general `f` next  
6. **Free Tambara → Optic → Lens/Prism/Traversal** — residual owned vs residual fed back  
7. Poly action ↔ `Circuit.Poly` / traversals — next card  
8. **PCA** — dagger-compose + own minor residual via `Optic (,)` — [pca.md](pca.md)

---

## reference

- Milewski, [*Tambara Equipment*](https://bartoszmilewski.com/2026/07/11/tambara-equipment/), July 2026  
  (archive: `~/self/external/bartosz/06-tambara-equipment.md`)  
- Milewski, [*Actegories*](https://bartoszmilewski.com/2026/06/30/actegories/), June 2026  
- Milewski, [*Profunctor Equipment in Haskell*](https://bartoszmilewski.com/2026/05/16/profunctor-equipment-in-haskell/), May 2026  
- Stroiński, [*Module categories, internal bimodules and Tambara modules*](https://arxiv.org/abs/2210.13443v1)  
- [proequip.md](proequip.md) — foldH, Cell, Knot as 2-cell  
- [proarrow.md](proarrow.md) — Traced ≅ Strong + Costrong  
- `Circuit.Ends.Unit` — `HasUnit` / `open`, spider lemma  
- `Circuit.Trace` — `Co`, `Contra`, `close`, `Knot`  
- nLab: [equipment](https://ncatlab.org/nlab/show/equipment), [Tambara module](https://ncatlab.org/nlab/show/Tambara+module)
