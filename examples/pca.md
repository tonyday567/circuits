---
name: pca
description: PCA as dagger-compose + Optic (,) residual; why Dagger is here
tags: ['category-theory', 'dagger', 'optics', 'pca', 'experimental']
---
# pca ⟜ principal focus, owned residual

> **Design-only / exploratory.** No eigensolver in the library. This card
> explains the *shape*: why `Dagger` is in circuits, where `Optic (,)`
> comes from, and how PCA sits on that hinge. Numerics stay in an
> interpreter (or hand-rolled 2D below). Builds on [tambara.md](tambara.md)
> and `Circuit.Dagger`.

---

## 0. Where `Optic (,)` comes from

**Not from this card, and not from PCA.** It is the free-Tambara packing
for the **product action**, written down in [tambara.md](tambara.md)
following Milewski (*Tambara Equipment*, 2026).

### Ladder (from Trace → free Tambara → lens)

```text
profunctor j + monoidal action t
        │  free Tambara Φ (left adjoint to forget action)
        ▼
FreeTamb t j s u  =  ∃m x y.  (s → t m x) × j x y × (t m y → u)
        │  j := Rep a b   (focus: get a / put b)
        ▼
Optic t s u a b   =  ∃m.  (s → t m a) × (t m b → u)
        │  t := (,)       (product / cartesian action)
        ▼
Lens s t a b      =  Optic (,) s t a b
        │  Yoneda
        ▼
s → (a, b → t)    classical get + residual put
```

Local types (same as [tambara.md](tambara.md) §1 — paste if needed):

```haskell
-- $setup
-- >>> import Circuit
-- >>> import Circuit.Dagger (Dagger (..), transpose)
-- >>> import Prelude hiding (id, (.), Monoid)
-- >>> import Control.Category
-- >>> import Data.Bifunctor (first, second)

data Optic t s u a b where
  Optic :: (s -> t m a) -> (t m b -> u) -> Optic t s u a b

type Lens s t a b = Optic (,) s t a b

fromClassical :: (s -> (a, b -> t)) -> Lens s t a b
fromClassical f =
  Optic
    (\s -> let (a, k) = f s in (k, a))
    (\(k, b) -> k b)

toClassical :: Lens s t a b -> s -> (a, b -> t)
toClassical (Optic get put) s =
  let (m, a) = get s
   in (a, \b -> put (m, b))

view :: Lens s s a a -> s -> a
view l s = fst (toClassical l s)

set :: Lens s t a b -> b -> s -> t
set l b s = snd (toClassical l s) b
```

Yoneda pocket card:

```text
Optic (,) s t a b
  ≅  ∃m. (s → (m, a), (m, b) → t)
  ≅  s → (a, b → t)
```

**Residual `m` is data the caller owns.** That is the optic side of the
hinge in [tambara.md](tambara.md):

| residual | construct | obligation |
|----------|-----------|------------|
| owned data | `Optic` / lens | none coinductive |
| sealed feedback | `Knot` / `trace` | **productive** |

PCA uses the **owned** column. It never ties the residual to itself.

---

## 1. Why `Dagger` is here

`Circuit.Dagger` is not “for PCA.” It is the **reversible / reverse-mode
wire** of the library:

```haskell
data Dagger arr a b = Dagger
  { fwd :: arr a b
  , bwd :: arr b a   -- not necessarily inverse; the adjoint direction
  }

transpose :: Dagger arr a b -> Dagger arr b a
transpose (Dagger f b) = Dagger b f
```

What it **promises** (structure, not a theorem about floats):

1. **Every wire has two directions** — forward data, backward contribution
   (cotangents in AD; adjoint maps in linear algebra).
2. **`transpose` is involutive on the pair** — swap the two arrows; the
   free dagger category over a base.
3. **Bimonoid dualities on `Net`** — copy ⊣ add, discard ⊣ zero, so
   `transpose` on structural rows is coherent (see `Circuit.Net`,
   `circuits-ad`).
4. **A home for self-adjoint patterns** — maps that equal their transpose
   after you pick a linear base: Gram / covariance live here.

What it does **not** promise:

- eigenvalues, SVD, or variance as a real functional  
- that `bwd` is a category-theoretic adjoint without a chosen inner product  
- productivity (that is the `(,)` `Knot` story)

So: **Dagger is the library’s name for “maps come with a reverse.”**
PCA is one consumer of that name when the base is linear and reverse =
transpose of a matrix.

---

## 2. PCA in that language

One line:

> **Dagger-compose to a self-adjoint, spectrally diagonalize, then an
> `Optic (,)` that focuses on the high-eigenvalue summand and owns the
> low-eigenvalue complement as residual.**

### Pipeline

```text
data X
  │
  │  center (affine → linear; choose origin)
  ▼
linear map X
  │
  │  cov = dagger X  >>>  X     (or X >>> dagger X)
  ▼
self-adjoint positive C
  │
  │  spectral  (interpreter / numerics — not circuits core)
  ▼
orthogonal change of basis + eigenvalues λ₁ ≥ λ₂ ≥ …
  │
  │  split: major (top k)  |  minor (rest)
  ▼
Optic (,)   focus = major coords
            residual m = minor coords
            put = reconstruct
```

| step | circuits vocabulary | who runs it |
|------|---------------------|-------------|
| center | plain base arrow | you |
| `cov = transpose x >>> x` | `Dagger` + `Category` | you |
| spectral | **not** in core | BLAS / hand 2D / `circuits-ad` friend |
| keep / discard | **`Optic (,)` residual ownership** | packing from [tambara.md](tambara.md) |
| reconstruct | `put` of that optic | you |

### Not `trace`

```text
partial trace   forget a factor (uniform in that wire)
PCA truncate    forget low-variance directions (ordered by C)
Knot / trace    seal residual as feedback (productivity tax)
Optic           own residual as data  ← PCA lives here
```

---

## 3. Toy 2D — own the minor axis

No solver: fix a basis where the principal axis is already \(x\) and the
minor axis is \(y\). (Any real PCA run is “change to this basis, then
this packing.”)

```haskell
-- point in the eigenbasis of a 2D cloud
type Pt = (Double, Double)   -- (major, minor)

-- focus = major coordinate; residual m = minor coordinate
-- Optic (,) Pt Pt Double Double
pc1 :: Lens Pt Pt Double Double
pc1 =
  fromClassical $ \(maj, minr) ->
    ( maj
    , \maj' -> (maj', minr) -- put: replace major, keep owned minor
    )

-- >>> view pc1 (3.0, 0.5)
-- 3.0
-- >>> set pc1 10.0 (3.0, 0.5)
-- (10.0,0.5)
```

Reconstruction error lives in the residual you still own:

```haskell
-- project to 1D principal line (zero the minor)
project1 :: Pt -> Pt
project1 p = set pc1 (view pc1 p) (0, 0)  -- major kept, minor wiped via put context
-- cleaner:
project1' :: Pt -> Pt
project1' (maj, _) = (maj, 0)

-- residual variance direction is the owned m after get
discarded :: Pt -> Double
discarded p =
  let (m, _) = case pc1 of
        Optic get _ -> get p
   in m

-- >>> discarded (3.0, 0.5)
-- 0.5
-- >>> project1' (3.0, 0.5)
-- (3.0,0.0)
```

Existential packing made explicit (same lens):

```haskell
-- ∃ m. (Pt → (m, Double), (m, Double) → Pt)  with m = Double (minor)
pc1Ex :: Lens Pt Pt Double Double
pc1Ex =
  Optic
    (\(maj, minr) -> (minr, maj)) -- get: residual first, focus second
    (\(minr, maj') -> (maj', minr))
```

That **is** `Optic (,)`: product residual holds the complement; focus is
the principal coordinate. Classical `s → (a, b → t)` is the Yoneda form
of the same thing.

---

## 4. Non-toy run — package `circuits-pca`

Implemented as `~/haskell/circuits-pca` over **harpie** arrays + hmatrix SVD:

```haskell
import Circuit.PCA
import Harpie.Array.Storable qualified as A

x = A.array [4, 2] ([1,1, 2,2, 3,3, 4,4] :: [Double])
model = fit 1 x
sc = scores model x
xh = projectRows model x
-- dagger face: gramViaDagger (center…) ≡ feature Gram X†X
```

| promise of `Dagger` | PCA use |
|---------------------|---------|
| reverse wire exists | `transpose2` / `gramDagger` |
| compose both ways | `gramFeatures` = \(X^\dagger X\) |
| `transpose` involution | `Circuit.Dagger.transpose` on the pair |
| Net bimonoid duals | AD cousin via `circuits-ad` (linked, not yet spectral) |

Spectral cut = hmatrix `thinSVD`. Protocol = `Circuit.PCA.Optic`.

---

## 5. Hinge with [tambara.md](tambara.md)

```text
                 residual ownership
              own ──────────────── seal
               │                    │
    finite     │ Optic (,)          │ Arr-only / no loop
               │ PCA major/minor    │
               │ lens zoo           │
               │                    │
  productive   │ coinductive optic  │ Knot / Hyper
  coinduction  │ (own a stream)     │ (pay productivity)
```

PCA sits **top-left**: finite residual, product action, owned complement.

Slogan (tied):

> **To make a circuit, surrender the residual to the knot (keep it productive).**  
> **To make an optic, own the residual.**  
> **PCA is an optic: principal = focus, minor = residual you own; Dagger only builds the self-adjoint you split.**

---

## 6. What this does *not* claim

- That `Optic` / `Lens` are exported from `Circuit` today — they are
  **card-local**, provenance [tambara.md](tambara.md).
- That `Dagger` computes PCA — it supplies **transpose-shaped wires**.
- That full lens zoo / grates fall out — other monoidal actions; see
  [tambara.md](tambara.md).
- That dependent types are required — residual type here is a fixed
  complement (`Double` or \(\mathbb{R}^{n-k}\)).

---

## reference

- [tambara.md](tambara.md) — free Tambara, `Optic t`, product → lens, residual ownership  
- [proarrow.md](proarrow.md) / [proequip.md](proequip.md) — equipment floor under Trace  
- `Circuit.Dagger` — `Dagger`, `transpose`, bimonoid duals  
- `Circuit.Net` — structural rows; transpose of wiring  
- Milewski, [*Tambara Equipment*](https://bartoszmilewski.com/2026/07/11/tambara-equipment/)  
  (archive: `~/self/external/bartosz/06-tambara-equipment.md`)  
- Eckart–Young — truncated SVD as best low-rank approximation (spectral interpreter law)
