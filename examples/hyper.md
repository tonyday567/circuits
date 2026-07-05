# Hyper — the final encoding

`Hyper` is the coinductive / final encoding.  Where `Trace` makes
feedback explicit with a `Knot` constructor, `Hyper` dissolves the
feedback channel into the type itself.  Every `Hyper a b` already
carries a continuation `Hyper b a` — the feedback is structural.

```haskell
-- $setup
-- >>> import Control.Category ((.))
-- >>> import Data.Profunctor (dimap)
-- >>> import Circuit (Trace(..), run, trace, untrace)
-- >>> import Circuit.Hyper
-- >>> import Prelude hiding (id, (.))
```

---

## the type

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

To produce a `b`, you invoke the dual `Hyper b a` — a continuation that
can feed values back.  Unfolding the recursion:

```
Hyper a b = (((...  → a) → b) → a) → b
```

The self-reference is in the type, not a constructor.  There is no `Knot`.
The dual arrow is always present — it's the argument to `invoke`.

---

## the five operations

| operation | type | what it does |
|-----------|------|-------------|
| `lift` / `↑` | `(a -> b) -> Hyper a b` | embed a plain function |
| `lower` / `↓` | `Hyper a b -> a -> b` | observe with constant continuation |
| `base` / `○` | `a -> Hyper b a` | ignore feedback, return constant |
| `push` / `⊲` | `(b -> c) -> Hyper a b -> Hyper a c` | prepend function to output |
| `runHyper` / `⥁` | `Hyper a a -> a` | tie the self-referential knot |

```haskell
-- >>> lower (lift (+ 1)) 5
-- 6

-- >>> lower (base 42) undefined
-- 42

-- >>> lower (push (+ 1) (lift (* 2))) 5
-- 6

-- >>> runHyper (Hyper $ \_ -> (42 :: Int))
-- 42
```

`runHyper` is `invoke h (Hyper runHyper)` — the hyperfunction is fed its own dual.
`lift` is `push f (lift f)` — infinite coinductive unrolling that works
because each layer unwraps on demand.

---

## the Either gap

`Traced Hyper (,)` exists.  `Traced Hyper Either` does not.  The reason is
in how each tensor's loop resolves:

| tensor | loop mechanism | fits Hyper? |
|--------|---------------|-------------|
| `(,)` | lazy knot — output and feedback co-occur | yes — `invoke`'s continuation is a single knot |
| `Either` | iteration — `Left` re-enters, `Right` exits | no — needs multiple re-entry with state threading |

Hyper's continuation model is one-shot: `invoke h k` asks `k` exactly once,
and `k` produces a value.  An Either loop needs to re-enter the body
multiple times with different `Left` values, each time asking the
continuation anew.  That requires either explicit state threading (which
Hyper's type doesn't expose) or delimited continuations (which are
Kleisli's domain, not Hyper's).

So `encodeEither` and `runEither` exist as separate combinators rather
than a `Traced` instance.  They encode the Either state machine into Hyper's
function domain — the state `Either a b` becomes an explicit argument
passed through `invoke`:

```haskell
encodeEither :: (Either a b -> Either a c)
             -> Hyper (Either a b -> c) (Either a b -> c)
encodeEither f = h
  where
    h = Hyper (\k s ->
      case f s of
        Right c -> c
        Left a  -> invoke k h (Left a))
```

`runEither f b = runHyper (encodeEither f) (Right b)` ties the knot and
injects the initial state.  The Either loop lives *inside* Hyper's
function argument rather than being eliminated to a plain function.

```haskell
-- >>> runEither (\case Right n | n < 3 -> Left (n + 1); Right n -> Right n; Left n | n < 3 -> Left (n + 1); Left n -> Right n) (0 :: Int)
-- 3
```

---

## the encoding triangle

`encode` maps `Trace` into `Hyper`.  The triangle identity says observing
after encoding gives the same result as running `Trace` directly:

```
lower (encode t)  =  run t
```

```haskell
-- >>> lower (encode (Arr (+ 1))) 5
-- 6
-- >>> run (Arr (+ 1) :: Trace (,) (->) Int Int) 5
-- 6

-- >>> let t = Arr (+ 1) . Arr (* 2) :: Trace (,) (->) Int Int
-- >>> lower (encode t) 5
-- 11
-- >>> run t 5
-- 11

-- >>> let k = Knot (\(xs, ()) -> (0 : xs, take 3 xs)) :: Trace (,) (->) () [Int]
-- >>> lower (encode k) ()
-- [0,0,0]
-- >>> run k ()
-- [0,0,0]
```

The `Knot` case is where the triangle earns its keep.  `encode (Knot f)`
uses Hyper's own `Traced Hyper (,)` instance — a coinductive lazy knot.  The
sliding axiom guarantees `lower (encode (Knot f)) = trace f`.

Compare `encode` vs `run` on `Knot f . g`:

```
-- encode: composition threads the continuation structurally
encode (Knot f . g)
  = encode (Knot f) . encode g              -- Hyper Category composition
  = trace (lift f) . encode g               -- Hyper's Traced (,) knot
  -- No Mendler case needed.

-- run: the Category instance has already fused g into the body
run (Knot f . g)
  = trace (f . untrace (run g))    -- g routed through the feedback channel
```

Hyper composition doesn't need a Mendler case because every `Category`
composition threads the continuation through `g . h` before `f` sees it.
The sliding axiom is structural, not enforced by pattern matching.

---

## instances

`Hyper` carries the standard coinductive instances:

| class | key method | notes |
|-------|-----------|-------|
| `Category` | `f . g = Hyper $ \h -> invoke f (g . h)` | continuation threads through composition |
| `Profunctor` | `dimap f g h = Hyper $ g . invoke h . dimap g f` | coinductive — calls itself |
| `Functor` | `fmap = rmap` | from Profunctor |

`Hyper` does not provide `Applicative` or `Monad` instances.  These
would require observing via `lower` on every step, collapsing the
continuation structure back to plain functions.

The `Profunctor` instance is coinductive: `dimap` calls itself.  Under
lazy evaluation, any finite observation (via `lower` or `runHyper`) only
unfolds finitely many layers, never reaching bottom.

```haskell
-- >>> lower (dimap words unwords (lift (map reverse))) "hello world"
-- "olleh dlrow"
```

---

## what Hyper cannot do

Hyper's continuation barrier limits what can be built directly:

| capability | Trace | Hyper |
|-----------|---------|-------|
| `first` / thread a pair | yes — pattern-match constructors | no — continuation grabs everything |
| fanout / `(&&&)` | yes — lower both branches | no — can't route one input to two places |
| Kleisli arrows / effects | yes — parametric in `arr` | no — `invoke` returns `b`, not `m b` |
| inspect structure | yes — GADT constructors | no — opaque |

The pattern: **build in `Trace`, encode to `Hyper`** when you want the
final encoding.  `encode` preserves observable behaviour, so `Trace`'s
expressive power flows through to Hyper's structural guarantees.

---

## Trace ↔ Hyper

| aspect | Trace | Hyper |
|--------|---------|-------|
| encoding | initial (syntax) | final (semantics) |
| feedback | explicit `Knot` | structural in type |
| sliding | handled by the `Category` instance | inherent in `(.)` |
| degeneration possible? | no — already in normal form | no |
| elimination | `run` | `lower` |
| map to other | `encode` (→ Hyper) | `flatten` (→ Trace) |
| inspection | constructors visible | opaque |
| composition cost | O(1) (normal form) | O(1) amortised |
| Either loops | `Traced (->) Either` | `encodeEither` / `runEither` |
| Kleisli | parametric in `arr` | pure only |

The two encodings are not isomorphic on the nose.  `lower . encode = run`
holds, but `encode . flatten ≠ id` — flattening a Hyper to `Trace`
observes it against a constant continuation, losing all feedback
structure.  `flatten h = Arr (lower h)` is the forgetful map, not an
inverse.
