# Hyper — the final encoding

`Hyper` is the coinductive / final encoding.  Where `Circuit` makes
feedback explicit with a `Knot` constructor, `Hyper` dissolves the
feedback channel into the type itself.  Every `Hyper a b` already
carries a continuation `Hyper b a` — the feedback is structural.

```haskell
-- $setup
-- >>> import Data.Profunctor (dimap)
-- >>> import Circuit.Hyper
-- >>> import Circuit.Circuit (Circuit(..), reify)
-- >>> import Circuit.Traced (Trace(..))
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
| `run` / `⥁` | `Hyper a a -> a` | tie the self-referential knot |

```haskell
-- >>> lower (lift (+ 1)) 5
-- 6

-- >>> lower (base 42) undefined
-- 42

-- >>> lower (push (+ 1) (lift (* 2))) 5
-- 6

-- >>> run (Hyper $ \_ -> (42 :: Int))
-- 42
```

`run` is `invoke h (Hyper run)` — the hyperfunction is fed its own dual.
`lift` is `push f (lift f)` — infinite coinductive unrolling that works
because each layer unwraps on demand.

---

## the Either gap

`Trace Hyper (,)` exists.  `Trace Hyper Either` does not.  The reason is
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
than a `Trace` instance.  They encode the Either state machine into Hyper's
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

`runEither f b = run (encodeEither f) (Right b)` ties the knot and
injects the initial state.  The Either loop lives *inside* Hyper's
function argument rather than being eliminated to a plain function.

```haskell
-- >>> runEither (\case Right n | n < 3 -> Left (n + 1); Right n -> Right n; Left n | n < 3 -> Left (n + 1); Left n -> Right n) (0 :: Int)
-- 3
```

---

## the encoding triangle

`encode` maps Circuit into Hyper.  The triangle identity says observing
after encoding gives the same result as running Circuit directly:

```
lower (encode c)  =  reify c
```

```haskell
-- >>> lower (encode (Lift (+ 1))) 5
-- 6
-- >>> reify (Lift (+ 1) :: Circuit (->) (,) Int Int) 5
-- 6

-- >>> let c = Compose (Lift (+ 1)) (Lift (* 2)) :: Circuit (->) (,) Int Int
-- >>> lower (encode c) 5
-- 11
-- >>> reify c 5
-- 11

-- >>> let k = Knot (\(xs, ()) -> (0 : xs, take 3 xs)) :: Circuit (->) (,) () [Int]
-- >>> lower (encode k) ()
-- [0,0,0]
-- >>> reify k ()
-- [0,0,0]
```

The `Knot` case is where the triangle earns its keep.  `encode (Knot f)`
uses Hyper's own `Trace (,)` instance — a coinductive lazy knot.  The
sliding axiom guarantees `lower (encode (Knot f)) = trace f`.

Compare `encode` vs `reify` on a `Compose (Knot f) g`:

```
-- encode: composition threads the continuation structurally
encode (Compose (Knot f) g)
  = encode (Knot f) . encode g              -- general Compose case
  = trace (lift f) . encode g               -- Hyper's Trace (,) knot
  -- No Mendler case needed.

-- reify: must inject g into the feedback channel
reify (Compose (Knot f) g)
  = trace (f . untrace (reify g))  -- explicit Mendler case
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
lazy evaluation, any finite observation (via `lower` or `run`) only
unfolds finitely many layers, never reaching bottom.

```haskell
-- >>> lower (dimap words unwords (lift (map reverse))) "hello world"
-- "olleh dlrow"
```

---

## what Hyper cannot do

Hyper's continuation barrier limits what can be built directly:

| capability | Circuit | Hyper |
|-----------|---------|-------|
| `first` / thread a pair | yes — pattern-match constructors | no — continuation grabs everything |
| fanout / `(&&&)` | yes — lower both branches | no — can't route one input to two places |
| Kleisli arrows / effects | yes — parametric in `arr` | no — `invoke` returns `b`, not `m b` |
| inspect structure | yes — GADT constructors | no — opaque |

The pattern: **build in Circuit, encode to Hyper** when you want the
final encoding.  `encode` preserves observable behaviour, so Circuit's
expressive power flows through to Hyper's structural guarantees.

---

## Circuit ↔ Hyper

| aspect | Circuit | Hyper |
|--------|---------|-------|
| encoding | initial (syntax) | final (semantics) |
| feedback | explicit `Knot` | structural in type |
| sliding | Mendler case | inherent in `(.)` |
| degeneration possible? | yes (without Mendler) | no |
| elimination | `reify` | `lower` |
| map to other | `encode` (→ Hyper) | `flatten` (→ Circuit) |
| inspection | constructors visible | opaque |
| composition cost | O(n²) left-nested | O(1) amortised |
| Either loops | `Trace (->) Either` | `encodeEither` / `runEither` |
| Kleisli | parametric in `arr` | pure only |

The two encodings are not isomorphic on the nose.  `lower . encode = reify`
holds, but `encode . flatten ≠ id` — flattening a Hyper to Circuit
observes it against a constant continuation, losing all feedback
structure.  `flatten h = Lift (lower h)` is the forgetful map, not an
inverse.
