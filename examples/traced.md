# Trace — reading the feedback boundary

`Trace` is a two-method class: `trace` closes a feedback loop, `untrace`
opens one.  The tensor (`(,)` or `Either`) chooses what "feedback" means.
This card walks through the structure: the bracket pattern in `trace`,
the uniformity of `untrace`, and what changes between pure and effectful
arrows.

```haskell
-- $setup
-- >>> import Control.Arrow (Kleisli(..), right)
-- >>> import Circuit.Traced
-- >>> import Prelude hiding (id, (.))
```

---

## trace — the bracket

For `Either`, every `trace` instance has the same shape:

```
trace f  =  enter   >>>   f   >>>   exit
```

| stage | pure `(->)` | `Kleisli IO` |
|-------|-------------|--------------|
| enter | `Right` | `Right` |
| exit | `id` | `pure` |
| loop mechanism | tail recursion | `prompt` / `control0` |

The loop mechanism is what differs.  The pure instance tail-calls.
The Kleisli instance allocates a `PromptTag`, places a `prompt` boundary,
and uses `control0` on `Left` to capture the continuation and re-enter —
constant stack space regardless of iteration count.

```haskell
-- >>> trace (\case Right n | n < 3 -> Left (n + 1); _ -> Right ()) (0 :: Int)
-- ()

-- >>> let step n = if n < 3 then Left (n + 1) else Right n in trace (either step step) (0 :: Int)
-- 3
```

```haskell
-- >>> runKleisli (trace (Kleisli $ \case Right () -> pure (Right (42 :: Int)))) ()
-- 42
```

### tensor conventions

| branch | `Trace (->) Either` | user-facing `Step s r` |
|--------|---------------------|------------------------|
| `Left` | feedback — iterate again | result — done |
| `Right` | output — done | continue — next state |

The convention is fixed by the `Trace` class.  User code with the opposite
convention (like `while.md`'s `Step s r`) bridges the gap with a swap
function.  The convention itself is arbitrary — what matters is that the
class picks one and sticks with it.

---

## untrace — lift the arrow through the tensor

`untrace` opens the loop: it takes an arrow on the output channel and
threads the tensor through, preserving the feedback channel untouched.

```
untrace f  =  id ⊗ f
```

For product: `id *** f` = `second f`.
For coproduct: `id +++ f` = `right f`.

| instance | `untrace` | formulation |
|----------|-----------|-------------|
| `Trace (->) (,)` | `fmap` | `second` on a pure arrow |
| `Trace (->) Either` | `fmap` | `right` on a pure arrow |
| `Trace (Kleisli IO) Either` | hand-written `\case` | `right` on an effectful arrow |

The pure cases collapse to `fmap` because `Functor (,) a` and
`Functor (Either a)` both map the second argument.  The Kleisli case
cannot use `fmap` — the arrow is effectful — but the shape is the same:
pass `Left` through with `pure`, map the arrow over `Right`.

In `Bitraversable` terms, the Kleisli `untrace` is `bitraverse pure f`:
traverse the output channel, pass the feedback channel through unchanged.

```haskell
-- >>> untrace (+ 1) (Right 4 :: Either Int Int)
-- Right 5
-- >>> untrace (+ 1) (Left 3 :: Either Int Int)
-- Left 3
```

```haskell
-- >>> runKleisli (untrace (Kleisli (\x -> pure (show x)))) (Right (42 :: Int))
-- Right "42"
-- >>> runKleisli (untrace (Kleisli (\x -> pure (show x)))) (Left (7 :: Int))
-- Left 7
```

The hand-written form and `right` from ArrowChoice produce the same
results.  `right` pays an `arr` tax — two extra `pure` wrappers from
`arr mirror` — but the semantics are identical.  The hand-written version
in `Circuit.Traced` avoids that allocation.

---

## the round-trip identity

Opening a loop and immediately closing it gives back the original arrow:

```
trace (untrace f)  =  f
```

In every instance the loop runs zero iterations — `untrace` places the
arrow on the output channel (wrapping with `Right` or `second`), `trace`
enters and exits immediately because the feedback channel is untouched.

```haskell
-- >>> trace ((untrace (+ 1)) :: Either Int Int -> Either Int Int) (4 :: Int)
-- 5

-- >>> trace ((untrace (+ (1 :: Int))) :: (Int, Int) -> (Int, Int)) (4 :: Int)
-- 5

-- >>> runKleisli (trace ((untrace (Kleisli (pure . show))) :: Kleisli IO (Either Int Int) (Either Int String))) (42 :: Int)
-- "42"
```

The identity holds regardless of tensor.  For `(,)` the lazy knot binds
`a` but `second f` never touches it — `(a, f b)` produces `(a, f b)`
and `trace` returns `f b`.  For `Either` the while-loop runs once:
`Right b` → `fmap f` → `Right (f b)` → exit.  For Kleisli the same
structure with `IO` threading.

This is also the sanity check that `untrace` isn't doing anything
surprising — it just threads the tensor through.  If `trace (untrace f) /= f`,
one of the two methods is wrong.

---

## design notes

- **`untrace` is uniform.** Every instance says the same thing: push the
  arrow through the output channel, preserve the feedback channel.  The
  difference between `fmap`, `right`, and `bitraverse pure` is how much
  functor structure the arrow carries — pure, `ArrowChoice`, or monadic.

- **`trace` is where the instances diverge.** The bracket is the same,
  but the loop mechanism changes.  Tail recursion for pure; delimited
  continuations for Kleisli.  The ceremony (`newPromptTag`, `prompt`) is
  per-bracket by design — each `trace` call seals its own delimited
  scope.

- **`Trace` has no `Arrow` superclass.** The instances spell out what
  `ArrowChoice` would provide, which keeps the dependency footprint
  minimal.  The structural intent (`untrace` is `right`) lives in
  comments and this card rather than in the class hierarchy.
