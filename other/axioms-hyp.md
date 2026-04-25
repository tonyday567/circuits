# Hyperfunction Axioms

Modern presentation aligned with the `Circuit` / `Hyper` library.

## Core Definitions (Kidney–Wu style)

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }

lift :: (a -> b) -> Hyper a b
push :: (a -> b) -> Hyper a b -> Hyper a b
compose :: Hyper b c -> Hyper a b -> Hyper a c   (infix (.) or #)
run :: Hyper a a -> a
lower :: Hyper a b -> (a -> b)
```

### Key Operations

- **lift** embeds a plain function, defined recursively: `lift f = push f (lift f)`
- **push** prepends a function to the continuation stack
- **compose** threads continuations backwards
- **run** ties the knot on the diagonal
- **lower** observes a hyperfunction by supplying a constant continuation

## The Axioms (LKS restated for clarity)

After substitution and simplification the essential content reduces to:

1. **Free category** (associativity, identity, functoriality of lift)
2. **Adjunction unit**: `lower . lift = id`
3. **Sliding / feedback** (the crucial axiom that forces `Loop`):

   Restated cleanly in terms of `lower`:

   ```haskell
   lower (compose (push f p) q) = f . lower (compose q p)
   ```

   Or in symbols:

   ```
   ε ((f ⊲ p) ⊙ q) = f . ε (q ⊙ p)
   ```

   This is exactly the sliding axiom of traced monoidal categories.

## Circuit as the Free Traced Encoding

The axioms determine the following GADT:

```haskell
data Circuit arr t a b where
  Lift    :: arr a b -> Circuit arr t a b
  Compose :: Circuit arr t b c -> Circuit arr t a b -> Circuit arr t a c
  Loop    :: arr (t a b) (t a c) -> Circuit arr t b c
```

`lower` (the interpretation) is defined by structural recursion with one Mendler case:

```haskell
lower (Lift f)                  = f
lower (Compose (Loop f) g)      = trace (f . untrace (lower g))
lower (Compose f g)             = lower f . lower g
lower (Loop k)                  = trace k
```

### Why the three constructors?

- **Lift + Compose** give the free category on the base arrow.
- **Loop** is required to satisfy the sliding axiom. Without the Mendler case the structure collapses to the free category (degenerate model).
- The **Trace class** supplies `trace` / `untrace` for a chosen tensor `t` (`(,)` or `Either`).

## Hyper as the Final Encoding

```haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }

toHyper :: Circuit (->) t a b -> Hyper a b
lower   :: Hyper a b -> (a -> b)
```

The triangle holds:

```
lower . toHyper = lower   (on Circuit)
```

Hyper bakes the feedback channel into the type itself, so sliding is structural rather than enforced by pattern matching.

## Adjunction lift ⊣ lower

**Unit**: `lower . lift = id` (derivable from the axioms)

**Counit**: `lift . lower = id` holds in the concrete stream model but is not forced by the axioms in general.

The unit is the fundamental direction: every hyperfunction can be observed by eliminating it to a plain function, then re-embedding that function via lift recovers the hyperfunction's behaviour.
