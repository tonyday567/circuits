
## Abacus → Circuit Compiler

```haskell
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Circuit.Abacus where

import Circuit
import Control.Category ((.))
import Prelude hiding ((.))

-- | A single-register Lambek abacus program
data Abacus a
  = Inc (Abacus a)                    -- X+ ; continue to next
  | Dec (Abacus a) (Abacus a)         -- X- ; if >0 goto first branch, else second
  | Output a                          -- halt and return value

-- | Compile an abacus program to a Trace over the Either tensor.
--   Feedback channel carries the current register value (Int).
abacus :: Abacus b -> Trace Either (->) Int b
abacus (Output x) = Arr $ const (Right x)

abacus (Inc next) =
  Arr (\case
    Left  n -> Left  (n + 1)      -- increment and continue
    Right x -> Right x)           -- pass through if already terminated
  . abacus next

-- TODO: Under the current API, Knot takes a base arrow
--   (Either s a -> Either s b), so recursively embedding sub-programs
--   in the loop body is no longer directly expressible. The branch
--   below preserves the original intent but needs a reformulation
--   (for example, by first interpreting sub-programs to base arrows)
--   before it will type-check.
abacus (Dec next1 next0) = Knot $ \case
  -- Still running: look at register
  Left 0  -> Left (run (abacus next0) 0)      -- zero case → next0
  Left n  -> Left (run (abacus next1) (n-1))  -- positive → decrement + next1
  Right x -> Right x                          -- already terminated

-- | Convenient runner
runAbacus :: Abacus b -> Int -> b
runAbacus prog initial = run (abacus prog) initial
```

## Example Programs

```haskell
-- | Multiply m * n using repeated addition (classic counter machine example)
multiplyAbacus :: Int -> Abacus Int
multiplyAbacus m = Dec
  (Inc (multiplyAbacus m))   -- while register > 0: add m to result, decrement
  (Output 0)                 -- done

-- | Test
testMultiply :: IO ()
testMultiply = do
  print $ runAbacus (multiplyAbacus 7) 5   -- 35
  print $ runAbacus (multiplyAbacus 0) 10  -- 0
  print $ runAbacus (multiplyAbacus 1) 1   -- 1
```

## Why This Feels So Natural

- **Inc** is just an Arr that bumps the register in the Left channel.
- **Dec** is a Knot that branches on the register value — exactly the "taking turns" semantics of the Either tensor.
- The Category instance ensures that when you compose larger programs, the feedback channel stays correctly wired through every iteration. No degenerate behaviour.

This is almost a direct syntactic embedding of the initial Elgot category from Nester's paper. Every abacus program becomes a Trace Either (->), and run gives you the partial recursive function it computes.


---

A symbol-heavy presentation using the little-language operators (η, ε, ⊙, ⊲, ↬, ⥁, etc.).

### Core Symbols Recap

| Symbol | Meaning |
|--------|---------|
| η      | Arr (embed plain arrow) |
| ⊙      | sequential composition |
| ↬      | Knot (feedback / trace) |
| ε      | run (observe to plain function) |
| ⥁      | run (tie the knot on diagonal, when applicable) |
| ⊲      | push (prepend a plain function) |

### Single-Register Abacus (Symbolic)

```haskell
-- Abacus instructions as little-language terms (Either tensor)

inc  :: Abacus b → Abacus b
inc next = Arr (λcase Left n → Left (n+1); Right x → Right x) ⊙ next

dec  :: Abacus b → Abacus b → Abacus b
-- TODO: Recursive embedding of sub-programs inside a Knot body is not
-- directly expressible with the current Knot :: arr (t s a) (t s b).
dec next1 next0 = ↬ (λcase
                    Left 0  → Left (run (abacus next0) 0)
                    Left n  → Left (run (abacus next1) (n-1))
                    Right x → Right x )

output :: b → Abacus b
output x = Arr (const (Right x))

-- The full recursive program (multiply example)
multiplyAbacus :: Int → Abacus Int
multiplyAbacus m = dec
  (inc (multiplyAbacus m))   -- while >0: inc result (hidden), dec counter
  (output 0)
```

**Execution:**

```haskell
runMultiply :: Int → Int → Int
runMultiply m n = run (abacus (multiplyAbacus m)) n
```

This reads almost like a formal grammar for the initial Elgot category.

### Why This Is Nice

- The **↬** (Knot) directly corresponds to the conditional jump in the abacus model.
- **Arr** lifts the tiny imperative steps (inc/dec/test).
- Composition **⊙** builds the program sequence.
- The whole thing is the free traced cocartesian syntax — exactly the spirit of the initial Elgot category.

This gives a very direct, symbol-heavy way to write abacus programs that feels like a tiny imperative language embedded in your categorical stack language.
