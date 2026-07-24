# Gem: the block-swap bug in `FinRel` bialgebra tests

## What we were doing

Adding `Circuit.FinRel` — finite-dimensional linear relations over GF(2) — as a
semantic base category for signal-flow graphs.  One of the oracle tests checks
the bialgebra law:

```
copy . plus  ==  par plus plus . swapMiddle . par copy copy
```

The left-hand side takes two inputs, adds them, then copies the result.  The
right-hand side first copies each input, then swaps the two middle bundles so
that the two `plus` gates receive matching pairs.

## What went wrong

We wrote the rearrangement as a swap of *individual wires*:

```haskell
swapMiddle2 :: FinRel F ((N2, N2), (N2, N2)) ((N2, N2), (N2, N2))
swapMiddle2 = wiring perm
  where
    perm 2 = 4
    perm 4 = 2
    perm i = i
```

For `N2` the object has two wires, so `((N2,N2),(N2,N2))` has four blocks and
therefore eight wires.  Swapping only wires 2 and 4 leaves wire 3 in place and
fails to move the whole third block.  The correct move is a **block-wise**
swap: block 1 (wires 2–3) exchanges places with block 2 (wires 4–5), while
blocks 0 and 3 stay fixed.

## Why the n=1 test passed

For `N1` each block is exactly one wire, so "swap the two middle blocks" and
"swap the two middle wires" are the same operation.  The degenerate case
masked the real shape of the permutation.

## The fix

Replace the wire-level permutation with a block-level one:

```haskell
swapBlocks ::
  forall n.
  (KnownNat n) =>
  FinRel F ((FinObj n, FinObj n), (FinObj n, FinObj n))
           ((FinObj n, FinObj n), (FinObj n, FinObj n))
swapBlocks = wiring perm
  where
    n = fromIntegral (natVal (Proxy @n))
    perm i
      | i < n     = i          -- block 0: pass through
      | i < 2*n   = i + n      -- block 1: move to block 2's slot
      | i < 3*n   = i - n      -- block 2: move to block 1's slot
      | otherwise = i          -- block 3: pass through
```

Now `swapMiddle = swapBlocks @1` and `swapMiddle2 = swapBlocks @2` are both
correct, and the n=2 bialgebra test passes.

## Why this kind of bug sneaks through testing

1. **n=1 is too degenerate.** Many tensor-structure checks collapse to the
   same operation when every block has size one.  It is the obvious first test
   to write, but it does not exercise the block structure.

2. **The name lied.** We called the helper `swapMiddle` and described it as
   "swap the second and third wires."  In a setting where a "wire" is actually
   an `n`-dimensional block, that wording is ambiguous.  Once we renamed it to
   `swapBlocks` the intended semantics became obvious and the bug became
   obvious.

3. **Permutation helpers are easy to eyeball incorrectly.** A one-line
   `wiring perm` looks too simple to be wrong, so it does not get the same
   scrutiny as the matrix-algebra core.  The hard part (RREF, nullspace,
   composition) was correct; the easy part (which wire goes where) was wrong.

## Take-away

When testing laws on a monoidal category whose objects have internal dimension,
always include the smallest **non-degenerate** case — usually `n=2`.  And name
permutation helpers in terms of the **blocks** they move, not the raw wires.
