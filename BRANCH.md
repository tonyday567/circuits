Design spike: remove Knot from Net, drop the t parameter, rename Sym->SMC and
Thread->Body.

Decisions:
- `Net` is now `Net w arr a b` — no feedback tensor `t`, no `Knot`
  constructor. It is the free symmetric monoidal category with a bimonoid
  over the wiring tensor `w` only.
- `enrich` (Loop -> Net) is removed. With no `Knot` in Net there is no
  canonical embedding of traced feedback into inspectable wiring. Feedback
  stays in `Loop`; wiring inspection stays in `Net`.
- `melt` becomes `Net w arr a b -> Loop t arr a b`. It no longer ties any
  knot inside Net; it only rewrites bimonoid rows into `Loop.Lift`. It still
  needs `Traced t arr` because `Loop`'s `Tensor`/`Category` instances need
  strength/trace to host the parallel composition that `Par` melts to.
- `Circuit.Fragment.AlgNet` drops `SigKnot`. `SigKnot` remains in `AlgLoop`
  where it belongs. `AlgNet` is now the free SMC-with-bimonoid signature.
- `Sym` is renamed to `SMC`, moved to its own module `Circuit.SMC`.
- `Thread` is renamed to `Body`, module `Circuit.Thread` -> `Circuit.Body`.

Design note:
Both `Net` and `SMC` are now wiring-only composites with a very similar bind
shape (sequential + monoidal rows). A possible next step is a more layered
encoding — e.g. `NetX (Loop (SMC a b))` or similar — where `Net` is built by
layering bimonoid rows over an already-traced or already-monoidal core. This
spike does not pursue that; it only clears the ground by removing the traced
payload from Net.
