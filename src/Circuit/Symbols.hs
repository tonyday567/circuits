-- | Unicode symbol aliases for the circuits library.
--
-- This module consolidates all unicode operator aliases in one place.
-- The canonical API uses lowercase names (@reify@, @run@, @lift@, etc.);
-- the symbols here are syntactic sugar.  On compilers that do not support
-- unicode operators (e.g. MicroHs), this module is simply excluded.
--
-- === string diagrams
--
-- Each operator below includes a string diagram showing data flow.
-- Boxes @[ f ]@ are morphisms; wires @──▶@ carry values left to right;
-- feedback loops @┌──┐@ route output back to input.  The diagrams make
-- the traced monoidal category structure visible without leaving the
-- source file.
--
-- === operator cheatsheet
--
-- @
-- name       symbol   home module     meaning
-- ──────────────────────────────────────────────────
-- lift       (↑)      Circuit         embed a plain arrow
-- compose    (⊙)      Circuit/Hyper   sequential composition
-- knot       (↮)      Circuit         feedback loop constructor
-- reify      (↘)      Circuit         interpret to plain arrow
-- push       (⊲)      Circuit/Hyper   prepend function
-- lower      (↓)      Hyper           observe hyperfunction
-- base       (○)      Hyper           constant continuation
-- run        (⥁)      Hyper           tie self-referential knot
-- encode     (⇨)      Hyper           Circuit → Hyper
-- invoke     (⇸)      Hyper           apply continuation
-- flatten    (⇦)      Hyper           Hyper → Circuit (lossy)
-- ambient    (∥)      Circuit         thread state wire alongside
-- trace      (↪)      Traced          close feedback loop
-- untrace    (↩)      Traced          open feedback loop
-- type (↬)            Hyper           type synonym for Hyper
-- @
module Circuit.Symbols
  ( -- * Re-exports
    module Circuit.Circuit,
    module Circuit.Hyper,
    module Circuit.Traced,

    -- * Symbol aliases — Circuit
    (↘),
    (⊲),
    (⊙),
    (↮),
    (↑),
    (∥),

    -- * Symbol aliases — Hyper
    (⇸),
    (↓),
    (⥁),
    (○),
    (⇨),
    (⇦),
    type (↬),

    -- * Symbol aliases — Traced
    (↪),
    (↩),
  )
where

import Circuit.Circuit hiding (push)
import Circuit.Circuit qualified as C
import Circuit.Hyper
import Circuit.Traced
import Control.Category (Category, (.))
import Data.Profunctor (Profunctor)
import Prelude hiding ((.))

-- Circuit.Circuit ----------------------------------------------------------

infixr 9 ↑
-- | Embed a plain arrow into a 'Circuit'.  Symbol alias for 'Lift'.
--
-- @
--   a ──[ f ]──▶ b
-- @
(↑) :: arr a b -> Circuit arr t a b
(↑) = Lift

infixr 9 ↮
-- | Tie a feedback loop.  Symbol alias for 'Knot'.
--
-- @
--       ┌───────────┐
--       │     f     │
--       │  ┌───┐    │
--   b ──┤  │   ├───▶ c
--       │  └─┬─┘    │
--       │    │ t a  │
--       └────┼──────┘
--            └── feedback
-- @
(↮) :: arr (t a b) (t a c) -> Circuit arr t b c
(↮) = Knot

-- | Sequential composition.  Works for both 'Circuit' and 'Hyper' via their
-- 'Category' instances.  Symbol alias for '(.)'.
--
-- @
--   a ──[ g ]──▶ ──[ f ]──▶ c
-- @
(⊙) :: Category cat => cat b c -> cat a b -> cat a c
(⊙) = (.)
infixr 9 ⊙

-- >>> reify ((Lift (+1) :: Circuit (->) (,) Int Int) `Compose` Lift (*2)) 5
-- 11

infixl 9 ↘
-- | Collapse a 'Circuit' to a plain arrow.
-- This is the unique traced functor from the initial encoding.
-- Symbol alias for 'reify'.
--
-- @
--   Circuit ──↘──▶ arr
-- @
(↘) :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
(↘) = reify

infixr 8 ⊲
-- | Push a plain function onto the end of a 'Circuit'.
-- Symbol alias for 'push'.
--
-- @
--   a ──[ c ]──▶ ──[ f ]──▶ b
-- @
(⊲) :: arr b c -> Circuit arr t a b -> Circuit arr t a c
(⊲) = C.push

infixl 5 ∥
-- | Thread a state wire alongside a circuit.
-- The state @s@ rides ambient through the computation — present but untouched,
-- sliding past feedback loops via braiding.
-- Symbol alias for 'ambient'.
--
-- A state wire enters from above and exits below, sliding past the
-- computation which flows left-to-right.  For 'Lift', the state tags
-- along via 'untrace'.  For 'Compose', the state threads through both
-- stages.  For 'Knot', the state slides past the feedback loop — the
-- sliding axiom made explicit.
--
-- @
--              s
--              │
--              ▼
--        ┌─────────────┐
--        │  ┌───────┐  │
--   a ───┤  │   c   │  ├─── b
--        │  └───┬───┘  │
--        │      │      │
--        └──────┼──────┘
--               │
--               ▼
--               s
--
--  For a Knot, the braid swaps state past feedback:
--
--        ┌─────────────────┐
--        │    ┌───────┐    │
--   a ───┤    │  c    │    ├─── b
--        │    └───┬───┘    │
--        │        │ t x    │
--   s ───┤  braid ├─────── ├─── s
--        │        │        │
--        └─────────────────┘
-- @
(∥) :: (Profunctor arr, Trace arr t)
    => (forall x y z. t x (t y z) -> t y (t x z))
    -> Circuit arr t a b
    -> Circuit arr t (t s a) (t s b)
(∥) = ambient

-- Circuit.Hyper ------------------------------------------------------------

-- | Type synonym for 'Hyper'.
type (↬) = Hyper

infixr 0 ⇸
-- | Invoke a hyperfunction with a continuation.
-- The continuation @Hyper b a@ feeds back into @Hyper a b@,
-- and the result @b@ emerges.
-- Symbol alias for 'invoke'.
--
-- @
--   Hyper a b ──[⇸]──▶ Hyper b a ──▶ b
-- @
(⇸) :: Hyper a b -> Hyper b a -> b
(⇸) = invoke

infixl 9 ↓
-- | Observe a hyperfunction by supplying a constant continuation.
-- The feedback channel is severed; what remains is a plain function.
-- Symbol alias for 'lower'.
--
-- @
--   ┌──────────────┐
--   │  h           │
--   │    ┌────┐    │
--   a───▶│const│───▶ b
--        └────┘
--   constant continuation
-- @
(↓) :: Hyper a b -> (a -> b)
(↓) = lower

-- | Self-referential knot.  Runs a hyperfunction by feeding its own
-- dual back as the continuation: @run h = invoke h (Hyper run)@.
-- Symbol alias for 'run'.
--
-- @
--   ┌──────────────────────┐
--   │  h ∷ Hyper a a       │
--   │       │              │
--   │  invoke(h, Hyper ⥁)  │──▶ a
--   │                      │
--   └──────────────────────┘
-- @
(⥁) :: Hyper a a -> a
(⥁) = run

infixl 9 ○
-- | Constant continuation.  Ignores the feedback channel and returns
-- a fixed value.  For any continuation @k@, @base a \`invoke\` k == a@.
-- Symbol alias for 'base'.
--
-- @
--   b ──[○ a]──▶ a     (ignores b)
-- @
(○) :: a -> Hyper b a
(○) = base

infixr 9 ⇨
-- | Encode a 'Circuit' into a 'Hyper'.
-- This is the unique traced functor from the initial to the final encoding,
-- satisfying the commuting triangle: @lower . encode = reify@.
-- Symbol alias for 'encode'.
--
-- @
--                ⇨
--   Circuit ──────────▶ Hyper
--       │                 │
--       │                 │
--       ↘                 ↓
--       └────── arr ──────┘
-- @
(⇨) :: Circuit (->) (,) a b -> Hyper a b
(⇨) = encode

infixr 9 ⇦
-- | Flatten a 'Hyper' to a 'Circuit' by observation.
-- All feedback structure is lost; only the observable behaviour remains.
-- Symbol alias for 'flatten'.
--
-- @
--   Hyper ──[⇦]──▶ Circuit     (forgetful)
-- @
(⇦) :: Hyper a b -> Circuit (->) (,) a b
(⇦) = flatten

-- Circuit.Traced -----------------------------------------------------------

infixr 9 ↪
-- | Close the feedback loop.  Symbol alias for 'trace'.
--
-- For the @(,)@ tensor — lazy knot (output and feedback produced simultaneously):
--
-- @
--       ┌───────────────┐
--       │       f       │
--       │   ┌─────┐     │
--   b ──┤   │(a,c)│────▶ c
--       │   └──┬──┘     │
--       │      │(a,b)   │
--       └──────┼────────┘
--              └─ lazy knot
-- @
--
-- For the @Either@ tensor — iteration (@Left@ feeds back, @Right@ exits):
--
-- @
--       ┌──────────────┐
--       │      f       │
--       │  ┌─────┐     │
--   b ──┤  │     ├────▶ c
--       │  └──┬──┘     │
--       │     │Left a  │
--       └─────┼────────┘
--             └─ loop
-- @
(↪) :: (Trace arr t) => arr (t a b) (t a c) -> arr b c
(↪) = trace

infixr 9 ↩
-- | Open the feedback loop.  Lifts a plain morphism into the tensor,
-- passing the channel unchanged.  Symbol alias for 'untrace'.
--
-- @
--   b ──[ f ]──▶ c    ──↩──▶    (a,b) ──[ f ]──▶ (a,c)
-- @
(↩) :: (Trace arr t) => arr b c -> arr (t a b) (t a c)
(↩) = untrace
