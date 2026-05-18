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

-- $setup
-- >>> import Prelude hiding (id, (.))
-- >>> import Control.Arrow (Kleisli (..), first, second)
-- >>> import Control.Category ((.))
-- >>> import Data.Either (fromRight)
-- >>> import Circuit.Symbols
--
-- Circuit axioms:
--
-- >>> let f = (+1)
-- >>> let g = (*2)
-- >>> (↘) ((↑) f ⊙ (↑) g :: Circuit (->) (,) Int Int) 5
-- 11
--
-- Traced axioms:
--
-- Vanishing:
-- >>> let h x = x + 1
-- >>> (↪) ((↩) h :: ((), Int) -> ((), Int)) 5
-- 6
--
-- Yanking:
-- >>> let swap (x, y) = (y, x)
-- >>> (↪) swap 42
-- 42
--
-- Tightening:
-- >>> let h (x, a) = (x, a)
-- >>> (↪) (second (+1) . h . second (*2)) 5
-- 11
--
-- Sliding:
-- >>> let swap (x, y) = (y, x)
-- >>> (↪) (second (+1) . swap) 5
-- 6
-- >>> (↪) (swap . second (+1)) 5
-- 6
--
-- Strength:
-- >>> let h (x, c) = (x, c + 1)
-- >>> let g (x, (a, c)) = (x', (a * 2, d)) where (x', d) = h (x, c)
-- >>> (↪) g (3, 5)
-- (6,6)
--
-- Hyper axioms:
--
-- >>> (↓) ((⇨) ((↑) (+1) :: Circuit (->) (,) Int Int)) 5
-- 6
-- >>> (↓) ((○) 42) undefined
-- 42
-- >>> let ask = Hyper (\k -> (⇸) k ((○) 0) + 1)
-- >>> (⇸) ask ((○) 42)
-- 43
--
-- Either iteration:
-- >>> let fac (n, acc) = if n <= 1 then Right acc else Left (n - 1, n * acc)
-- >>> (↪) (either fac fac) (5, 1 :: Int)
-- 120

-- Circuit.Circuit ----------------------------------------------------------

infixr 9 ↑

-- | Embed a plain arrow into a 'Circuit'.  Symbol alias for 'Lift'.
--
-- @
--   a ──[ f ]──▶ b
-- @
--
-- >>> (↘) ((↑) (+1) :: Circuit (->) (,) Int Int) 5
-- 6
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
(⊙) :: (Category cat) => cat b c -> cat a b -> cat a c
(⊙) = (.)

infixr 9 ⊙

-- >>> (↘) ((↑) (+1) ⊙ (↑) (*2) :: Circuit (->) (,) Int Int) 5
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
-- Symbol alias for 'Circuit.Circuit.push'.
--
-- @
--   a ──[ c ]──▶ ──[ f ]──▶ b
-- @
--
-- >>> (↘) ((+1) ⊲ (↑) (*2) :: Circuit (->) (,) Int Int) 5
-- 11
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
--
-- >>> let braid (x, (s, a)) = (s, (x, a))
-- >>> (↘) ((∥) braid ((↑) (+1) :: Circuit (->) (,) Int Int)) ("st", 5)
-- ("st",6)
-- >>> let step (xs, ()) = (0 : xs, take 3 xs)
-- >>> (↘) ((∥) braid ((↮) step)) ("st", ())
-- ("st",[0,0,0])
(∥) ::
  (Profunctor arr, Trace arr t) =>
  (forall x y z. t x (t y z) -> t y (t x z)) ->
  Circuit arr t a b ->
  Circuit arr t (t s a) (t s b)
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
--
-- >>> let ask = Hyper (\k -> (⇸) k ((○) 0) + 1)
-- >>> (⇸) ask ((○) 42)
-- 43
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
--
-- >>> (↓) (lift (+1)) 5
-- 6
-- >>> (↓) (lift reverse) "hello"
-- "olleh"
-- >>> (↓) ((○) 42) undefined
-- 42
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
--
-- >>> (⥁) (Hyper $ \_ -> 42 :: Int)
-- 42
-- >>> (⥁) (Hyper $ \h -> (⇸) h ((○) 0) + 1) :: Int
-- 1
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
--
-- >>> (↓) ((⇨) ((↑) (+1) :: Circuit (->) (,) Int Int)) 5
-- 6
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
--
-- >>> let h = lift (+ 1)
-- >>> (↘) ((⇦) h) 5
-- 6
-- >>> (↓) ((⇨) ((⇦) h)) 5
-- 6
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
--
-- >>> let powers (ns, ()) = (1 : map (*2) ns, take 5 ns)
-- >>> (↪) powers () :: [Integer]
-- [1,2,4,8,16]
--
-- >>> let f (x, a) = (x, a + 1)
-- >>> (↪) f 5
-- 6
--
-- >>> let swap (x, y) = (y, x)
-- >>> (↪) swap 42
-- 42
--
-- >>> let f (x, a) = (x, a)
-- >>> (↪) (second (+1) . f . second (*2)) 5
-- 11
--
-- >>> let swap (x, y) = (y, x)
-- >>> (↪) (second (+1) . swap) 5
-- 6
-- >>> (↪) (swap . second (+1)) 5
-- 6
--
-- >>> let f (x, c) = (x, c + 1)
-- >>> let g (x, (a, c)) = (x', (a * 2, d)) where (x', d) = f (x, c)
-- >>> (↪) g (3, 5)
-- (6,6)
--
-- >>> let fac (n, acc) = if n <= 1 then Right acc else Left (n - 1, n * acc)
-- >>> (↪) (either fac fac) (5, 1 :: Int)
-- 120
--
-- >>> let f = Right . (+1) . fromRight undefined
-- >>> (↪) f 5
-- 6
--
-- >>> let swapEither = \case Left x -> Right x; Right x -> Left x
-- >>> (↪) swapEither 42
-- 42
--
-- >>> let f = fmap ((+1) :: Int -> Int) . fmap ((*2) :: Int -> Int)
-- >>> (↪) (f :: Either () Int -> Either () Int) 5
-- 11
--
-- >>> let fibs = Kleisli $ \(fibs, ()) -> pure (0 : 1 : zipWith (+) fibs (drop 1 fibs), take 3 fibs)
-- >>> runKleisli ((↪) fibs) ()
-- [0,1,1]
--
-- >>> let exit42 = Kleisli $ \case Right () -> pure (Right (42 :: Int))
-- >>> runKleisli ((↪) exit42) ()
-- 42
(↪) :: (Trace arr t) => arr (t a b) (t a c) -> arr b c
(↪) = trace

infixr 9 ↩

-- | Open the feedback loop.  Lifts a plain morphism into the tensor,
-- passing the channel unchanged.  Symbol alias for 'untrace'.
--
-- @
--   b ──[ f ]──▶ c    ──↩──▶    (a,b) ──[ f ]──▶ (a,c)
-- @
--
-- >>> let f x = x + 1
-- >>> (↪) ((↩) f :: ((), Int) -> ((), Int)) 5
-- 6
(↩) :: (Trace arr t) => arr b c -> arr (t a b) (t a c)
(↩) = untrace
