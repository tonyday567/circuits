-- | Unicode symbol aliases for the circuits library.
--
-- This module consolidates all unicode operator aliases in one place.
-- The canonical API uses lowercase names (@reify@, @run@, @lift@, etc.);
-- the symbols here are syntactic sugar.  On compilers that do not support
-- unicode operators (e.g. MicroHs), this module is simply excluded.
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
-- forward    (↣)      Circuit         left-to-right composition
-- lower      (↓)      Hyper           observe hyperfunction
-- base       (○)      Hyper           constant continuation
-- push       (⊲)      Circuit/Hyper   prepend function
-- run        (⥁)      Hyper           tie self-referential knot
-- encode     (⇨)      Hyper           Circuit → Hyper
-- invoke     (⇸)      Hyper           apply continuation
-- flatten    (⇦)      Hyper           Hyper → Circuit (lossy)
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
    (↣),
    (⊲),
    (⊙),
    (↮),
    (↑),

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
import Prelude hiding ((.))

-- Circuit.Circuit ----------------------------------------------------------

infixr 9 ↑
-- | Embed a plain arrow. Symbol alias for 'Lift'.
(↑) :: arr a b -> Circuit arr t a b
(↑) = Lift

infixr 9 ↮
-- | Tie a feedback loop. Symbol alias for 'Knot'.
(↮) :: arr (t a b) (t a c) -> Circuit arr t b c
(↮) = Knot

-- | Sequential composition. Works for both 'Circuit' and 'Hyper' via their
-- 'Category' instances. Symbol alias for '(.)'.
(⊙) :: Category cat => cat b c -> cat a b -> cat a c
(⊙) = (.)
infixr 9 ⊙

-- >>> reify ((Lift (+1) :: Circuit (->) (,) Int Int) `Compose` Lift (*2)) 5
-- 11

infixl 9 ↘
-- | Collapse a 'Circuit' to a plain arrow. Symbol alias for 'reify'.
(↘) :: (Category arr, Trace arr t) => Circuit arr t x y -> arr x y
(↘) = reify

infixr 8 ⊲
-- | Push a plain function onto a 'Circuit'. Symbol alias for 'push'.
(⊲) :: arr b c -> Circuit arr t a b -> Circuit arr t a c
(⊲) = C.push

infixl 9 ↣
-- | Left-to-right sequential composition.  Symbol alias for '(>>>)'.
(↣) :: Circuit arr t a b -> Circuit arr t b c -> Circuit arr t a c
f ↣ g = Compose g f

-- Circuit.Hyper ------------------------------------------------------------

-- | Type synonym for 'Hyper'.
type (↬) = Hyper

infixr 0 ⇸
-- | Invoke a hyperfunction with a continuation. Symbol alias for 'invoke'.
(⇸) :: Hyper a b -> Hyper b a -> b
(⇸) = invoke

infixl 9 ↓
-- | Observe a hyperfunction. Symbol alias for 'lower'.
(↓) :: Hyper a b -> (a -> b)
(↓) = lower

-- | Self-referential knot.  Symbol alias for 'run'.
(⥁) :: Hyper a a -> a
(⥁) = run

infixl 9 ○
-- | Constant continuation. Symbol alias for 'base'.
(○) :: a -> Hyper b a
(○) = base

infixr 9 ⇨
-- | Encode a 'Circuit' into a 'Hyper'. Symbol alias for 'encode'.
(⇨) :: Circuit (->) (,) a b -> Hyper a b
(⇨) = encode

infixr 9 ⇦
-- | Flatten a 'Hyper' to a 'Circuit' (lossy). Symbol alias for 'flatten'.
(⇦) :: Hyper a b -> Circuit (->) (,) a b
(⇦) = flatten

-- Circuit.Traced -----------------------------------------------------------

infixr 9 ↪
-- | Close the feedback loop. Symbol alias for 'trace'.
(↪) :: (Trace arr t) => arr (t a b) (t a c) -> arr b c
(↪) = trace

infixr 9 ↩
-- | Open the feedback loop. Symbol alias for 'untrace'.
(↩) :: (Trace arr t) => arr b c -> arr (t a b) (t a c)
(↩) = untrace
