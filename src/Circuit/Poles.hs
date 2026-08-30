{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Free channel poles over a base arrow, plus concrete box helpers.
--
-- A channel has exactly two poles:
--
--   * @Out@ — the companion (read / emit pole), covariant in the payload.
--   * @In@  — the conjoint (write / commit pole), contravariant in the payload.
--
-- @Poles@ is the record that pairs one @In@ with one @Out@.  The poles are
-- defined purely in terms of the base arrow @arr@.
--
-- 'open' produces a matched pair; 'close' plugs the pair back together by
-- feeding the @Out@ into the @In@.
--
-- A /symmetric/ pole @Poles arr a a@ with @close (conjoint p) (companion p) = id@
-- is the copycat strategy for the multiplicative excluded middle @A ⅋ A⊥@:
-- it routes traffic between the two poles without ever deciding which side is
-- true.  For the unit object use 'open' (also exported as 'copycat').
--
-- == Relationship to 'Circuit.Moore'
--
-- @Poles@ is the bi-polar / effectful API: it is the right tool for
-- @K IO/STM@ process plumbing where the channel is a write pole paired
-- with a read pole.  For pure @(->)@ Moore-style machines indexed by a
-- polynomial, prefer 'Circuit.Moore'.
module Circuit.Poles
  ( -- * Channel poles (bi-polar contract)
    Out (..),
    In (..),

    -- * Matched pair
    Poles (..),

    -- * Counit
    close,

    -- * Generalised polar plug
    plug,

    -- * Prefixing an action to an @In@
    prefixIn,

    -- * Suffixing an action to an @Out@
    suffixOut,

    -- * Companion / conjoint of a tight arrow
    companionTight,
    conjointTight,

    -- * Build a @Poles@ from primitive actions
    poles,
    poles0,
    polesK,

    -- * Extract primitive actions from a @Poles@
    splay,
    splay0,

    -- * Sequential composition
    compose,
    compose0,
    (>:>),

    -- * Parallel composition
    polesTensor,

    -- * Morphism-level mapping
    iomap,
    imap,
    omap,

    -- * Dualising object / unit poles (requires constant morphisms)
    HasDual (..),

    -- * Copycat / multiplicative excluded middle
    copycat,

    -- * Boxes
    box,
    boxAsymmetric,

    -- * Additive connectives
    pair,
    race,
  )
where

import Circuit.Bimonoid (Copy (copy))
import Circuit.Category (Category (..), FunctionLike (..), K (..), (.>))
import Circuit.Tensor (Bias (..), Tensor, Unit)
import Circuit.Tensor qualified as Tensor
import Circuit.Traced (Assoc (..), Slide (..), Strength (..))
import Data.Bifunctor (bimap)
import Data.Kind (Type)
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Category ((.>))
-- >>> import Circuit.Poles
-- >>> import Circuit.Tensor (Bias (..))
-- >>> import Circuit.Syntax (eval)
-- >>> import Circuit.Category (K(..), runK)
-- >>> import Data.Maybe (isNothing)

-- * Channel poles — the companion and conjoint of the identity functor.

-- | @Out@ is the companion of the identity functor.  Covariant in @a@
-- (sits in the output position).
newtype Out arr a = Out
  { -- | Emit through the companion, supplying the other pole.
    emit :: forall x. In arr x -> arr x a
  }

-- | @In@ is the conjoint of the identity functor.  Contravariant in
-- @a@ (sits in the input position).
newtype In arr a = In
  { -- | Commit through the conjoint, supplying the other pole.
    commit :: forall x. Out arr x -> arr a x
  }

-- | A matched pair of channel poles: one @In@ and one @Out@.
--
-- This is the bi-polar communication contract.  The conjoint (@In@)
-- consumes payloads of type @a@; the companion (@Out@) produces payloads
-- of type @b@.  For symmetric channels such as queues @a = b@.
--
-- Together with 'prefixIn' and 'suffixOut', @Poles@ carries an /enriched/
-- profunctor structure over the base category @arr@: 'prefixIn' is the
-- left action of @arr@ on @In@ poles, and 'suffixOut' is the right action
-- of @arr@ on @Out@ poles.
data Poles arr a b = Poles
  { -- | Write pole (producer), the conjoint.
    conjoint :: In arr a,
    -- | Read pole  (consumer), the companion.
    companion :: Out arr b
  }

-- | Plug an @In@ and an @Out@ of the same payload type together.
--
-- 'close' feeds the @Out@ into the @In@ pole, producing a morphism
-- @arr a a@ from the paired payload type.
--
-- Yanking: for the unit poles from 'open',
-- @close (conjoint p) (companion p) = id@.

{- HLINT ignore close "Eta reduce" -}
close :: In arr a -> Out arr a -> arr a a
close contra = commit contra

-- | Generalised polar plug.
--
-- 'plug' feeds an @Out arr b@ into an @In arr a@, producing a morphism
-- @arr a b@.  It is the counit of the polar pairing without the same-type
-- restriction of 'close'.  Every @In@ pole is already a polymorphic consumer
-- of @Out@ poles, so this is just the underlying 'commit' exposed.
--
-- >>> let polesU = open :: Poles (->) () ()
-- >>> let outA = suffixOut (companion polesU) (const 42) :: Out (->) Int
-- >>> let inA = prefixIn (const ()) (conjoint polesU) :: In (->) String
-- >>> plug inA outA "hello"
-- 42

{- HLINT ignore plug "Eta reduce" -}
plug :: In arr a -> Out arr b -> arr a b
plug i o = commit i o

-- | Precompose an @arr@-morphism with an @In@ pole.
--
-- Given @f :: arr a b@ and an @In@ pole at type @b@, produce an @In@ pole
-- at type @a@.  Running the resulting pole first executes @f@ and then
-- commits through the original pole.
--
-- This is the left (contravariant) action of the base category on @In@
-- poles.  Specialised to unit poles it is the canonical way to build
-- effectful write poles.
--
-- >>> let polesU = open :: Poles (->) () ()
-- >>> let inA = prefixIn (const ()) (conjoint polesU) :: In (->) Int
-- >>> commit inA (companion polesU) 42
-- ()
prefixIn :: forall arr a b. (Category arr) => arr a b -> In arr b -> In arr a
prefixIn f i = In $ \(o :: Out arr x) -> f .> commit i o

-- | Postcompose an @arr@-morphism with an @Out@ pole.
--
-- Given an @Out@ pole at type @a@ and @g :: arr a b@, produce an @Out@
-- pole at type @b@.  Running the resulting pole first emits through the
-- original pole and then executes @g@ on the emitted value.
--
-- This is the right (covariant) action of the base category on @Out@
-- poles.  Specialised to unit poles it is the canonical way to build
-- effectful read poles.
--
-- >>> let polesU = open :: Poles (->) () ()
-- >>> let outA = suffixOut (companion polesU) (const 42) :: Out (->) Int
-- >>> emit outA (conjoint polesU) ()
-- 42
suffixOut :: forall arr a b. (Category arr) => Out arr a -> arr a b -> Out arr b
suffixOut o g = Out $ \(i :: In arr x) -> emit o i .> g

-- * Companion / conjoint of a tight arrow

-- | The companion of a tight arrow incident to the dualising object.
--
-- A morphism @f :: arr bot b@ from the dualising object is postcomposed with
-- the unit companion, yielding an @Out arr b@.  This is the equipment-theoretic
-- companion restricted to unit-incident arrows; the same construction works for
-- any arrow with a dualising object.
--
-- >>> let polesU = open :: Poles (->) () ()
-- >>> let outInc = companionTight (const 42 :: () -> Int) :: Out (->) Int
-- >>> emit outInc (conjoint polesU) ()
-- 42
companionTight ::
  forall arr b bot.
  (HasDual bot arr) =>
  arr bot b ->
  Out arr b
companionTight = suffixOut (companion (open :: Poles arr bot bot))

-- | The conjoint of a tight arrow incident to the dualising object.
--
-- A morphism @f :: arr a bot@ to the dualising object is precomposed with the
-- unit conjoint, yielding an @In arr a@.
--
-- >>> let polesU = open :: Poles (->) () ()
-- >>> let inInc = conjointTight (const () :: Int -> ()) :: In (->) Int
-- >>> commit inInc (companion polesU) 7
-- ()
conjointTight ::
  forall arr a bot.
  (HasDual bot arr) =>
  arr a bot ->
  In arr a
conjointTight f = prefixIn f (conjoint (open :: Poles arr bot bot))

-- * Dualising object / unit poles

-- | Arrows that have channel poles for a given dualising object @bot@.
--
-- The dualising object is the target of the polar pairing and the object
-- through which the two poles of a 'Poles' are plugged together.  In the
-- cartesian case it is the monoidal unit @()@; for halt-mark / delivery
-- pairings it can be 'Bool'.
--
-- The poles are the identity-on-@bot@ morphism split into its two polar
-- halves.  The companion is constant; the conjoint delegates to the
-- opposing companion.
--
-- These poles require the base arrow to support constant morphisms, so
-- they are captured by this class rather than being definable for all
-- arrows.
class (Category arr) => HasDual bot arr where
  -- | The dualising object as channel poles.
  --
  -- === Yank
  --
  -- >>> let poles = open :: Poles (->) () ()
  -- >>> close (conjoint poles) (companion poles) ()
  -- ()
  --
  -- === Plug
  --
  -- >>> let polesA = open :: Poles (->) () ()
  -- >>> let polesU = open :: Poles (->) () ()
  -- >>> commit (conjoint polesA) (companion polesU) ()
  -- ()
  -- >>> emit (companion polesA) (conjoint polesU) ()
  -- ()
  open :: Poles arr bot bot

-- | The copycat strategy at the dualising object @bot@.
--
-- This is the multiplicative excluded middle @bot ⅋ bot⊥@ for arrows that
-- have poles at @bot@: a self-dual channel whose 'close' is the identity on
-- @bot@.  It routes between the two poles without ever deciding which one
-- holds.
--
-- The additive excluded middle @bot ⊕ bot⊥@ — a verdict, now — is /not/
-- supported; there is no @decide :: Either bot bot@ here, because only the
-- routing witness is provable.
copycat :: forall arr bot. (HasDual bot arr) => Poles arr bot bot
copycat = open
{-# INLINE copycat #-}

-- | Build a @Poles@ from a write morphism and a read morphism.
--
-- @write :: arr a bot@ consumes the input payload and produces the dualising
-- object; @read :: arr bot b@ consumes the dualising object and produces the
-- output payload.  The dualising-object poles wire the two halves together.
--
-- This is the canonical way to turn a pair of primitive channel actions
-- into a matched pair of @In@ and @Out@ poles.
--
-- Compositional spelling:
--
-- @
-- poles write receive =
--   Poles (prefixIn write (conjoint open)) (suffixOut (companion open) receive)
-- @
poles ::
  forall arr a b bot.
  (HasDual bot arr) =>
  arr a bot ->
  arr bot b ->
  Poles arr a b
poles write receive =
  Poles
    (prefixIn write (conjoint open))
    (suffixOut (companion open) receive)

-- | Convenience version of 'poles' when the dualising object is @()@.
poles0 ::
  (HasDual () arr) =>
  arr a () ->
  arr () b ->
  Poles arr a b
poles0 = poles @_ @_ @_ @()
{-# INLINE poles0 #-}

-- | Specialization of 'poles' for @K@ actions.
--
-- @write :: a -> m ()@ consumes the input payload; @receive :: m b@
-- produces the output payload. The dualising-object handling is hidden
-- inside the @K@ wrappers.
polesK ::
  forall m a b.
  (Monad m) =>
  (a -> m ()) ->
  m b ->
  Poles (K m) a b
polesK write receive = poles (K write) (K $ const receive)

-- | Extract the primitive write and read actions from a @Poles@ by
-- plugging each pole with the dualising-object poles.
--
-- For a @Poles@ built with 'poles', this recovers the original
-- @write :: arr a bot@ and @receive :: arr bot b@.
--
-- >>> let p = poles0 (\() -> ()) (const (42 :: Int)) :: Poles (->) () Int
-- >>> let (write, receive) = splay0 p
-- >>> (write (), receive ())
-- ((),42)
splay ::
  forall arr a b bot.
  (HasDual bot arr) =>
  Poles arr a b ->
  (arr a bot, arr bot b)
splay p =
  ( commit (conjoint p) (companion (open :: Poles arr bot bot)),
    emit (companion p) (conjoint (open :: Poles arr bot bot))
  )

-- | Convenience version of 'splay' when the dualising object is @()@.
splay0 ::
  (HasDual () arr) =>
  Poles arr a b ->
  (arr a (), arr () b)
splay0 = splay @_ @_ @_ @()
{-# INLINE splay0 #-}

-- * Composition

-- | Sequential composition of @Poles@.
--
-- Given @p1 :: Poles arr a b@ and @p2 :: Poles arr b c@, produce an
-- @Poles arr a c@ by connecting the @b@ pole of @p1@ to the @b@ pole of
-- @p2@.  The primitive actions are extracted via 'splay' and reassembled
-- with 'poles', so 'box' preserves the composition:
--
-- @box (compose p1 p2) = box p2 . box p1@
--
-- Identity exists at the chosen unit type: @open :: Poles arr u u@ is
-- the identity for composition.
--
-- >>> let p1 = poles0 (const ()) (const 1 :: () -> Int) :: Poles (->) () Int
-- >>> let p2 = poles0 (const ()) (const 2 :: () -> Int) :: Poles (->) Int Int
-- >>> box @() (compose0 p1 p2) ()
-- 2
--
-- 'open' at the dualising object is the identity for composition:
--
-- >>> let r = poles @(->) @Bool @Bool @Bool not not
-- >>> box @Bool (compose @_ @_ @_ @_ @Bool (open :: Poles (->) Bool Bool) r) True
-- True
compose ::
  forall arr a b c bot.
  (HasDual bot arr) =>
  Poles arr a b ->
  Poles arr b c ->
  Poles arr a c
compose p1 p2 =
  let (write1, read1) = splay p1 :: (arr a bot, arr bot b)
      (write2, read2) = splay p2 :: (arr b bot, arr bot c)
   in poles write1 (read1 .> write2 .> read2)

-- | Convenience version of 'compose' when the dualising object is @()@.
compose0 ::
  (HasDual () arr) =>
  Poles arr a b ->
  Poles arr b c ->
  Poles arr a c
compose0 = compose @_ @_ @_ @_ @()
{-# INLINE compose0 #-}

-- | Forward-composition operator for @Poles@.  @p1 >:> p2 = compose p1 p2@.
(>:>) ::
  forall arr a b c bot.
  (HasDual bot arr) =>
  Poles arr a b ->
  Poles arr b c ->
  Poles arr a c
p1 >:> p2 = compose @arr @a @b @c @bot p1 p2

infixr 1 >:>

-- | Parallel composition of @Poles@.
--
-- Pair two @Poles@ side by side on the tensor @t@.  The primitive
-- actions are tensored and then collapsed to and from the dualising object
-- with the tensor unitors.  This requires the tensor unit to coincide with
-- the dualising object @bot@; in practice this is the cartesian @(,)@ tensor
-- with @bot = ()@.
--
-- >>> let p1 = poles0 (const ()) (const 1 :: () -> Int) :: Poles (->) () Int
-- >>> let p2 = poles0 (const ()) (const 2 :: () -> Int) :: Poles (->) () Int
-- >>> box @() (polesTensor p1 p2) ((), ())
-- (1,2)
polesTensor ::
  forall t arr a b c d bot.
  (Tensor t arr, HasDual bot arr, Unit t ~ bot) =>
  Poles arr a b ->
  Poles arr c d ->
  Poles arr (t a c) (t b d)
polesTensor p1 p2 =
  let (write1, read1) = splay p1 :: (arr a bot, arr bot b)
      (write2, read2) = splay p2 :: (arr c bot, arr bot d)
      write = Tensor.unitr . Tensor.tensor write1 write2
      readPoles = Tensor.tensor read1 read2 . Tensor.unitl'
   in poles write readPoles

-- | Precompose the input and postcompose the output of a @Poles@.
--
-- This is the morphism-level profunctor action: @f :: arr a' a@ shapes
-- what the conjoint sees, and @g :: arr b b'@ shapes what the companion
-- emits.
--
-- >>> let p = poles0 (const ()) (const 42 :: () -> Int) :: Poles (->) () Int
-- >>> let p' = iomap (const ()) ((+1) :: Int -> Int) p :: Poles (->) () Int
-- >>> box @() p' ()
-- 43
iomap ::
  forall arr a a' b b'.
  (Category arr) =>
  arr a' a ->
  arr b b' ->
  Poles arr a b ->
  Poles arr a' b'
iomap f g (Poles i o) = Poles (prefixIn f i) (suffixOut o g)

-- | Precompose the input of a @Poles@.
imap ::
  forall arr a a' b.
  (Category arr) =>
  arr a' a ->
  Poles arr a b ->
  Poles arr a' b
imap f (Poles i o) = Poles (prefixIn f i) o

-- | Postcompose the output of a @Poles@.
omap ::
  forall arr a b b'.
  (Category arr) =>
  arr b b' ->
  Poles arr a b ->
  Poles arr a b'
omap g (Poles i o) = Poles i (suffixOut o g)

-- | Dualising object @()@ for @(->)@.
--
-- The companion is the constant function returning @()@; the conjoint
-- recursively emits through the supplied companion.
instance HasDual () (->) where
  open = Poles inU outU
    where
      outU = Out $ \_ -> const ()
      inU = In $ \o -> emit o inU

-- | Dualising object @()@ for @K@ @m@.
--
-- Same shape as the @(->)@ instance, but the constant companion returns
-- @()@ in the monad.
instance (Monad m) => HasDual () (K m) where
  open = Poles inU outU
    where
      outU = Out $ \_ -> K $ \_ -> pure ()
      inU = In $ \o -> emit o inU

-- $dualising-object
--
-- The class parameter @bot@ is the object through which the two poles of a
-- 'Poles' are plugged.  For the cartesian @(,)@ tensor this is the monoidal
-- unit @()@, which is terminal.  'copycat' yanks to the identity on @bot@
-- exactly when @bot@ is terminal; for non-terminal objects such as 'Bool'
-- the same 'open' still typechecks but 'copycat' becomes a constant
-- endomorphism rather than the identity.  The 'Bool' instances below make
-- that plumbing explicit.

-- | Dualising object 'Bool' for @(->)@.
--
-- The companion is the constant function returning 'False'; the conjoint
-- recursively emits through the supplied companion.  Because 'Bool' is not
-- terminal, 'copycat' at 'Bool' is the constant function, not the identity.
instance HasDual Bool (->) where
  open = Poles inU outU
    where
      outU = Out $ \_ -> const False
      inU = In $ \o -> emit o inU

-- | Dualising object 'Bool' for @K@ @m@.
--
-- Same shape as the @(->)@ instance, but the constant companion returns
-- 'False' in the monad.
instance (Monad m) => HasDual Bool (K m) where
  open = Poles inU outU
    where
      outU = Out $ \_ -> K $ \_ -> pure False
      inU = In $ \o -> emit o inU

-- | Close a @Poles@ to a plain base-arrow morphism.
--
-- A matched pair of free poles (@Poles@) is a box with one input wire and
-- one output wire.  This helper embeds that box into a traced monoidal
-- category by unit-plugging the remaining two slots, giving a plain
-- @arr a b@: input on the left, output on the right, with the unit plumbing
-- hidden.
--
-- >>> let p = poles0 (const ()) (const 42) :: Poles (->) () Int
-- >>> box @() p ()
-- 42
box ::
  forall bot arr a b.
  (HasDual bot arr) =>
  Poles arr a b ->
  arr a b
box p =
  commit (conjoint p) (companion (open :: Poles arr bot bot))
    .> emit (companion p) (conjoint (open :: Poles arr bot bot))

-- | Asymmetric box with the dualising object exposed on opposite sides.
--
-- Uses 'Circuit.Tensor.tensor' at the base arrow level. The input carries the dualising object
-- on the right and the output carries it on the left; most users will prefer
-- the dualising-object-normalised 'box'.
--
-- >>> let p = poles0 (const ()) (const 42) :: Poles (->) () Int
-- >>> boxAsymmetric @() p ((), ())
-- ((),42)
boxAsymmetric ::
  forall bot t arr a b.
  (HasDual bot arr, Tensor t arr) =>
  Poles arr a b ->
  arr (t a bot) (t bot b)
boxAsymmetric p =
  Tensor.tensor
    (commit (conjoint p) (companion open))
    (emit (companion p) (conjoint open))

-- * Additive connectives

-- $setup
-- >>> import Circuit.Poles
-- >>> import Circuit.Layer (run)
-- >>> import Data.Maybe (isNothing)

-- | Additive conjunction: both sub-poles receive the same input and their
-- outputs are paired.
--
-- This is the @&@ connective / @await@ fragment: every branch sees the
-- input, and the composite emits all of their results.
--
-- >>> let p1 = poles0 (const ()) (const 1 :: () -> Int) :: Poles (->) () Int
-- >>> let p2 = poles0 (const ()) (const 2 :: () -> Int) :: Poles (->) () Int
-- >>> box @() (pair p1 p2) ()
-- (1,2)
pair ::
  forall arr a b c.
  (HasDual () arr, Tensor (,) arr, Copy arr a) =>
  Poles arr a b ->
  Poles arr a c ->
  Poles arr a (b, c)
pair p1 p2 =
  let (w1, r1) = splay0 p1
      (w2, r2) = splay0 p2
      w = Tensor.unitr . Tensor.tensor w1 w2 . copy
      r = Tensor.tensor r1 r2 . Tensor.unitl'
   in poles0 w r

-- | Additive disjunction / race: both sub-poles receive the same input, but
-- only the first output satisfying the predicate is emitted.
--
-- The predicate selects "silent" values that should be skipped. The bias
-- chooses which side to prefer when both are non-silent. The picking logic is
-- lifted into the base arrow via 'FunctionLike'.
--
-- >>> let eL = poles0 (const ()) (const (Just 1)) :: Poles (->) () (Maybe Int)
-- >>> let eR = poles0 (const ()) (const (Just 2)) :: Poles (->) () (Maybe Int)
-- >>> box @() (race isNothing LeftFirst eL eR) ()
-- Just 1
-- >>> box @() (race isNothing RightFirst eL eR) ()
-- Just 2
race ::
  forall arr a b.
  (HasDual () arr, Tensor (,) arr, Copy arr a, FunctionLike arr) =>
  (b -> Bool) ->
  Bias ->
  Poles arr a b ->
  Poles arr a b ->
  Poles arr a b
race isSilent bias p1 p2 = omap (function (pick bias)) (pair p1 p2)
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y
