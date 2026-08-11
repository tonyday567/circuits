{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Free channel ends over a base arrow, plus concrete box helpers.
--
-- A channel has exactly two ends:
--
--   * @Out@ — the companion (read / emit end), covariant in the payload.
--   * @In@  — the conjoint (write / commit end), contravariant in the payload.
--
-- @Ends@ is the record that pairs one @In@ with one @Out@.  The ends are
-- defined purely in terms of the base arrow @arr@.
--
-- 'open' produces a matched pair; 'close' plugs the pair back together by
-- feeding the @Out@ into the @In@.
--
-- A /symmetric/ end @Ends arr a a@ with @close (conjoint e) (companion e) = id@
-- is the copycat strategy for the multiplicative excluded middle @A ⅋ A⊥@:
-- it routes traffic between the two poles without ever deciding which side is
-- true.  For the unit object use 'open' (also exported as 'copycat').
--
-- == Relationship to 'Circuit.ChannelPoly'
--
-- @Ends@ is the bi-polar / effectful API: it is the right tool for
-- @Kleisli IO/STM@ process plumbing where the channel is a write end paired
-- with a read end.  For pure @(->)@ Moore-style channels indexed by a
-- polynomial, prefer 'Circuit.ChannelPoly.Channel'.
--
-- There is no deprecation shim yet: the relationship between the bi-polar
-- and polynomial views is still being settled.  This module stays unchanged
-- until 'Channel' gains 'Kleisli' evaluation or an equivalent effectful
-- story.
--
-- Effectful queue-based constructors ('openSTM', 'openIO') live in
-- @Circuit.Agent.Ends@ so that the core library does not depend on @stm@.
module Circuit.Ends
  ( -- * Channel ends (bi-polar contract)
    Out (..),
    In (..),

    -- * Matched pair
    Ends (..),

    -- * Counit
    close,

    -- * Prefixing an action to an @In@
    prefixIn,

    -- * Suffixing an action to an @Out@
    suffixOut,

    -- * Build an @Ends@ from primitive actions
    ends,
    ends0,
    endsK,

    -- * Extract primitive actions from an @Ends@
    splay,
    splay0,

    -- * Sequential composition
    composeEnds,
    composeEnds0,
    (>:>),

    -- * Parallel composition
    parEnds,

    -- * Profunctor structure (morphism-level)
    dimapEnds,
    lmapEnds,
    rmapEnds,

    -- * Unit ends (requires constant morphisms)
    HasUnit (..),

    -- * Copycat / multiplicative excluded middle
    copycat,

    -- * Boxes
    box,
    boxAsymmetric,

    -- * Additive connectives
    pairEnds,
    Bias (..),
    IsSilent (..),
    HasSilent (..),
    raceEnds,
    raceMediator,
  )
where

import Circuit.Category (Category (..), Discrete (..), (.>))
import Circuit.Dagger (CopyDiscard (..))
import Circuit.Loop (Loop (..))
import Circuit.Mediate (Mediator (..))
import Circuit.Tensor (Tensor (..), Unit)
import Control.Arrow (Kleisli (..))
import Data.Maybe (isNothing)
import Data.Void (Void)
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Category ((.>))
-- >>> import Circuit.Ends
-- >>> import Circuit.Layer (run)
-- >>> import Control.Arrow (Kleisli(..), runKleisli)

-- ---------------------------------------------------------------------------
-- Channel ends — the companion and conjoint of the identity functor.
-- ---------------------------------------------------------------------------

-- | @Out@ is the companion of the identity functor.  Covariant in @a@
-- (sits in the output position).
newtype Out arr a = Out
  { -- | Emit through the companion, supplying the other end.
    emit :: forall x. In arr x -> arr x a
  }

-- | @In@ is the conjoint of the identity functor.  Contravariant in
-- @a@ (sits in the input position).
newtype In arr a = In
  { -- | Commit through the conjoint, supplying the other end.
    commit :: forall x. Out arr x -> arr a x
  }

-- | A matched pair of channel ends: one @In@ and one @Out@.
--
-- This is the bi-polar communication contract.  The conjoint (@In@)
-- consumes payloads of type @a@; the companion (@Out@) produces payloads
-- of type @b@.  For symmetric channels such as queues @a = b@.
--
-- Together with 'prefixIn' and 'suffixOut', @Ends@ carries an /enriched/
-- profunctor structure over the base category @arr@: 'prefixIn' is the
-- left action of @arr@ on @In@ ends, and 'suffixOut' is the right action
-- of @arr@ on @Out@ ends.
data Ends arr a b = Ends
  { -- | Write end (producer), the conjoint.
    conjoint :: In arr a,
    -- | Read end  (consumer), the companion.
    companion :: Out arr b
  }

-- | Plug an @In@ and an @Out@ of the same payload type together.
--
-- 'close' feeds the @Out@ into the @In@ end, producing a morphism
-- @arr a a@ from the paired payload type.
--
-- Yanking: for the unit ends from 'open',
-- @close (conjoint ends) (companion ends) = id@.
close :: In arr a -> Out arr a -> arr a a
close contra = commit contra

-- | Precompose an @arr@-morphism with an @In@ end.
--
-- Given @f :: arr a b@ and an @In@ end at type @b@, produce an @In@ end
-- at type @a@.  Running the resulting end first executes @f@ and then
-- commits through the original end.
--
-- This is the left (contravariant) action of the base category on @In@
-- ends.  Specialised to unit ends it is the canonical way to build
-- effectful write ends.
--
-- >>> let endsU = open :: Ends (->) () ()
-- >>> let inA = prefixIn (const ()) (conjoint endsU) :: In (->) Int
-- >>> commit inA (companion endsU) 42
-- ()
prefixIn :: forall arr a b. (Discrete arr) => arr a b -> In arr b -> In arr a
prefixIn f i = In $ \(o :: Out arr x) -> withOb @arr @a $ withOb @arr @b $ withOb @arr @x $ f .> commit i o

-- | Postcompose an @arr@-morphism with an @Out@ end.
--
-- Given an @Out@ end at type @a@ and @g :: arr a b@, produce an @Out@
-- end at type @b@.  Running the resulting end first emits through the
-- original end and then executes @g@ on the emitted value.
--
-- This is the right (covariant) action of the base category on @Out@
-- ends.  Specialised to unit ends it is the canonical way to build
-- effectful read ends.
--
-- >>> let endsU = open :: Ends (->) () ()
-- >>> let outA = suffixOut (companion endsU) (const 42) :: Out (->) Int
-- >>> emit outA (conjoint endsU) ()
-- 42
suffixOut :: forall arr a b. (Discrete arr) => Out arr a -> arr a b -> Out arr b
suffixOut o g = Out $ \(i :: In arr x) -> withOb @arr @x $ withOb @arr @a $ withOb @arr @b $ emit o i .> g

-- ---------------------------------------------------------------------------
-- Unit ends
-- ---------------------------------------------------------------------------

-- | Arrows that have unit channel ends for a given unit object @u@.
--
-- The unit ends are the identity-on-@u@ morphism split into its two
-- polar halves.  The companion is constant; the conjoint delegates to
-- the opposing companion.
--
-- These ends require the base arrow to support constant morphisms, so
-- they are captured by this class rather than being definable for all
-- arrows.
class (Category arr) => HasUnit u arr where
  -- | The monoidal unit as channel ends.
  --
  -- === Yank
  --
  -- >>> let ends = open :: Ends (->) () ()
  -- >>> close (conjoint ends) (companion ends) ()
  -- ()
  --
  -- === Unit plug
  --
  -- >>> let endsA = open :: Ends (->) () ()
  -- >>> let endsU = open :: Ends (->) () ()
  -- >>> commit (conjoint endsA) (companion endsU) ()
  -- ()
  -- >>> emit (companion endsA) (conjoint endsU) ()
  -- ()
  open :: Ends arr u u

-- | The copycat strategy at the unit type @u@.
--
-- This is the multiplicative excluded middle @u ⅋ u⊥@ for arrows that have
-- unit ends at @u@: a self-dual channel whose 'close' is the identity on @u@.
-- It routes between the two poles without ever deciding which one holds.
--
-- The additive excluded middle @u ⊕ u⊥@ — a verdict, now — is /not/
-- supported; there is no @decide :: Either u u@ here, because only the
-- routing witness is provable.
copycat :: forall arr u. (HasUnit u arr) => Ends arr u u
copycat = open
{-# INLINE copycat #-}

-- | Build an @Ends@ from a write morphism and a read morphism.
--
-- @write :: arr a ()@ consumes the input payload and produces the unit;
-- @read :: arr () b@ consumes the unit and produces the output payload.
-- The unit ends wire the two halves together.
--
-- This is the canonical way to turn a pair of primitive channel actions
-- into a matched pair of @In@ and @Out@ ends.
--
-- Compositional spelling:
--
-- @
-- ends write receive =
--   Ends (prefixIn write (conjoint open)) (suffixOut (companion open) receive)
-- @
ends ::
  forall arr a b u.
  (Discrete arr, HasUnit u arr) =>
  arr a u ->
  arr u b ->
  Ends arr a b
ends write receive =
  Ends
    (prefixIn write (conjoint open))
    (suffixOut (companion open) receive)

-- | Convenience version of 'ends' when the unit object is @()@.
ends0 ::
  (Discrete arr, HasUnit () arr) =>
  arr a () ->
  arr () b ->
  Ends arr a b
ends0 = ends @_ @_ @_ @()
{-# INLINE ends0 #-}

-- | Specialization of 'ends' for @Kleisli@ actions.
--
-- @write :: a -> m u@ consumes the input payload; @receive :: m b@
-- produces the output payload. The unit handling is hidden inside the
-- @Kleisli@ wrappers.
endsK ::
  forall m a b.
  (Monad m) =>
  (a -> m ()) ->
  m b ->
  Ends (Kleisli m) a b
endsK write receive = ends (Kleisli write) (Kleisli $ const receive)

-- | Extract the primitive write and read actions from an @Ends@ by
-- plugging each end with the unit ends.
--
-- For an @Ends@ built with 'ends', this recovers the original
-- @write :: arr a u@ and @receive :: arr u b@.
--
-- >>> let e = ends0 (\() -> ()) (const (42 :: Int)) :: Ends (->) () Int
-- >>> let (write, receive) = splay0 e
-- >>> (write (), receive ())
-- ((),42)
splay ::
  forall arr a b u.
  (HasUnit u arr) =>
  Ends arr a b ->
  (arr a u, arr u b)
splay e =
  ( commit (conjoint e) (companion (open :: Ends arr u u)),
    emit (companion e) (conjoint (open :: Ends arr u u))
  )

-- | Convenience version of 'splay' when the unit object is @()@.
splay0 ::
  (HasUnit () arr) =>
  Ends arr a b ->
  (arr a (), arr () b)
splay0 = splay @_ @_ @_ @()
{-# INLINE splay0 #-}

-- ---------------------------------------------------------------------------
-- Composition
-- ---------------------------------------------------------------------------

-- | Sequential composition of @Ends@.
--
-- Given @e1 :: Ends arr a b@ and @e2 :: Ends arr b c@, produce an
-- @Ends arr a c@ by connecting the @b@ end of @e1@ to the @b@ end of
-- @e2@.  The primitive actions are extracted via 'splay' and reassembled
-- with 'ends', so 'box' preserves the composition:
--
-- @box (composeEnds e1 e2) = box e2 . box e1@
--
-- Identity exists at the chosen unit type: @open :: Ends arr u u@ is
-- the identity for composition.
--
-- >>> let e1 = ends0 (const ()) (const 1 :: () -> Int) :: Ends (->) () Int
-- >>> let e2 = ends0 (const ()) (const 2 :: () -> Int) :: Ends (->) Int Int
-- >>> run (box @(,) (composeEnds0 e1 e2)) ()
-- 2
composeEnds ::
  forall arr a b c u.
  (Discrete arr, HasUnit u arr) =>
  Ends arr a b ->
  Ends arr b c ->
  Ends arr a c
composeEnds e1 e2 =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @u $
          let (write1, read1) = splay e1 :: (arr a u, arr u b)
              (write2, read2) = splay e2 :: (arr b u, arr u c)
           in ends write1 (read1 .> write2 .> read2)

-- | Convenience version of 'composeEnds' when the unit object is @()@.
composeEnds0 ::
  (Discrete arr, HasUnit () arr) =>
  Ends arr a b ->
  Ends arr b c ->
  Ends arr a c
composeEnds0 = composeEnds @_ @_ @_ @_ @()
{-# INLINE composeEnds0 #-}

-- | Forward-composition operator for @Ends@.  @e1 >:> e2 = composeEnds e1 e2@.
(>:>) ::
  forall arr a b c u.
  (Discrete arr, HasUnit u arr) =>
  Ends arr a b ->
  Ends arr b c ->
  Ends arr a c
e1 >:> e2 = composeEnds @arr @a @b @c @u e1 e2

infixr 1 >:>

-- | Parallel composition of @Ends@.
--
-- Pair two @Ends@ side by side on the tensor @t@.  The primitive
-- actions are tensored and then collapsed to and from the unit with the
-- tensor unitors.  This requires the tensor unit to coincide with the
-- @Ends@ unit @u@; in practice this is the cartesian @(,)@ tensor with
-- @u = ()@.
--
-- >>> let e1 = ends0 (const ()) (const 1 :: () -> Int) :: Ends (->) () Int
-- >>> let e2 = ends0 (const ()) (const 2 :: () -> Int) :: Ends (->) () Int
-- >>> run (box @(,) (parEnds e1 e2)) ((), ())
-- (1,2)
parEnds ::
  forall t arr a b c d u.
  (Tensor t arr, Discrete arr, HasUnit u arr, Unit t ~ u) =>
  Ends arr a b ->
  Ends arr c d ->
  Ends arr (t a c) (t b d)
parEnds e1 e2 =
  withOb @arr @(t a c) $
    withOb @arr @(t b d) $
      withOb @arr @(t u u) $
        withOb @arr @u $
          let (write1, read1) = splay e1 :: (arr a u, arr u b)
              (write2, read2) = splay e2 :: (arr c u, arr u d)
              write = par write1 write2 .> (unitr :: arr (t u u) u)
              readEnds = (unitl' :: arr u (t u u)) .> par read1 read2
           in ends write readEnds

-- | Precompose the input and postcompose the output of an @Ends@.
--
-- This is the morphism-level profunctor action: @f :: arr a' a@ shapes
-- what the conjoint sees, and @g :: arr b b'@ shapes what the companion
-- emits.
--
-- >>> let e = ends0 (const ()) (const 42 :: () -> Int) :: Ends (->) () Int
-- >>> let e' = dimapEnds (const ()) ((+1) :: Int -> Int) e :: Ends (->) () Int
-- >>> run (box @(,) e') ()
-- 43
dimapEnds ::
  forall arr a a' b b'.
  (Discrete arr) =>
  arr a' a ->
  arr b b' ->
  Ends arr a b ->
  Ends arr a' b'
dimapEnds f g (Ends i o) = Ends (prefixIn f i) (suffixOut o g)

-- | Precompose the input of an @Ends@.
lmapEnds ::
  forall arr a a' b.
  (Discrete arr) =>
  arr a' a ->
  Ends arr a b ->
  Ends arr a' b
lmapEnds f (Ends i o) = Ends (prefixIn f i) o

-- | Postcompose the output of an @Ends@.
rmapEnds ::
  forall arr a b b'.
  (Discrete arr) =>
  arr b b' ->
  Ends arr a b ->
  Ends arr a b'
rmapEnds g (Ends i o) = Ends i (suffixOut o g)

-- | Unit ends for @(->)@ with unit @()@.
--
-- The companion is the constant function returning @()@; the conjoint
-- recursively emits through the supplied companion.
instance HasUnit () (->) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> const ()
      inU = In $ \o -> emit o inU

-- | Unit ends for @Kleisli@ @m@ with unit @()@.
--
-- Same shape as the @(->)@ instance, but the constant companion returns
-- @()@ in the monad.
instance (Monad m) => HasUnit () (Kleisli m) where
  open = Ends inU outU
    where
      outU = Out $ \_ -> Kleisli $ \_ -> pure ()
      inU = In $ \o -> emit o inU

-- ---------------------------------------------------------------------------
-- Boxes
-- ---------------------------------------------------------------------------

-- | String-diagram boxes from channel ends.
--
-- A matched pair of free ends (@Ends@) is a box with one input wire and
-- one output wire.  The helpers below embed that box into a traced
-- monoidal category by unit-plugging the remaining two slots.

-- | Embed an @Ends@ into a plain @Loop t arr a b@.
--
-- Connects the two channel ends through the unit object, giving a plain
-- @Loop t arr a b@. This is the version most users expect: input on the
-- left, output on the right, with the unit plumbing hidden.
--
-- >>> let e = ends0 (const ()) (const 42) :: Ends (->) () Int
-- >>> run (box @(,) e) ()
-- 42
box ::
  forall t arr a b.
  (HasUnit (Unit t) arr, Ob arr a, Ob arr b, Ob arr (Unit t)) =>
  Ends arr a b ->
  Loop t arr a b
box ends' =
  Lift $
    commit (conjoint ends') (companion (open :: Ends arr (Unit t) (Unit t)))
      .> emit (companion ends') (conjoint (open :: Ends arr (Unit t) (Unit t)))

-- | Asymmetric box with units exposed on opposite sides.
--
-- Uses 'par' at the base arrow level and lifts the result with 'Lift'.
-- The input carries the unit on the right and the output carries the unit
-- on the left; most users will prefer the unit-normalised 'box'.
--
-- >>> let e = ends0 (const ()) (const 42) :: Ends (->) () Int
-- >>> run (boxAsymmetric @(,) e) ((), ())
-- ((),42)
boxAsymmetric ::
  forall t arr a b.
  (HasUnit (Unit t) arr, Tensor t arr) =>
  Ends arr a b ->
  Loop t arr (t a (Unit t)) (t (Unit t) b)
boxAsymmetric ends' =
  Lift $
    par
      (commit (conjoint ends') (companion open))
      (emit (companion ends') (conjoint open))

-- $setup
-- >>> import Circuit.Ends
-- >>> import Circuit.Layer (run)

-- | Parallel product of two morphisms on a pair.
--
-- This is the cartesian product, renamed from 'Par' to avoid collision with
-- the multiplicative disjunction 'Circuit.Tensor.Par'.
class CartesianPar arr where
  parP :: arr a b -> arr c d -> arr (a, c) (b, d)

instance CartesianPar (->) where
  parP f g (x, y) = (f x, g y)

instance (Monad m) => CartesianPar (Kleisli m) where
  parP (Kleisli f) (Kleisli g) = Kleisli $ \(x, y) -> (,) <$> f x <*> g y

-- | Values that can be tested for silence.
class IsSilent b where
  -- | True iff the value is silent.
  isSilent :: b -> Bool

instance IsSilent [a] where
  isSilent = null

instance IsSilent (Maybe a) where
  isSilent = isNothing

instance IsSilent Void where
  isSilent = const True

-- | Values that carry a canonical silent value.
class (IsSilent b) => HasSilent b where
  -- | The canonical silent value.
  silent :: b

instance HasSilent [a] where
  silent = []

instance HasSilent (Maybe a) where
  silent = Nothing

-- | Schedule bias for disjunctive composition.
data Bias = LeftFirst | RightFirst
  deriving (Eq, Show)

-- | Additive conjunction: both sub-ends receive the same input and their
-- outputs are paired.
--
-- This is the @&@ connective / 'await' fragment: every branch sees the
-- input, and the composite emits all of their results.
--
-- >>> let e1 = ends0 (const ()) (const 1 :: () -> Int) :: Ends (->) () Int
-- >>> let e2 = ends0 (const ()) (const 2 :: () -> Int) :: Ends (->) () Int
-- >>> run (box @(,) (pairEnds e1 e2)) ()
-- (1,2)
pairEnds ::
  (CopyDiscard (->) a) =>
  Ends (->) a b ->
  Ends (->) a c ->
  Ends (->) a (b, c)
pairEnds e1 e2 =
  let (w1, r1) = splay0 e1
      (w2, r2) = splay0 e2
      w = discard . parP w1 w2 . copy
      r = parP r1 r2 . copy
   in ends0 w r

-- | Additive disjunction / race: both sub-ends receive the same input, but
-- only the first non-silent output (according to the bias) is emitted.
--
-- The bias is explicit in the term rather than silently left-biased.  The
-- picking logic is the additive disjunction mediator: a state machine whose
-- residual is the first non-silent value it has seen.
--
-- >>> let eL = ends0 (const ()) (const (Just 1)) :: Ends (->) () (Maybe Int)
-- >>> let eR = ends0 (const ()) (const (Just 2)) :: Ends (->) () (Maybe Int)
-- >>> run (box @(,) (raceEnds LeftFirst eL eR)) ()
-- Just 1
-- >>> run (box @(,) (raceEnds RightFirst eL eR)) ()
-- Just 2
raceEnds ::
  (CopyDiscard (->) a, IsSilent b) =>
  Bias ->
  Ends (->) a b ->
  Ends (->) a b ->
  Ends (->) a b
raceEnds bias e1 e2 =
  let (w1, r1) = splay0 e1
      (w2, r2) = splay0 e2
      w = discard . parP w1 w2 . copy
      r = pick bias . parP r1 r2 . copy
   in ends0 w r
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y

-- | Additive disjunction as a mediator.
--
-- The residual is the first non-silent value seen.  Once set, every further
-- input is ignored and the chosen value is emitted repeatedly.  This is the
-- same picking logic as 'raceEnds', expressed in the @?@-policy vocabulary.
raceMediator :: (IsSilent b) => Bias -> Mediator (Maybe b) (b, b) b
raceMediator bias =
  Mediator Nothing $ \s (x, y) ->
    case s of
      Just z -> (Just z, Just z)
      Nothing ->
        let z = pick bias (x, y)
         in (Just z, Just z)
  where
    pick LeftFirst (x, y) = if isSilent x then y else x
    pick RightFirst (x, y) = if isSilent y then x else y
