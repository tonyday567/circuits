{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- | Channel structure for the tensors used in traced categories.
--
-- This module collects the braided, cartesian, and cocartesian structure
-- over the standard tensors @(,)@ and 'Either', along with the general
-- 'ambientBy' combinator for threading additional state wires.
--
-- The goal is to keep the core 'Loop' GADT and 'run' mechanism
-- independent of these structural details.
--
-- Note: the monomorphic 'assocL' and 'assocR' helpers below reassociate
-- /leftward/ and /rightward/ respectively — the opposite direction to
-- 'Circuit.Channel.assoc' and 'Circuit.Channel.assoc''. The 'slide'
-- from 'Braided' is the slide @t a (t b c) -> t b (t a c)@; 'swap' here
-- is the symmetric braiding @t a b -> t b a@. They cohere as
-- @slide = assocR '.>' par swap id '.>' assocL@ wherever the 'Tensor'
-- and 'Action' structure is available.
--
-- 'Tensor' / 'Action' are kind-polymorphic.
module Circuit.Tensor
  ( Braided (..),
    ambient,
    ambientBy,
    superpose,

    -- * Channel product on base arrows
    Unit,
    Tensor (..),
    Action (..),

    -- * Shared-medium fusion (the ⅋ connective)
    Bias (..),
    Fire (..),
    Schedule (..),
    Shared (..),
    sharedKnotBy,

    -- * Cartesian / cocartesian associators
    assocL,
    assocR,
    coassoc,
    coassoc',
    coseed,
    coabsorbL,
    coabsorbR,
    coreleaseL,
    coreleaseR,

    -- * Multiplicative disjunction (par)
    Bot,
    Par (..),
    distL,
    distR,
    mix,

    -- * Linear implication (internal hom)
    Lolli (..),

    -- * Exponentials
    Exponential (..),
    BangCopy (..),
    BangWeaken (..),
    WhyNotIntro (..),
    WhyNotMonoid (..),
    LinearBang,
    AffineBang,
    RelevantBang,
  )
where

import Circuit.Category (Category (..), Discrete (..), (.>))
import Circuit.Channel (Strength (..), Traced (..), assocD, assocD', braidD, strengthD)
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Control.Arrow (Kleisli (..))
import Control.Monad (Monad)
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.Profunctor (Profunctor, dimap)
import Data.These (These (..))
import Data.Void (Void, absurd)
import Prelude hiding (curry, id, uncurry, (.))

-- $setup
-- >>> :set -XLambdaCase
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Loop (Loop (..))
-- >>> import Control.Arrow (Kleisli (..), runKleisli)
-- >>> import Data.Functor.Identity (Identity)
-- >>> import Prelude hiding (id, (.))

-- ===========================================================================
-- BRAIDING
-- ===========================================================================

-- | A braiding for a bifunctor tensor.
--
-- The slide swaps a wire past a nested pair:
--
-- @
--   t x (t y z)  ->  t y (t x z)
-- @
--
-- For @(,)@ this is the cartesian slide.  For @Either@ it is the
-- coproduct slide.  Both are derived from the associator and swap.
class (Bifunctor t) => Braided t where
  slide :: t x (t y z) -> t y (t x z)

-- | Cartesian slide: @(x, (y, z)) -> (y, (x, z))@.
instance Braided (,) where
  slide ~(x, ~(y, z)) = (y, (x, z))

-- | Coproduct slide.
--
-- >>> slide (Left "hi" :: Either String (Either Int Bool))
-- Right (Left "hi")
instance Braided Either where
  slide (Left x) = Right (Left x)
  slide (Right (Left y)) = Left y
  slide (Right (Right z)) = Right (Right z)

-- | Thread a state wire through a circuit using the canonical slide.
--
-- This is 'ambientBy' with the slide supplied by the 'Braided' instance.
ambient ::
  (Braided t, Strength t (->)) =>
  Loop t (->) a b ->
  Loop t (->) (t s a) (t s b)
ambient = ambientBy slide

-- ===========================================================================
-- CARTESIAN STRUCTURE ((,))
-- ===========================================================================

-- | Leftward associator: @(a, (b, c)) -> ((a, b), c)@.
assocL :: (a, (b, c)) -> ((a, b), c)
assocL ~(a, ~(b, c)) = ((a, b), c)

-- | Rightward associator: @((a, b), c) -> (a, (b, c))@.
assocR :: ((a, b), c) -> (a, (b, c))
assocR ~(~(a, b), c) = (a, (b, c))

-- | Introduce a state wire alongside a payload.
--
-- Given an initial state and a payload value, produce a paired value
-- suitable for feeding into a circuit threaded with 'ambientBy'.
seed :: s -> a -> (s, a)
seed s a = (s, a)

-- | Move a value from the payload into the state wire.
--
-- @absorb f = first (uncurry f) . assocL@
absorb :: (t -> s -> s') -> (s, (t, b)) -> (s', b)
absorb f (s, (t, b)) = (f t s, b)

-- | Move a value from the state wire into the payload.
--
-- @release f = assocR . first f@
release :: (s -> (s', t)) -> (s, b) -> (s', (t, b))
release f (s, b) = let (s', t) = f s in (s', (t, b))

-- ===========================================================================
-- COCARTESIAN STRUCTURE (Either)
-- ===========================================================================

-- | Coassociator for sums.
--
-- >>> coassoc (Left 1 :: Either Int (Either Bool Char))
-- Left (Left 1)
coassoc :: Either a (Either b c) -> Either (Either a b) c
coassoc (Left a) = Left (Left a)
coassoc (Right (Left b)) = Left (Right b)
coassoc (Right (Right c)) = Right c

-- | Inverse coassociator.
--
-- >>> coassoc' (Left (Left 1) :: Either (Either Int Bool) Char)
-- Left 1
coassoc' :: Either (Either a b) c -> Either a (Either b c)
coassoc' (Left (Left a)) = Left a
coassoc' (Left (Right b)) = Right (Left b)
coassoc' (Right c) = Right (Right c)

-- | Tag a state value onto whichever branch of the sum is active.
--
-- >>> coseed "st" (Left 42 :: Either Int Char)
-- Left ("st",42)
coseed :: s -> Either a b -> Either (s, a) (s, b)
coseed s = bimap (s,) (s,)

-- | If the left branch is taken, move a value from the payload into the state wire.
--
-- >>> coabsorbL (+) (Left (10, (3, 7)) :: Either (Int, (Int, Int)) Bool)
-- Left (13,7)
coabsorbL :: (t -> s -> s') -> Either (s, (t, a)) b -> Either (s', a) b
coabsorbL f (Left (s, (t, a))) = Left (f t s, a)
coabsorbL _ (Right b) = Right b

-- | If the right branch is taken, move a value from the payload into the state wire.
--
-- >>> coabsorbR (+) (Right (10, (3, 7)) :: Either Bool (Int, (Int, Int)))
-- Right (13,7)
coabsorbR :: (t -> s -> s') -> Either a (s, (t, b)) -> Either a (s', b)
coabsorbR f (Right (s, (t, b))) = Right (f t s, b)
coabsorbR _ (Left a) = Left a

-- | If the left branch is taken, move a value from the state wire into the payload.
--
-- >>> coreleaseL (\s -> (s+1, s*2)) (Left (5, 99) :: Either (Int, Int) Char)
-- Left (6,(10,99))
coreleaseL :: (s -> (s', t)) -> Either (s, a) b -> Either (s', (t, a)) b
coreleaseL f (Left (s, a)) = let (s', t) = f s in Left (s', (t, a))
coreleaseL _ (Right b) = Right b

-- | If the right branch is taken, move a value from the state wire into the payload.
--
-- >>> coreleaseR (\s -> (s+1, s*2)) (Right (5, 99) :: Either Char (Int, Int))
-- Right (6,(10,99))
coreleaseR :: (s -> (s', t)) -> Either a (s, b) -> Either a (s', (t, b))
coreleaseR f (Right (s, b)) = let (s', t) = f s in Right (s', (t, b))
coreleaseR _ (Left a) = Left a

-- ===========================================================================
-- GENERAL AMBIENT STATE THREADING
-- ===========================================================================

-- | Thread a state wire through a Circuit.
--
-- 'ambientBy' threads an additional state component alongside a circuit
-- without the circuit having to mention it. The state wire is slid
-- past the feedback channel so it travels "ambiently".
--
-- The @slide@ function swaps the state wire past the feedback channel:
-- @t x (t s a) -> t s (t x a)@. For @(,)@, this is
-- @\(x, (s, a)) -> (s, (x, a))@.
--
-- >>> import Circuit.Layer (run)
-- >>> import Circuit.Loop (Loop(..))
-- >>> let slide (x, (s, a)) = (s, (x, a))
-- >>> run (ambientBy slide (Lift (+1) :: Loop (,) (->) Int Int)) ("st", 5)
-- ("st",6)
--
-- >>> let step (xs, ()) = (0 : xs, take 3 xs)
-- >>> run (ambientBy slide (Knot step)) ("st", ())
-- ("st",[0,0,0])
ambientBy ::
  (Strength t (->)) =>
  (forall x y z. t x (t y z) -> t y (t x z)) ->
  Loop t (->) a b ->
  Loop t (->) (t s a) (t s b)
ambientBy _br (Lift f) = Lift (strength f)
ambientBy br (Knot k) = Knot (dimap br br (strength k))

-- ===========================================================================
-- Tensor / Action — tensor action on morphisms
-- ===========================================================================

-- | The unit object for a tensor @t@.
--
-- @t@ is an object-level bifunctor (@Either@, @(,)@, type-level @(+)@, …)
-- with kind @k -> k -> k@, not a morphism tensor.
type family Unit (t :: k -> k -> k) :: k

-- | The tensor action of @t@ on a category @arr@, without braiding.
--
-- 'par' is the tensor product of morphisms (parallel composition on
-- disjoint wires). 'unitl' and 'unitr' witness that the tensor has a unit
-- object. This is the planar fragment: 'Tensor' only provides the
-- associator and unitors, not a braiding.
--
-- Kind-polymorphic: @t@ and @arr@ share object kind (inferred via PolyKinds).
class (Category arr) => Tensor t arr where
  -- | Parallel composition: run two arrows on disjoint wires.
  --
  -- >>> par ((+1) :: Int -> Int) ((*2) :: Int -> Int) (3, 4)
  -- (4,8)
  par :: (Ob arr a, Ob arr b, Ob arr c, Ob arr d) => arr a b -> arr c d -> arr (t a c) (t b d)

  -- | Left unitor: @I ⊗ a -> a@.
  unitl :: (Ob arr a) => arr (t (Unit t) a) a

  -- | Inverse left unitor: @a -> I ⊗ a@.
  unitl' :: (Ob arr a) => arr a (t (Unit t) a)

  -- | Right unitor: @a ⊗ I -> a@.
  unitr :: (Ob arr a) => arr (t a (Unit t)) a

  -- | Inverse right unitor: @a -> a ⊗ I@.
  unitr' :: (Ob arr a) => arr a (t a (Unit t))

-- | The action of a tensor @t@ on a category @arr@, extended with a
-- symmetric braiding.
--
-- This is the self-action of a symmetric monoidal category: @t@ acts on
-- @arr@ by taking morphisms to morphisms over paired objects, and 'swap'
-- provides the symmetry.
class (Tensor t arr) => Action t arr where
  -- | Symmetric braiding.
  --
  -- >>> swap (3, 4) :: (Int, Int)
  -- (4,3)
  swap :: (Ob arr a, Ob arr b) => arr (t a b) (t b a)

type instance Unit (,) = ()

-- | Cartesian tensor action on functions.
--
-- Laws: 'unitl' = 'snd', 'unitl'' = @((),)@, 'unitr' = 'fst', 'unitr'' = @(,) ()@.
instance Tensor (,) (->) where
  par f g (a, c) = (f a, g c)
  {-# INLINE par #-}
  unitl ~((), a) = a
  {-# INLINE unitl #-}
  unitl' a = ((), a)
  {-# INLINE unitl' #-}
  unitr ~(a, ()) = a
  {-# INLINE unitr #-}
  unitr' a = (a, ())
  {-# INLINE unitr' #-}

-- | Cartesian symmetry on functions.
instance Action (,) (->) where
  swap (a, b) = (b, a)
  {-# INLINE swap #-}

-- | Cartesian tensor on @Kleisli@ (effectful sequential product).
instance (Monad m) => Tensor (,) (Kleisli m) where
  par (Kleisli f) (Kleisli g) =
    Kleisli $ \(a, c) -> do
      b <- f a
      d <- g c
      pure (b, d)
  {-# INLINE par #-}
  unitl = Kleisli $ \((), a) -> pure a
  {-# INLINE unitl #-}
  unitl' = Kleisli $ \a -> pure ((), a)
  {-# INLINE unitl' #-}
  unitr = Kleisli $ \(a, ()) -> pure a
  {-# INLINE unitr #-}
  unitr' = Kleisli $ \a -> pure (a, ())
  {-# INLINE unitr' #-}

instance (Monad m) => Action (,) (Kleisli m) where
  swap = Kleisli $ \(a, b) -> pure (b, a)
  {-# INLINE swap #-}

type instance Unit Either = Void

-- | Coproduct tensor action on functions.
--
-- >>> par ((+1) :: Int -> Int) ((*2) :: Int -> Int) (Left 3 :: Either Int Int)
-- Left 4
--
-- >>> par ((+1) :: Int -> Int) ((*2) :: Int -> Int) (Right 3 :: Either Int Int)
-- Right 6
instance Tensor Either (->) where
  par = bimap
  {-# INLINE par #-}
  unitl = either absurd id
  {-# INLINE unitl #-}
  unitl' = Right
  {-# INLINE unitl' #-}
  unitr = either id absurd
  {-# INLINE unitr #-}
  unitr' = Left
  {-# INLINE unitr' #-}

-- | Coproduct symmetry on functions.
--
-- >>> swap (Left 3 :: Either Int Int) :: Either Int Int
-- Right 3
instance Action Either (->) where
  swap = \case
    Left a -> Right a
    Right b -> Left b
  {-# INLINE swap #-}

-- | Coproduct tensor action on @Kleisli@ @m@.
--
-- >>> import Control.Arrow (Kleisli(..), runKleisli)
-- >>> let f = Kleisli (\n -> pure (n + 1)) :: Kleisli IO Int Int
-- >>> let g = Kleisli (\n -> pure (n * 2)) :: Kleisli IO Int Int
-- >>> runKleisli (par f g) (Left 3 :: Either Int Int)
-- Left 4
-- >>> runKleisli (par f g) (Right 3 :: Either Int Int)
-- Right 6
instance (Monad m) => Tensor Either (Kleisli m) where
  par (Kleisli f) (Kleisli g) =
    Kleisli $ \case
      Left a -> Left <$> f a
      Right c -> Right <$> g c
  {-# INLINE par #-}
  unitl = Kleisli $ either absurd pure
  {-# INLINE unitl #-}
  unitl' = Kleisli $ pure . Right
  {-# INLINE unitl' #-}
  unitr = Kleisli $ either pure absurd
  {-# INLINE unitr #-}
  unitr' = Kleisli $ pure . Left
  {-# INLINE unitr' #-}

-- | Coproduct symmetry on @Kleisli@ @m@.
instance (Monad m) => Action Either (Kleisli m) where
  swap = Kleisli $ pure . swap
  {-# INLINE swap #-}

type instance Unit These = Void

-- | Inclusive tensor action on functions.
--
-- Laws: 'unitl' eliminates a vacuous 'This', 'unitl'' injects with 'That';
-- 'unitr' eliminates a vacuous 'That', 'unitr'' injects with 'This'.
instance Tensor These (->) where
  par = bimap
  {-# INLINE par #-}
  unitl (That a) = a
  unitl (This v) = absurd v
  unitl (These v _) = absurd v
  {-# INLINE unitl #-}
  unitl' = That
  {-# INLINE unitl' #-}
  unitr (This a) = a
  unitr (That v) = absurd v
  unitr (These _ v) = absurd v
  {-# INLINE unitr #-}
  unitr' = This
  {-# INLINE unitr' #-}

-- | Inclusive symmetry on functions.
instance Action These (->) where
  swap (This a) = That a
  swap (That b) = This b
  swap (These a b) = These b a
  {-# INLINE swap #-}

-- | Inclusive tensor action on @Kleisli@ @m@.
instance (Monad m) => Tensor These (Kleisli m) where
  par (Kleisli f) (Kleisli g) =
    Kleisli $ \case
      This a -> This <$> f a
      That c -> That <$> g c
      These a c -> These <$> f a <*> g c
  {-# INLINE par #-}
  unitl = Kleisli $ \case
    That a -> pure a
    This v -> absurd v
    These v _ -> absurd v
  {-# INLINE unitl #-}
  unitl' = Kleisli $ pure . That
  {-# INLINE unitl' #-}
  unitr = Kleisli $ \case
    This a -> pure a
    That v -> absurd v
    These _ v -> absurd v
  {-# INLINE unitr #-}
  unitr' = Kleisli $ pure . This
  {-# INLINE unitr' #-}

-- | Inclusive symmetry on @Kleisli@ @m@.
instance (Monad m) => Action These (Kleisli m) where
  swap =
    Kleisli $
      pure . \case
        This a -> That a
        That b -> This b
        These a b -> These b a
  {-# INLINE swap #-}

-- | Lift 'Tensor'/'Action' through 'Loop'.
--
-- This is the single lawful instance: it evaluates each 'Loop' branch
-- independently with 'run' and combines the results using the base arrow's
-- tensor. It is correct and black-hole-free, but does not fuse feedback
-- loops. For the fused superposition of two 'Knot's, use 'superpose'.
instance (Tensor t arr, Traced t' arr) => Tensor t (Loop t' arr) where
  par ::
    forall a b c d.
    ( Ob (Loop t' arr) a,
      Ob (Loop t' arr) b,
      Ob (Loop t' arr) c,
      Ob (Loop t' arr) d
    ) =>
    Loop t' arr a b ->
    Loop t' arr c d ->
    Loop t' arr (t a c) (t b d)
  par f g = Lift (par (run f) (run g))
  unitl = Lift unitl
  unitl' = Lift unitl'
  unitr = Lift unitr
  unitr' = Lift unitr'

instance (Action t arr, Traced t' arr) => Action t (Loop t' arr) where
  swap = Lift swap

-- | Fused parallel composition for 'Loop' when the feedback tensor matches.
--
-- Two 'Knot's in parallel superpose into one 'Knot' over a paired channel,
-- satisfying the superposing axiom of traced monoidal categories:
--
-- @superpose (trace f) (trace g) = trace (pre . par f g . post)@
--
-- where @pre@ and @post@ rearrange the paired channel via associators
-- and braiding. This preserves sharing for recursive circuits; the lawful
-- 'Tensor' instance falls back to independent evaluation.
--
-- >>> let k1 = Circuit.Loop.Knot (\(ns, _) -> (1 : ns, take 3 ns)) :: Circuit.Loop.Loop (,) (->) [Int] [Int]
-- >>> let k2 = Circuit.Loop.Knot (\(ns, _) -> (2 : ns, take 3 ns))
-- >>> Circuit.Layer.run (superpose k1 k2) ([], [])
-- ([1,1,1],[2,2,2])
--
-- The same fusion works for @Kleisli@, preserving sharing across the
-- recursive channels under @MonadFix@.
--
-- >>> let k1 = Circuit.Loop.Knot (Kleisli $ \(ns, _) -> pure (1 : ns, take 3 ns)) :: Circuit.Loop.Loop (,) (Kleisli Identity) [Int] [Int]
-- >>> let k2 = Circuit.Loop.Knot (Kleisli $ \(ns, _) -> pure (2 : ns, take 3 ns))
-- >>> runKleisli (Circuit.Layer.run (superpose k1 k2)) ([], [])
-- Identity ([1,1,1],[2,2,2])
superpose ::
  forall t arr a b c d.
  (Tensor t arr, Strength t arr, Discrete arr) =>
  Loop t arr a b ->
  Loop t arr c d ->
  Loop t arr (t a c) (t b d)
superpose x y =
  withOb @arr @a $
    withOb @arr @b $
      withOb @arr @c $
        withOb @arr @d $
          case (x, y) of
            (Knot @_ @s @_ @_ @_ f, Knot @_ @s1 @_ @_ @_ g) ->
              withOb @arr @(t s s1) $
                withOb @arr @(t (t s s1) (t a c)) $
                  withOb @arr @(t (t s s1) (t b d)) $
                    Knot $
                      pre .>> par f g .>> post
            (Knot @_ @s @_ @_ @_ f, Lift g) ->
              withOb @arr @(t s (t a c)) $
                withOb @arr @(t s (t b d)) $
                  Knot $
                    assoc'_ .>> par f g .>> assoc_
            (Lift f, Knot @_ @s @_ @_ @_ g) ->
              withOb @arr @(t s (t a c)) $
                withOb @arr @(t s (t b d)) $
                  Knot $
                    braid_ .>> par f g .>> braid_
            (Lift f, Lift g) -> Lift (par f g)
  where
    (.>>) :: forall x y z. arr x y -> arr y z -> arr x z
    (.>>) f' g' = withOb @arr @x $ withOb @arr @y $ withOb @arr @z $ g' . f'

    assoc_ :: forall x y z. arr (t (t x y) z) (t x (t y z))
    assoc_ = assocD

    assoc'_ :: forall x y z. arr (t x (t y z)) (t (t x y) z)
    assoc'_ = assocD'

    braid_ :: forall x y z. arr (t x (t y z)) (t y (t x z))
    braid_ = braidD

    pre, post :: forall u v w x. arr (t (t u v) (t w x)) (t (t u w) (t v x))
    pre = assoc_ .>> strengthD braid_ .>> assoc'_
    post = assoc_ .>> strengthD braid_ .>> assoc'_

-- ===========================================================================
-- Shared-medium fusion (the ⅋ connective)
-- ===========================================================================

-- | Nonempty ordered subsets of the active poles in shared-feedback fusion.
--
-- | Schedule bias for the inclusive @These@ branch.
data Bias = LeftFirst | RightFirst
  deriving (Eq, Show)

-- | A schedule decision, now shaped by the inclusive tensor.
--
-- * @L@ — advance the left body only; the right input is not consumed
--   (corresponds to 'This').
-- * @R@ — advance the right body only; the left input is not consumed
--   (corresponds to 'That').
-- * @Both b@ — advance both bodies, with the bias choosing the order
--   (corresponds to 'These').
data Fire = L | R | Both Bias
  deriving (Eq, Show)

-- | A schedule drives shared-feedback fusion.
--
-- The state @s@ is the shared feedback channel.  At each step the schedule
-- looks at the state and chooses which poles advance, returning the updated
-- schedule state.
newtype Schedule s = Schedule
  { -- | Given the current shared state, return the updated state and a 'Fire'
    -- value describing which poles advance and in what order.
    chooseS :: s -> (s, Fire)
  }

-- | Tensors that support shared-feedback fusion of two knot bodies.
--
-- This is the operational content of the multiplicative disjunction: two
-- sub-loops share one feedback channel, and a 'Schedule' resolves the
-- interleaving.  Contrast 'superpose', which keeps the feedback channels
-- independent (⊗).
class (Tensor t arr) => Shared t arr where
  -- | Fuse two feedback bodies over a shared channel.
  --
  -- The combined body has type @arr (t s (t a c)) (t s (These b d))@: one
  -- shared state @s@, paired inputs @a@ and @c@, and a partial output.  At
  -- each step the schedule chooses which body advances; the gated body's
  -- input is discarded and no output is produced for that side.
  sharedBy ::
    Schedule s ->
    arr (t s a) (t s b) ->
    arr (t s c) (t s d) ->
    arr (t s (t a c)) (t s (These b d))

-- | Shared fusion wrapped as a 'Knot'.
--
-- This takes explicit knot bodies that already share the feedback type @s@.
-- 'Loop' hides its feedback type existentially, so a generic 'Loop'-level
-- combinator cannot constrain two arbitrary knots to share the same channel;
-- this helper makes the shared state explicit at the call site.
sharedKnotBy ::
  forall t arr a b c d s.
  (Shared t arr, Ob arr s, Ob arr (t s (t a c)), Ob arr (t s (These b d))) =>
  Schedule s ->
  arr (t s a) (t s b) ->
  arr (t s c) (t s d) ->
  Loop t arr (t a c) (These b d)
sharedKnotBy sched f g = Knot (sharedBy sched f g)

-- | Cartesian shared fusion on functions.
--
-- The schedule chooses which bodies advance and in what order.  @L@/@R@
-- run only the chosen body and emit a partial 'This'/'That' product; the
-- other body's input is discarded.  @Both LeftFirst@ / @Both RightFirst@ run
-- both bodies, threading the shared state in the chosen order, and emit a
-- total 'These' product.  When both bodies read and write @s@, the two orders
-- are observationally different — this is the ⅋-vs-⊗ distinction.
instance Shared (,) (->) where
  sharedBy sched f g (s, (a, c)) =
    let (s', fire) = chooseS sched s
     in case fire of
          L ->
            let (s'', b) = f (s', a)
             in (s'', This b)
          R ->
            let (s'', d) = g (s', c)
             in (s'', That d)
          Both LeftFirst ->
            let (s'', b) = f (s', a)
                (s''', d) = g (s'', c)
             in (s''', These b d)
          Both RightFirst ->
            let (s'', d) = g (s', c)
                (s''', b) = f (s'', a)
             in (s''', These b d)
  {-# INLINE sharedBy #-}

-- | Cartesian shared fusion on @Kleisli@ arrows.
instance (Monad m) => Shared (,) (Kleisli m) where
  sharedBy sched (Kleisli f) (Kleisli g) =
    Kleisli $ \(s, (a, c)) -> do
      let (s', fire) = chooseS sched s
      case fire of
        L -> do
          (s'', b) <- f (s', a)
          pure (s'', This b)
        R -> do
          (s'', d) <- g (s', c)
          pure (s'', That d)
        Both LeftFirst -> do
          (s'', b) <- f (s', a)
          (s''', d) <- g (s'', c)
          pure (s''', These b d)
        Both RightFirst -> do
          (s'', d) <- g (s', c)
          (s''', b) <- f (s'', a)
          pure (s''', These b d)
  {-# INLINE sharedBy #-}

-- | Unit of the par tensor (⊥).
type family Bot (p :: k -> k -> k) :: k

-- | Multiplicative disjunction action on a category.
--
-- 'parP' is the par product of morphisms.  The unitors witness that
-- @⊥ ⅋ a ≅ a@ and @a ⅋ ⊥ ≅ a@.
class (Category arr) => Par p arr where
  -- | Parallel composition under par.
  parP :: arr a b -> arr c d -> arr (p a c) (p b d)

  -- | Left unitor: @⊥ ⅋ a -> a@.
  unitlP :: (Ob arr a) => arr (p (Bot p) a) a

  -- | Inverse left unitor: @a -> ⊥ ⅋ a@.
  unitlP' :: (Ob arr a) => arr a (p (Bot p) a)

  -- | Right unitor: @a ⅋ ⊥ -> a@.
  unitrP :: (Ob arr a) => arr (p a (Bot p)) a

  -- | Inverse right unitor: @a -> a ⅋ ⊥@.
  unitrP' :: (Ob arr a) => arr a (p a (Bot p))

type instance Bot Either = Void

-- | Coproduct as multiplicative disjunction on functions.
--
-- The unit is the initial object @Void@; the unitors are the coproduct
-- injections absorbed by the universal property.
instance Par Either (->) where
  parP = bimap
  {-# INLINE parP #-}
  unitlP = either absurd id
  {-# INLINE unitlP #-}
  unitlP' = Right
  {-# INLINE unitlP' #-}
  unitrP = either id absurd
  {-# INLINE unitrP #-}
  unitrP' = Left
  {-# INLINE unitrP' #-}

-- | Coproduct as multiplicative disjunction on @Kleisli@ arrows.
instance (Monad m) => Par Either (Kleisli m) where
  parP (Kleisli f) (Kleisli g) =
    Kleisli $ \case
      Left a -> Left <$> f a
      Right c -> Right <$> g c
  {-# INLINE parP #-}
  unitlP = Kleisli $ either absurd pure
  {-# INLINE unitlP #-}
  unitlP' = Kleisli $ pure . Right
  {-# INLINE unitlP' #-}
  unitrP = Kleisli $ either pure absurd
  {-# INLINE unitrP #-}
  unitrP' = Kleisli $ pure . Left
  {-# INLINE unitrP' #-}

-- ---------------------------------------------------------------------------
-- Linear distributors and mix
-- ---------------------------------------------------------------------------

-- | Left linear distributor: @A ⊗ (B ⅋ C) -> (A ⊗ B) ⅋ C@.
--
-- For @(,)@ and @Either@ this is the one-way product-over-coproduct map.
-- Note that @(_, Right c) = Right c@ discards the @a@; this is legal
-- affinely but not in strict MLL. The distributors already live in the
-- affine fragment.
distL :: (a, Either b c) -> Either (a, b) c
distL (a, Left b) = Left (a, b)
distL (_, Right c) = Right c
{-# INLINE distL #-}

-- | Right linear distributor: @(B ⅋ C) ⊗ A -> B ⅋ (C ⊗ A)@.
--
-- Mirror of 'distL': the same affine discard is present when the left
-- summand is taken.
distR :: (Either b c, a) -> Either b (c, a)
distR (Left b, _) = Left b
distR (Right c, a) = Right (c, a)
{-# INLINE distR #-}

-- | Mix: the canonical map @⊥ -> 1@ from par unit to tensor unit.
--
-- Every @⊥@-value is vacuous, so it maps to the unique tensor unit.
mix :: Void -> ()
mix = absurd
{-# INLINE mix #-}

-- ===========================================================================
-- Linear implication (internal hom)
-- ===========================================================================

-- | Closed monoidal structure: @A ⊸ B@ is the right adjoint of tensor.
--
-- Maps @A ⊗ B -> C@ correspond to maps @A -> B ⊸ C@ via 'curry'/'uncurry'.
-- 'eval' is the counit @A ⊗ (A ⊸ B) -> B@ (hom on the right of the tensor).
-- That is the existing Chu convention; it differs from @uncurry id@ by a
-- 'swap'.  'lolli' is identity on the implication object, used to mention
-- it.
--
-- Kind is fixed to 'Type' so type applications stay concrete (GHC 9.14
-- panics on kind-polymorphic @TypeApplications@ here).
class (Category arr) => Lolli (t :: Type -> Type -> Type) (arr :: Type -> Type -> Type) where
  -- | The implication object @A ⊸ B@.
  --
  -- Indexed by the base arrow as well as the tensor, so @(->)@ and
  -- @Mat@ can both close @(,)@ without colliding.
  type LolliT t arr a b :: Type

  -- | Identity at the implication object.  The argument is a type proxy.
  lolli ::
    (Ob arr a, Ob arr b, Ob arr (LolliT t arr a b)) =>
    arr a b ->
    arr (LolliT t arr a b) (LolliT t arr a b)

  -- | Evaluation counit @A ⊗ (A ⊸ B) -> B@.
  eval ::
    ( Ob arr a,
      Ob arr b,
      Ob arr (LolliT t arr a b),
      Ob arr (t a (LolliT t arr a b))
    ) =>
    arr (t a (LolliT t arr a b)) b

  -- | Curry the left factor: @(A ⊗ B -> C) -> (A -> B ⊸ C)@.
  curry ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (LolliT t arr b c)
    ) =>
    arr (t a b) c ->
    arr a (LolliT t arr b c)

  -- | Uncurry the left factor: @(A -> B ⊸ C) -> (A ⊗ B -> C)@.
  uncurry ::
    ( Ob arr a,
      Ob arr b,
      Ob arr c,
      Ob arr (t a b),
      Ob arr (LolliT t arr b c)
    ) =>
    arr a (LolliT t arr b c) ->
    arr (t a b) c

-- | Cartesian closed structure on functions: implication collapses to
-- function space.
instance Lolli (,) (->) where
  type LolliT (,) (->) a b = a -> b
  lolli _ = id
  {-# INLINE lolli #-}
  eval (a, f) = f a
  {-# INLINE eval #-}
  curry f a b = f (a, b)
  {-# INLINE curry #-}
  uncurry g (a, b) = g a b
  {-# INLINE uncurry #-}

-- ===========================================================================
-- Exponentials (! and ?)
-- ===========================================================================

-- | Exponential modality: object-level types for @!A@ and @?A@.
--
-- The structural rules are split into independent subclasses so that
-- affine and linear uses of the modality differ only in their constraint
-- sets, mirroring the 'Copy'/'Discard' split at the base-arrow level.
--
-- * @!A@ has a contraction half ('BangCopy') and a weakening half
--   ('BangWeaken').  Linear logic requires both; affine logic requires
--   only weakening.
-- * @?A@ currently exposes only its unit rule ('WhyNotIntro'); the ⅋-monoid
--   multiplication on @?A@ ('WhyNotMerge') is missing. In the vocabulary of
--   'Circuit.Dagger', @?A@ is currently 'CoAffine'-only (the unit @Zero@)
--   and the missing half is 'CoRelevant' (the merge @Merge@). That hole is
--   the first observable thing the Exponential split made visible; wiring it
--   is part of the chu-depth class dig.
class (Tensor t arr) => Exponential t arr where
  type Bang t arr a :: Type
  type WhyNot t arr a = result | result -> a

-- | Contraction half of @!A@: copy @!A → !A ⊗ !A@.
class (Exponential t arr) => BangCopy t arr where
  copyE ::
    ( Ob arr a,
      Ob arr (Bang t arr a),
      Ob arr (t (Bang t arr a) (Bang t arr a))
    ) =>
    arr (Bang t arr a) (t (Bang t arr a) (Bang t arr a))

-- | Weakening half of @!A@: dereliction @!A → A@ and discard @!A → I@.
class (Exponential t arr) => BangWeaken t arr where
  discardE ::
    (Ob arr a, Ob arr (Bang t arr a), Ob arr (Unit t)) =>
    arr (Bang t arr a) (Unit t)

  derelict ::
    (Ob arr a, Ob arr (Bang t arr a)) =>
    arr (Bang t arr a) a

-- | Unit rule for @?A@: introduction @A → ?A@.
class (Exponential t arr) => WhyNotIntro t arr where
  introduce ::
    (Ob arr a, Ob arr (WhyNot t arr a)) =>
    arr a (WhyNot t arr a)

-- | The ⅋-monoid structure on @?A@.
--
-- Dual to the @!@-comonoid ('BangCopy' / 'BangWeaken'), but living on the
-- par product rather than the tensor product. 'mergeE' is the
-- multiplication @?A ⅋ ?A → ?A@ and 'zeroE' is the unit @⊥ → ?A@.
class (Exponential t arr, Par p arr) => WhyNotMonoid t p arr where
  mergeE ::
    ( Ob arr a,
      Ob arr (WhyNot t arr a),
      Ob arr (p (WhyNot t arr a) (WhyNot t arr a))
    ) =>
    arr (p (WhyNot t arr a) (WhyNot t arr a)) (WhyNot t arr a)

  zeroE ::
    (Ob arr a, Ob arr (WhyNot t arr a), Ob arr (Bot p)) =>
    arr (Bot p) (WhyNot t arr a)

-- | Linear @!A@: both contraction and weakening.
type LinearBang t arr = (Exponential t arr, BangCopy t arr, BangWeaken t arr)

-- | Affine @!A@: weakening only.
type AffineBang t arr = (Exponential t arr, BangWeaken t arr)

-- | Relevant @!A@: contraction only.
type RelevantBang t arr = (Exponential t arr, BangCopy t arr)

-- | Cartesian collapse: @!A ≅ A@, and @?A@ is the free monoid of lists.
instance Exponential (,) (->) where
  type Bang (,) (->) a = a
  type WhyNot (,) (->) a = [a]

instance BangCopy (,) (->) where
  copyE x = (x, x)
  {-# INLINE copyE #-}

instance BangWeaken (,) (->) where
  discardE _ = ()
  {-# INLINE discardE #-}
  derelict = id
  {-# INLINE derelict #-}

instance WhyNotIntro (,) (->) where
  introduce x = [x]
  {-# INLINE introduce #-}

instance WhyNotMonoid (,) Either (->) where
  mergeE = either id id
  {-# INLINE mergeE #-}
  zeroE = absurd
  {-# INLINE zeroE #-}
