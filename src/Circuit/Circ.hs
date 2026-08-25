{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Loose bicategory of 'Circuit.Body.Body' values with varying carriers.
--
-- A KSW loose 1-cell is a body @arr (t ch a) (t ch b)@ with its carrier @ch@
-- hidden.  The 2-cells are carrier intertwiners: maps @α : ch -> ch'@ that make
-- the Mealy square commute.  'Body' is the fibre at fixed carrier; 'Circ' is
-- the coproduct of those fibres, and 'Sq' / 'Intertwiner' move between them.
--
-- == Carrier-tensoring composition
--
-- @cascade@ composes two bodies whose carriers are tensored:
--
-- @
--   f :: Body t ch  arr a b
--   g :: Body t ch' arr b c
--   cascade g f :: Circ t arr a c   -- carrier  t ch ch'
-- @
--
-- The composite is
--
-- @
--   assoc .> slide .> strength f .> slide .> strength g .> assoc'
-- @
--
-- using 'Circuit.Channel.assoc', 'assoc'', 'slide' and 'strength'.  No
-- braiding/'Action' is needed because 'slide' already swaps the second carrier
-- past the payload.
--
-- == Law witnesses
--
-- The bicategory laws hold only up to invertible 'Sq' witnesses: carriers
-- @ch ⊗ (ch' ⊗ ch'')@ and @(ch ⊗ ch') ⊗ ch''@ are different Haskell types, so
-- on-the-nose associativity is impossible.  The proof artifact is the
-- intertwiner itself; the falsification artifact is observational, via the
-- pointed specialisation 'cascadeSome' and 'Circuit.Body.runSomeBody'.
module Circuit.Circ
  ( -- * Loose 1-cell (carrier hidden)
    Circ (..),
    idCirc,

    -- * Indexed 2-cell (carrier map + commuting square)
    Sq (..),
    idSq,
    vcomp,

    -- * Existential closure of Sq
    Intertwiner (..),

    -- * The two paths whose equality is the square
    downThenAcross,
    acrossThenDown,

    -- * Carrier-tensoring composition
    cascade,
    cascadeBody,
    cascadeSome,

    -- * Horizontal 2-cell algebra
    rightWhisker,
    leftWhisker,
    hcompose,
    whiskerSq,
  )
where

import Circuit.Body (Body (..), SomeBody (..))
import Circuit.Category (Category (..), (.>))
import Circuit.Channel (Channel (..), Strength (..))
import Circuit.Tensor (Tensor (..), Unit)
import Prelude hiding (id, (.))

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Circuit.Circ
-- >>> import Circuit.Body (Body (..))

-- | Loose 1-cell: a body with its carrier type hidden.
data Circ t arr a b where
  Circ :: Body t ch arr a b -> Circ t arr a b

-- | Identity loose 1-cell at the tensor unit carrier.
--
-- The carrier is pinned to 'Unit' so that the unit law can be witnessed with
-- the unitor; without the annotation GHC would instantiate the hidden carrier
-- to 'Any'.
idCirc :: forall t arr a. (Strength t arr) => Circ t arr a a
idCirc = Circ (Body id :: Body t (Unit t) arr a a)

-- | Square (indexed 2-cell).  The carrier maps compose; the middle body must
-- match (a caller side condition).
data Sq t arr ch ch' a b = Sq
  { -- | Map between carriers.
    carrierMap :: arr ch ch',
    -- | Source body, over the source carrier.
    sqSrc :: Body t ch arr a b,
    -- | Target body, over the target carrier.
    sqTgt :: Body t ch' arr a b
  }

-- | Identity square on a body.
idSq :: (Category arr) => Body t ch arr a b -> Sq t arr ch ch a b
idSq b = Sq id b b

-- | Vertical composition of squares.
--
-- The middle body must match; this is a caller side condition.
vcomp ::
  (Category arr) =>
  Sq t arr ch' ch'' a b ->
  Sq t arr ch ch' a b ->
  Sq t arr ch ch'' a b
vcomp g f = Sq (carrierMap f .> carrierMap g) (sqSrc f) (sqTgt g)

-- | Existential closure of 'Sq', for stating "there exists a 2-cell".
data Intertwiner t arr a b where
  Intertwiner :: Sq t arr ch ch' a b -> Intertwiner t arr a b

-- | Go down (carrier map) then across (target body).
--
-- A nondegenerate intertwiner witness: counter state quotiented by parity.
-- These examples exercise both parities and both reset branches.  A paired
-- perturbation doctest on 'acrossThenDown' shows the equality can fail, so
-- these agreement cases are not vacuous.
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', odd n')) :: Body (,) Int (->) Bool Bool
-- >>> let parity = (Body $ \(b, r) -> let b' = if r then False else not b in (b', b')) :: Body (,) Bool (->) Bool Bool
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Bool
-- >>> downThenAcross sq (4, False)
-- (True,True)
-- >>> downThenAcross sq (4, True)
-- (False,False)
-- >>> downThenAcross sq (5, False)
-- (False,False)
downThenAcross ::
  (Tensor t arr) =>
  Sq t arr ch ch' a b ->
  arr (t ch a) (t ch' b)
downThenAcross sq = tensor (carrierMap sq) id .> morphism (sqTgt sq)

-- | Go across (source body) then down (carrier map).
--
-- Agreement cases for the same witness:
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', odd n')) :: Body (,) Int (->) Bool Bool
-- >>> let parity = (Body $ \(b, r) -> let b' = if r then False else not b in (b', b')) :: Body (,) Bool (->) Bool Bool
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Bool
-- >>> acrossThenDown sq (4, False)
-- (True,True)
-- >>> acrossThenDown sq (4, True)
-- (False,False)
-- >>> acrossThenDown sq (5, False)
-- (False,False)
--
-- Perturbation: observe even-ness instead of odd-ness.  The two paths now
-- disagree, which proves the agreement cases above are not vacuous.
--
-- >>> let badCounter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', even n')) :: Body (,) Int (->) Bool Bool
-- >>> let bad = Sq odd badCounter parity :: Sq (,) (->) Int Bool Bool Bool
-- >>> downThenAcross bad (4, False)
-- (True,True)
-- >>> acrossThenDown bad (4, False)
-- (True,False)
acrossThenDown ::
  (Tensor t arr) =>
  Sq t arr ch ch' a b ->
  arr (t ch a) (t ch' b)
acrossThenDown sq = morphism (sqSrc sq) .> tensor (carrierMap sq) id

-- | Carrier-tensoring composition of loose 1-cells.
--
-- The composite has carrier @t ch ch'@ when the first body has carrier @ch@
-- and the second has carrier @ch'@.
cascade ::
  (Strength t arr) =>
  Circ t arr b c ->
  Circ t arr a b ->
  Circ t arr a c
cascade (Circ g) (Circ f) =
  Circ $
    Body
      ( assoc
          .> slide
          .> strength (morphism f)
          .> slide
          .> strength (morphism g)
          .> assoc'
      )

-- | Pointed carrier-tensoring composition for @t = (,)@ and @arr = (->)@.
--
-- This is the specialisation used for observational testing: seeds pair under
-- the tensor, and the composite can be run with 'Circuit.Body.runSomeBody'.
-- It is the pointed counterpart to the unpointed 'cascade'.
cascadeSome ::
  SomeBody (,) (->) b c ->
  SomeBody (,) (->) a b ->
  SomeBody (,) (->) a c
cascadeSome (SomeBody s2 (Body g)) (SomeBody s1 (Body f)) =
  SomeBody (s1, s2) $ Body $ \((s1', s2'), a) ->
    let (s1'', b) = f (s1', a)
        (s2'', c) = g (s2', b)
     in ((s1'', s2''), c)

-- | Compose two bodies at carriers @ch@ and @ch'@ into a body at carrier
-- @t ch ch'@.  This is the body-level building block of 'cascade' and of
-- horizontal 2-cell algebra.
cascadeBody ::
  (Strength t arr) =>
  Body t ch' arr b c ->
  Body t ch arr a b ->
  Body t (t ch ch') arr a c
cascadeBody g f =
  Body
    ( assoc
        .> slide
        .> strength (morphism f)
        .> slide
        .> strength (morphism g)
        .> assoc'
    )

-- | Right whisker: tensor a square with an identity-on-boundaries 1-cell on
-- the right.
rightWhisker ::
  (Tensor t arr, Strength t arr) =>
  Sq t arr ch ch' a b ->
  Body t d arr b c ->
  Sq t arr (t ch d) (t ch' d) a c
rightWhisker sq r =
  Sq
    (tensor (carrierMap sq) id)
    (cascadeBody r (sqSrc sq))
    (cascadeBody r (sqTgt sq))

-- | Left whisker: tensor an identity-on-boundaries 1-cell on the left of a
-- square.
leftWhisker ::
  (Tensor t arr, Strength t arr) =>
  Body t d arr a' a ->
  Sq t arr ch ch' a b ->
  Sq t arr (t d ch) (t d ch') a' b
leftWhisker l sq =
  Sq
    (tensor id (carrierMap sq))
    (cascadeBody (sqSrc sq) l)
    (cascadeBody (sqTgt sq) l)

-- | Horizontal composition of two squares.
hcompose ::
  (Tensor t arr, Strength t arr) =>
  Sq t arr ch2 ch2' b c ->
  Sq t arr ch1 ch1' a b ->
  Sq t arr (t ch1 ch2) (t ch1' ch2') a c
hcompose sq2 sq1 =
  Sq
    (tensor (carrierMap sq1) (carrierMap sq2))
    (cascadeBody (sqSrc sq2) (sqSrc sq1))
    (cascadeBody (sqTgt sq2) (sqTgt sq1))

-- | Boundary whisker: apply tight maps to the input and output boundaries of a
-- square.  This is the `Sq` side of the interchange law; the `Poles` side is
-- `iomap` on the Moore-split representation.
whiskerSq ::
  (Tensor t arr) =>
  arr a' a ->
  arr b b' ->
  Sq t arr ch ch' a b ->
  Sq t arr ch ch' a' b'
whiskerSq f g sq =
  Sq
    (carrierMap sq)
    (Body $ tensor id f .> morphism (sqSrc sq) .> tensor id g)
    (Body $ tensor id f .> morphism (sqTgt sq) .> tensor id g)

-- | 'Category' instance for 'Circ'.
--
-- The laws hold only up to invertible 'Sq': on-the-nose associativity and
-- unitality are impossible as Haskell values because the carriers of the two
-- sides differ.  Observational witnesses live in "Axioma.Circ".
instance (Strength t arr) => Category (Circ t arr) where
  id :: forall a. Circ t arr a a
  id = idCirc
  {-# INLINE id #-}

  (.) :: forall a b c. Circ t arr b c -> Circ t arr a b -> Circ t arr a c
  (.) = cascade
  {-# INLINE (.) #-}
