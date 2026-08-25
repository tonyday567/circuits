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
    withIntertwiner,

    -- * The two paths whose equality is the square
    downThenAcross,
    acrossThenDown,

    -- * Carrier-tensoring composition
    cascade,
    cascadeBody,
    cascadeSome,

    -- * Structural proof witnesses (unitors and associator)
    unitorLeft,
    unitorRight,
    unitorLeftSq,
    unitorRightSq,
    associator,
    associatorSq,

    -- * Feedback (closed loop over a carrier component)
    feedback,

    -- * Bisimulation (behavioural quotient of bodies)
    bisimilarStates,
    isBisimulation,
    maxBisimulation,

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
import Circuit.Tensor (Tensor (..), Unit, unitl, unitr)
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

-- | Eliminator for the existential carrier types of an 'Intertwiner'.
withIntertwiner ::
  Intertwiner t arr a b ->
  (forall ch ch'. Sq t arr ch ch' a b -> r) ->
  r
withIntertwiner (Intertwiner sq) k = k sq

-- | Go down (carrier map) then across (target body).
--
-- A nondegenerate intertwiner witness: counter state quotiented by parity.
-- The payload is 'Char' so the carrier slot and payload slot are type-distinct;
-- slot confusion is a type error.  These examples exercise both parities and
-- both reset branches.  A paired perturbation doctest on 'acrossThenDown'
-- shows the equality can fail, so these agreement cases are not vacuous.
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if odd n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let parity = (Body $ \(b, r) -> let b' = not r && not b in (b', if b' then 'x' else 'y')) :: Body (,) Bool (->) Bool Char
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> downThenAcross sq (4, False)
-- (True,'x')
-- >>> downThenAcross sq (4, True)
-- (False,'y')
-- >>> downThenAcross sq (5, False)
-- (False,'y')
downThenAcross ::
  (Tensor t arr) =>
  Sq t arr ch ch' a b ->
  arr (t ch a) (t ch' b)
downThenAcross sq = tensor (carrierMap sq) id .> morphism (sqTgt sq)

-- | Go across (source body) then down (carrier map).
--
-- Agreement cases for the same witness:
--
-- >>> let counter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if odd n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let parity = (Body $ \(b, r) -> let b' = not r && not b in (b', if b' then 'x' else 'y')) :: Body (,) Bool (->) Bool Char
-- >>> let sq = Sq odd counter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> acrossThenDown sq (4, False)
-- (True,'x')
-- >>> acrossThenDown sq (4, True)
-- (False,'y')
-- >>> acrossThenDown sq (5, False)
-- (False,'y')
--
-- Perturbation: observe even-ness instead of odd-ness.  The two paths now
-- disagree, which proves the agreement cases above are not vacuous.
--
-- >>> let badCounter = (Body $ \(n, r) -> let n' = if r then 0 else n + 1 in (n', if even n' then 'x' else 'y')) :: Body (,) Int (->) Bool Char
-- >>> let bad = Sq odd badCounter parity :: Sq (,) (->) Int Bool Bool Char
-- >>> downThenAcross bad (4, False)
-- (True,'x')
-- >>> acrossThenDown bad (4, False)
-- (True,'y')
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
-- It is the pointed counterpart to the unpointed 'cascade' and is implemented
-- in terms of 'cascadeBody', so tests that exercise it also exercise the same
-- engine used by 'cascade', whiskering, and horizontal composition.
cascadeSome ::
  SomeBody (,) (->) b c ->
  SomeBody (,) (->) a b ->
  SomeBody (,) (->) a c
cascadeSome (SomeBody s2 g) (SomeBody s1 f) =
  SomeBody (s1, s2) (cascadeBody g f)

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

-- | Indexed left unitor square.
unitorLeftSq ::
  (Tensor t arr, Strength t arr) =>
  Body t ch arr a b ->
  Sq t arr (t (Unit t) ch) ch a b
unitorLeftSq b = Sq unitl (cascadeBody b (Body id)) b

-- | Left unitor witness: composing a body with the identity at the unit carrier
-- is isomorphic to the original body.
unitorLeft ::
  (Tensor t arr, Strength t arr) =>
  Body t ch arr a b ->
  Intertwiner t arr a b
unitorLeft b = Intertwiner (unitorLeftSq b)

-- | Indexed right unitor square.
unitorRightSq ::
  (Tensor t arr, Strength t arr) =>
  Body t ch arr a b ->
  Sq t arr (t ch (Unit t)) ch a b
unitorRightSq b = Sq unitr (cascadeBody (Body id) b) b

-- | Right unitor witness.
unitorRight ::
  (Tensor t arr, Strength t arr) =>
  Body t ch arr a b ->
  Intertwiner t arr a b
unitorRight b = Intertwiner (unitorRightSq b)

-- | Indexed associator square.
associatorSq ::
  (Strength t arr) =>
  Body t ch3 arr c d ->
  Body t ch2 arr b c ->
  Body t ch1 arr a b ->
  Sq t arr (t (t ch1 ch2) ch3) (t ch1 (t ch2 ch3)) a d
associatorSq h g f =
  Sq
    assoc
    (cascadeBody h (cascadeBody g f))
    (cascadeBody (cascadeBody h g) f)

-- | Associator witness: carrier bracketing of three composed bodies is
-- isomorphic up to the associator of the tensor.
associator ::
  (Strength t arr) =>
  Body t ch3 arr c d ->
  Body t ch2 arr b c ->
  Body t ch1 arr a b ->
  Intertwiner t arr a d
associator h g f = Intertwiner (associatorSq h g f)

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

-- | Close a feedback loop over a component @s@ of the input/output object.
--
-- The 1-cell must be of the form @Circ t arr (t s a) (t s b)@: the feedback
-- value @s@ appears as the first component of the tensor in both domain and
-- codomain.  The result moves @s@ into the hidden carrier, turning it into
-- state.  This is the guarded / state-bootstrapping feedback of KSW, not the
-- immediate fixed-point trace: yanking fails here, which is the expected
-- behaviour for a feedback category.
--
-- Implemented by reassociating so that @s@ becomes part of the carrier:
--
-- @
--   feedback (Circ (Body f)) = Circ (Body (assoc .> f .> assoc'))
-- @
feedback ::
  (Channel t arr) =>
  Circ t arr (t s a) (t s b) ->
  Circ t arr a b
feedback (Circ (Body f)) = Circ $ Body $ assoc .> f .> assoc'

-- * Bisimulation

-- | Step a @(,) / (->)@ body: given a state and an input, return the next
-- state and output.
stepBody :: Body (,) s (->) a b -> s -> a -> (s, b)
stepBody (Body f) s a = f (s, a)

-- | Check whether a relation is a bisimulation between two finite-state bodies.
--
-- The relation must be over the provided state spaces; the check is exact over
-- the bounded input alphabet.  A relation @R@ is a bisimulation when for every
-- @(s1, s2) ∈ R@ and every input @a@, the outputs coincide and the successor
-- states are again @R@-related.
isBisimulation ::
  (Eq s1, Eq s2, Eq b) =>
  [a] ->
  Body (,) s1 (->) a b ->
  Body (,) s2 (->) a b ->
  [(s1, s2)] ->
  Bool
isBisimulation inputs body1 body2 rel =
  all
    ( \(s1, s2) ->
        all
          ( \a ->
              let (s1', b1) = stepBody body1 s1 a
                  (s2', b2) = stepBody body2 s2 a
               in b1 == b2 && (s1', s2') `elem` rel
          )
          inputs
    )
    rel

-- | Compute the maximal bisimulation between two finite-state bodies over a
-- bounded input alphabet.  The state spaces are supplied explicitly because a
-- 'Body' is a function and does not enumerate its own states.
maxBisimulation ::
  (Eq s1, Eq s2, Eq b) =>
  [a] ->
  [s1] ->
  [s2] ->
  Body (,) s1 (->) a b ->
  Body (,) s2 (->) a b ->
  [(s1, s2)]
maxBisimulation inputs states1 states2 body1 body2 = go initRel
  where
    initRel = [(s1, s2) | s1 <- states1, s2 <- states2]
    go rel =
      let rel' =
            filter
              ( \(s1, s2) ->
                  all
                    ( \a ->
                        let (s1', b1) = stepBody body1 s1 a
                            (s2', b2) = stepBody body2 s2 a
                         in b1 == b2 && (s1', s2') `elem` rel
                    )
                    inputs
              )
              rel
       in if rel' == rel then rel else go rel'

-- | Check whether two specific states are bisimilar.
bisimilarStates ::
  (Eq s1, Eq s2, Eq b) =>
  [a] ->
  [s1] ->
  [s2] ->
  Body (,) s1 (->) a b ->
  Body (,) s2 (->) a b ->
  s1 ->
  s2 ->
  Bool
bisimilarStates inputs states1 states2 body1 body2 s1 s2 =
  (s1, s2) `elem` maxBisimulation inputs states1 states2 body1 body2

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
