-- | Mixed optics as residual maps.
--
-- In the equipment-optics story an optic between two spans with common
-- boundaries is a globular 2-cell between the corresponding loose arrows.  In
-- @Prof@ that unwinds to the mixed-optic coend
--
-- @
--   Optic_M((S,R),(A,B)) = ∫^M C(S, M ⊙ A) × D(M ⊙ B, R)
-- @
--
-- where @⊙@ is a monoidal action.  In @circuits@ the action is the tensor @t@
-- itself.  'POptic' is the /integrand/ — the residual @ch@ is in the type, so
-- this is the residual-remembering rung.  'Optic' hides it, which is the
-- coend without the quotient.
--
-- == Relationship to the rest of the library
--
-- 'POptic' is the curried form of 'Circuit.Equip.iomap': a pointed optic is
-- exactly a pair of actions on channel poles, 'popticForward' precomposing the
-- conjoint and 'popticBackward' postcomposing the companion.  'popticPoles' is
-- that identification, and it costs nothing to state.
--
-- The objects of the optic category are boundary /pairs/, which the local
-- 'Circuit.Category.Category' class cannot index directly.  "Circuit.Poly"
-- already solves that problem: @'Circuit.Poly.Mono' i o@ packages a boundary
-- pair as a single @Poly@, and @instance Category Morphism@ is the wiki's
-- "category for free".  So this module does not duplicate that instance; it
-- maps into it, with 'opticAsLens', 'lensAsOptic', 'popticAsLens' and
-- 'lensAsPOptic'.
--
-- == Constraints
--
-- Only 'identityPOptic' needs 'Unital', for the unitors.  Composition and the
-- update action need nothing beyond 'Strength', because
-- @'strength' f == 'Circuit.Tensor.tensor' 'Circuit.Category.id' f@ — a
-- coherence the @Axioma.Cell@ oracles check at @(,)@, 'Either' and 'These'.
-- This matters for base arrows that are premonoidal and therefore have
-- 'Strength' but deliberately no 'Tensor' instance, such as @Circuit.Prob@.
module Circuit.Optic
  ( -- * Pointed mixed optic
    POptic (..),

    -- * Mixed optic with hidden residual
    Optic (..),
    withOptic,

    -- * Pointed composition
    identityPOptic,
    composePOptic,

    -- * Hidden composition
    identityOptic,
    composeOptic,

    -- * Action on morphisms
    popticUpdate,
    opticUpdate,

    -- * Action on channel poles
    popticPoles,

    -- * Bridge to the polynomial lens
    asOptic,
    popticAsLens,
    opticAsLens,
    lensAsPOptic,
    lensAsOptic,

    -- * Bridge to pointed processes
    pprocessAsLens,
    lensAsPProcess,
  )
where

import Circuit.Category (Category, (.>), (<.))
import Circuit.Equip (Poles, iomap)
import Circuit.Poly (Lens, Mono, Morphism, applyLens, lens)
import Circuit.Process (PProcess (..))
import Circuit.Tensor (Unit, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Optic
-- >>> import Circuit.Equip (Poles (..))
-- >>> import Circuit.Poly (applyLens)
-- >>> import Prelude hiding (id, (.))
-- >>> :{
-- let firstLens :: POptic (,) String (->) Int Int (Int, String) (Int, String)
--     firstLens = POptic (\(n, s) -> (s, n)) (\(s, n) -> (n, s))
--     outer :: POptic (,) String (->) (Int, Bool) (Int, Bool) ((Int, Bool), String) ((Int, Bool), String)
--     outer = POptic (\(p, s) -> (s, p)) (\(s, p) -> (p, s))
--     inner :: POptic (,) Bool (->) Int Int (Int, Bool) (Int, Bool)
--     inner = POptic (\(n, b) -> (b, n)) (\(b, n) -> (n, b))
--     prismLeft :: POptic Either String (->) Int Int (Either Int String) (Either Int String)
--     prismLeft =
--       POptic
--         (\case { Left n -> Right n; Right s -> Left s })
--         (\case { Left s -> Right s; Right n -> Left n })
-- :}

-- | A pointed mixed optic from @(s,r)@ to @(a,b)@ with residual @ch@.
--
-- * @popticForward :: arr s (t ch a)@ splits the domain left boundary into the
--   residual and the codomain left boundary.
-- * @popticBackward :: arr (t ch b) r@ recombines the residual with the
--   codomain right boundary.
--
-- For @t = (,)@ and @arr = (->)@ this is the concrete lens pair
-- @s -> (ch, a)@ and @(ch, b) -> r@.  For @t = 'Either'@ it is a prism: the
-- residual is the branch that did not match.
data POptic t ch arr a b s r = POptic
  { -- | Forward direction: introduce the residual and the codomain left boundary.
    popticForward :: arr s (t ch a),
    -- | Backward direction: consume the residual and the codomain right boundary.
    popticBackward :: arr (t ch b) r
  }

-- | A mixed optic with the residual existentially hidden.
--
-- There is no residual /value/ here, only a residual type: the forward leg
-- produces the residual and the backward leg consumes it.  This is why
-- 'Optic' is cheaper than an existential body wrapper, which would have to
-- store a seed and therefore has no inhabitant at tensors with an uninhabited
-- unit.  'identityOptic' exists at 'Either', where
-- @'Circuit.Tensor.Unit' 'Either' = 'Data.Void.Void'@ and the corresponding
-- pointed-body identity does not.
data Optic t arr a b s r where
  Optic :: POptic t ch arr a b s r -> Optic t arr a b s r

-- | Eliminator for the existential residual type.
withOptic ::
  Optic t arr a b s r ->
  (forall ch. POptic t ch arr a b s r -> x) ->
  x
withOptic (Optic o) k = k o

-- | Identity pointed optic at the boundary pair @(a,b)@.  The residual is the
-- tensor unit.
--
-- This is the only operation in the module that needs 'Unital' rather than
-- 'Strength', and it needs only the unitors.
identityPOptic :: (Unital t arr) => POptic t (Unit t) arr a b a b
identityPOptic = POptic unitl' unitl
{-# INLINE identityPOptic #-}

-- | Vertical composition of pointed mixed optics.
--
-- Given @opt1@ from @(s,r)@ to @(a,b)@ with residual @ch1@ and @opt2@ from
-- @(a,b)@ to @(u,v)@ with residual @ch2@, the composite has residual
-- @t ch1 ch2@ — the tensoring of residuals in the coend formula.  The
-- residual order matches 'Circuit.Body.mergeChannel': first-applied on the
-- left.
--
-- Note what is /absent/: composition reassociates and applies 'strength', but
-- never 'Circuit.Traced.slide'.  'Circuit.Body.mergeChannel' needs two slides,
-- because a single 'Circuit.Body.Body' must push one carrier past the payload
-- so that one arrow sees both.  A pointed optic keeps its two residuals on the
-- same side throughout.  That is the precise sense in which body composition
-- is the fused case of optic composition.
--
-- Unit and associativity hold only up to the residual unitor and associator,
-- exactly as for the squares in "Circuit.Equip"; the observational statements
-- are in @Axioma.Optic@.
--
-- >>> popticUpdate (composePOptic inner outer) (+ 1) ((3, True), "hi")
-- ((4,True),"hi")
--
-- The same result by nesting the updates — functoriality of 'popticUpdate':
--
-- >>> popticUpdate outer (popticUpdate inner (+ 1)) ((3, True), "hi")
-- ((4,True),"hi")
composePOptic ::
  (Strength t arr) =>
  POptic t ch2 arr u v a b ->
  POptic t ch1 arr a b s r ->
  POptic t (t ch1 ch2) arr u v s r
composePOptic (POptic f2 b2) (POptic f1 b1) =
  POptic
    (f1 .> strength f2 .> assoc')
    (assoc .> strength b2 .> b1)
{-# INLINE composePOptic #-}

-- | 'identityPOptic' with the residual hidden.
identityOptic :: (Unital t arr) => Optic t arr a b a b
identityOptic = Optic identityPOptic
{-# INLINE identityOptic #-}

-- | 'composePOptic' with the residuals hidden.  Once hidden, the bracketing
-- that makes 'composePOptic' associative only up to the associator is no longer
-- observable in the type.
composeOptic ::
  (Strength t arr) =>
  Optic t arr u v a b ->
  Optic t arr a b s r ->
  Optic t arr u v s r
composeOptic (Optic o2) (Optic o1) = Optic (composePOptic o2 o1)
{-# INLINE composeOptic #-}

-- | Apply a pointed optic to a plain base-arrow morphism.
--
-- A lens turns a focus-update into a whole-update; a prism turns a
-- branch-update into a sum-update.
--
-- >>> popticUpdate firstLens (+ 1) (3, "hello")
-- (4,"hello")
--
-- >>> (popticUpdate prismLeft (+ 1) (Left 3), popticUpdate prismLeft (+ 1) (Right "hi"))
-- (Left 4,Right "hi")
--
-- Lawfulness is not enforced.  @'popticUpdate' o 'Circuit.Category.id' ==
-- 'Circuit.Category.id'@ is the round-trip condition, and a well-typed optic
-- can fail it; @Axioma.Optic@ carries a witness that it can.
popticUpdate ::
  (Strength t arr) =>
  POptic t ch arr a b s r ->
  arr a b ->
  arr s r
popticUpdate (POptic f b) m = f .> strength m .> b
{-# INLINE popticUpdate #-}

-- | 'popticUpdate' through the existential.
opticUpdate ::
  (Strength t arr) =>
  Optic t arr a b s r ->
  arr a b ->
  arr s r
opticUpdate (Optic o) = popticUpdate o
{-# INLINE opticUpdate #-}

-- | The action of a pointed optic on channel poles.
--
-- This is 'Circuit.Equip.iomap' with its two arguments read as the legs of an
-- optic: 'popticForward' precomposes the conjoint, 'popticBackward'
-- postcomposes the companion.  A pointed optic /is/ a morphism of that
-- enriched profunctor.
--
-- >>> let p = Poles fst (\ch -> (ch, 7)) :: Poles String String (->) (String, Int) (String, Int)
-- >>> companion (popticPoles firstLens p) "hi"
-- (7,"hi")
popticPoles ::
  (Category arr) =>
  POptic t ch arr a b s r ->
  Poles ch ch arr (t ch a) (t ch b) ->
  Poles ch ch arr s r
popticPoles (POptic f b) = iomap f b
{-# INLINE popticPoles #-}

-- | Hide the residual of a pointed optic.
asOptic :: POptic t ch arr a b s r -> Optic t arr a b s r
asOptic = Optic
{-# INLINE asOptic #-}

-- | A cartesian pointed optic as a polynomial lens.
--
-- Currying the residual away turns the pair @s -> (ch, a)@, @(ch, b) -> r@
-- into @s -> (a, b -> r)@, which is exactly
-- @'Circuit.Poly.applyLens' :: 'Morphism' ('Mono' r s) ('Mono' b a) -> s -> (a, b -> r)@.
--
-- >>> let (a, put) = applyLens (popticAsLens firstLens) (3, "hello") in (a, put 9)
-- (3,(9,"hello"))
popticAsLens :: POptic (,) ch (->) a b s r -> Lens s r a b
popticAsLens (POptic f g) =
  lens (\s -> snd (f s)) (\s b -> g (fst (f s), b))

-- | A cartesian optic as a polynomial lens.
opticAsLens :: Optic (,) (->) a b s r -> Lens s r a b
opticAsLens (Optic o) = popticAsLens o

-- | A polynomial lens as a cartesian pointed optic.
--
-- The residual is reconstructed as the continuation type @b -> r@ — the
-- classical "existential is a function" encoding.  So @'lensAsPOptic'
-- . 'popticAsLens'@ changes the residual and is only an identity after the
-- coend quotient; @Axioma.Optic@ checks that it is an identity
-- observationally, which is that quotient in action.
lensAsPOptic :: Lens s r a b -> POptic (,) (b -> r) (->) a b s r
lensAsPOptic m =
  POptic
    (\s -> let (a, k) = applyLens m s in (k, a))
    (\(k, b) -> k b)

-- | A polynomial lens as a cartesian optic.
lensAsOptic :: Lens s r a b -> Optic (,) (->) a b s r
lensAsOptic = Optic <. lensAsPOptic

-- | A pointed monomial process as a polynomial lens.
pprocessAsLens :: PProcess s i o -> Lens s s o i
pprocessAsLens pp = lens get put
  where
    get s = pprocessExtract pp s
    put s = pprocessStep pp s

-- | Build a pointed process from a polynomial lens and a seed.
lensAsPProcess :: Lens s s o i -> s -> PProcess s i o
lensAsPProcess m s0 =
  PProcess
    s0
    (\s i -> snd (applyLens m s) i)
    (\s -> fst (applyLens m s))
