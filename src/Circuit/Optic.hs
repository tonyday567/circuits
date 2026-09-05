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
-- itself.  'OpticP' is the /integrand/ — the residual @ch@ is in the type, so
-- this is the residual-remembering rung.  'Optic' hides it, which is the
-- coend without the quotient.
--
-- == Relationship to the rest of the library
--
-- 'OpticP' is the curried form of 'Circuit.Equip.iomap': a pointed optic is
-- exactly a pair of actions on channel poles, 'opticForwardP' precomposing the
-- conjoint and 'opticBackwardP' postcomposing the companion.  'opticPolesP' is
-- that identification, and it costs nothing to state.
--
-- The objects of the optic category are boundary /pairs/, which the local
-- 'Circuit.Category.Category' class cannot index directly.  "Circuit.Poly"
-- already solves that problem: @'Circuit.Poly.Mono' i o@ packages a boundary
-- pair as a single @Poly@, and @instance Category Morphism@ is the wiki's
-- "category for free".  So this module does not duplicate that instance; it
-- maps into it, with 'opticAsLens', 'lensAsOptic', 'opticAsLensP' and
-- 'lensAsOpticP'.
--
-- == Constraints
--
-- Only 'identityOpticP' needs 'Unital', for the unitors.  Composition and the
-- update action need nothing beyond 'Strength', because
-- @'strength' f == 'Circuit.Tensor.tensor' 'Circuit.Category.id' f@ — a
-- coherence the Axioma oracles check at @(,)@, 'Either' and 'These'.
-- This matters for base arrows that are premonoidal and therefore have
-- 'Strength' but deliberately no 'Tensor' instance, such as @Circuit.Prob@.
module Circuit.Optic
  ( -- * Pointed mixed optic
    OpticP (..),

    -- * Mixed optic with hidden residual
    Optic (..),
    withOptic,

    -- * Pointed composition
    identityOpticP,
    composeOpticP,

    -- * Hidden composition
    identityOptic,
    composeOptic,

    -- * Action on morphisms
    opticUpdateP,
    opticUpdate,

    -- * Action on channel poles
    opticPolesP,

    -- * Bridge to the polynomial lens
    asOptic,
    opticAsLensP,
    opticAsLens,
    lensAsOpticP,
    lensAsOptic,

    -- * Bridge to pointed processes
    processAsLens,
    lensAsProcess,
  )
where

import Circuit.Category (Category, (.>), (<.))
import Circuit.Equip (Poles, iomap)
import Circuit.Poly (Lens, Mono, Morphism, applyLens, lens)
import Circuit.Process (Process (..))
import Circuit.Tensor (Unit, Unital (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Optic
-- >>> import Circuit.Equip (Poles (..))
-- >>> import Circuit.Poly (applyLens)
-- >>> import Prelude hiding (id, (.))
-- >>> :{
-- let firstLens :: OpticP (,) String (->) Int Int (Int, String) (Int, String)
--     firstLens = OpticP (\(n, s) -> (s, n)) (\(s, n) -> (n, s))
--     outer :: OpticP (,) String (->) (Int, Bool) (Int, Bool) ((Int, Bool), String) ((Int, Bool), String)
--     outer = OpticP (\(p, s) -> (s, p)) (\(s, p) -> (p, s))
--     inner :: OpticP (,) Bool (->) Int Int (Int, Bool) (Int, Bool)
--     inner = OpticP (\(n, b) -> (b, n)) (\(b, n) -> (n, b))
--     prismLeft :: OpticP Either String (->) Int Int (Either Int String) (Either Int String)
--     prismLeft =
--       OpticP
--         (\case { Left n -> Right n; Right s -> Left s })
--         (\case { Left s -> Right s; Right n -> Left n })
-- :}

-- | A pointed mixed optic from @(s,r)@ to @(a,b)@ with residual @ch@.
--
-- * @opticForwardP :: arr s (t ch a)@ splits the domain left boundary into the
--   residual and the codomain left boundary.
-- * @opticBackwardP :: arr (t ch b) r@ recombines the residual with the
--   codomain right boundary.
--
-- For @t = (,)@ and @arr = (->)@ this is the concrete lens pair
-- @s -> (ch, a)@ and @(ch, b) -> r@.  For @t = 'Either'@ it is a prism: the
-- residual is the branch that did not match.
data OpticP t ch arr a b s r = OpticP
  { -- | Forward direction: introduce the residual and the codomain left boundary.
    opticForwardP :: arr s (t ch a),
    -- | Backward direction: consume the residual and the codomain right boundary.
    opticBackwardP :: arr (t ch b) r
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
  Optic :: OpticP t ch arr a b s r -> Optic t arr a b s r

-- | Eliminator for the existential residual type.
withOptic ::
  Optic t arr a b s r ->
  (forall ch. OpticP t ch arr a b s r -> x) ->
  x
withOptic (Optic o) k = k o

-- | Identity pointed optic at the boundary pair @(a,b)@.  The residual is the
-- tensor unit.
--
-- This is the only operation in the module that needs 'Unital' rather than
-- 'Strength', and it needs only the unitors.
identityOpticP :: (Unital t arr) => OpticP t (Unit t) arr a b a b
identityOpticP = OpticP unitl' unitl
{-# INLINE identityOpticP #-}

-- | Vertical composition of pointed mixed optics.
--
-- Given @opt1@ from @(s,r)@ to @(a,b)@ with residual @ch1@ and @opt2@ from
-- @(a,b)@ to @(u,v)@ with residual @ch2@, the composite has residual
-- @t ch1 ch2@ — the tensoring of residuals in the coend formula.  The
-- residual order matches 'Circuit.Body.seqCompose': first-applied on the
-- left.
--
-- Note what is /absent/: composition reassociates and applies 'strength', but
-- never 'Circuit.Traced.slide'.  'Circuit.Body.seqCompose' needs two slides,
-- because a single 'Circuit.Body.Body' must push one carrier past the payload
-- so that one arrow sees both.  A pointed optic keeps its two residuals on the
-- same side throughout.  That is the precise sense in which body composition
-- is the fused case of optic composition.
--
-- Unit and associativity hold only up to the residual unitor and associator,
-- exactly as for the squares in "Circuit.Equip"; the observational statements
-- are in @Axioma.Optic@.
--
-- >>> opticUpdateP (composeOpticP inner outer) (+ 1) ((3, True), "hi")
-- ((4,True),"hi")
--
-- The same result by nesting the updates — functoriality of 'opticUpdateP':
--
-- >>> opticUpdateP outer (opticUpdateP inner (+ 1)) ((3, True), "hi")
-- ((4,True),"hi")
composeOpticP ::
  (Strength t arr) =>
  OpticP t ch2 arr u v a b ->
  OpticP t ch1 arr a b s r ->
  OpticP t (t ch1 ch2) arr u v s r
composeOpticP (OpticP f2 b2) (OpticP f1 b1) =
  OpticP
    (f1 .> strength f2 .> assoc')
    (assoc .> strength b2 .> b1)
{-# INLINE composeOpticP #-}

-- | 'identityOpticP' with the residual hidden.
identityOptic :: (Unital t arr) => Optic t arr a b a b
identityOptic = Optic identityOpticP
{-# INLINE identityOptic #-}

-- | 'composeOpticP' with the residuals hidden.  Once hidden, the bracketing
-- that makes 'composeOpticP' associative only up to the associator is no longer
-- observable in the type.
composeOptic ::
  (Strength t arr) =>
  Optic t arr u v a b ->
  Optic t arr a b s r ->
  Optic t arr u v s r
composeOptic (Optic o2) (Optic o1) = Optic (composeOpticP o2 o1)
{-# INLINE composeOptic #-}

-- | Apply a pointed optic to a plain base-arrow morphism.
--
-- A lens turns a focus-update into a whole-update; a prism turns a
-- branch-update into a sum-update.
--
-- >>> opticUpdateP firstLens (+ 1) (3, "hello")
-- (4,"hello")
--
-- >>> (opticUpdateP prismLeft (+ 1) (Left 3), opticUpdateP prismLeft (+ 1) (Right "hi"))
-- (Left 4,Right "hi")
--
-- Lawfulness is not enforced.  @'opticUpdateP' o 'Circuit.Category.id' ==
-- 'Circuit.Category.id'@ is the round-trip condition, and a well-typed optic
-- can fail it; @Axioma.Optic@ carries a witness that it can.
opticUpdateP ::
  (Strength t arr) =>
  OpticP t ch arr a b s r ->
  arr a b ->
  arr s r
opticUpdateP (OpticP f b) m = f .> strength m .> b
{-# INLINE opticUpdateP #-}

-- | 'opticUpdateP' through the existential.
opticUpdate ::
  (Strength t arr) =>
  Optic t arr a b s r ->
  arr a b ->
  arr s r
opticUpdate (Optic o) = opticUpdateP o
{-# INLINE opticUpdate #-}

-- | The action of a pointed optic on channel poles.
--
-- This is 'Circuit.Equip.iomap' with its two arguments read as the legs of an
-- optic: 'opticForwardP' precomposes the conjoint, 'opticBackwardP'
-- postcomposes the companion.  A pointed optic /is/ a morphism of that
-- enriched profunctor.
--
-- >>> let p = Poles fst (\ch -> (ch, 7)) :: Poles String String (->) (->) (String, Int) (String, Int)
-- >>> companion (opticPolesP firstLens p) "hi"
-- (7,"hi")
opticPolesP ::
  (Category arr) =>
  OpticP t ch arr a b s r ->
  Poles ch ch arr arr (t ch a) (t ch b) ->
  Poles ch ch arr arr s r
opticPolesP (OpticP f b) = iomap f b
{-# INLINE opticPolesP #-}

-- | Hide the residual of a pointed optic.
asOptic :: OpticP t ch arr a b s r -> Optic t arr a b s r
asOptic = Optic
{-# INLINE asOptic #-}

-- | A cartesian pointed optic as a polynomial lens.
--
-- Currying the residual away turns the pair @s -> (ch, a)@, @(ch, b) -> r@
-- into @s -> (a, b -> r)@, which is exactly
-- @'Circuit.Poly.applyLens' :: 'Morphism' ('Mono' r s) ('Mono' b a) -> s -> (a, b -> r)@.
--
-- >>> let (a, put) = applyLens (opticAsLensP firstLens) (3, "hello") in (a, put 9)
-- (3,(9,"hello"))
opticAsLensP :: OpticP (,) ch (->) a b s r -> Lens s r a b
opticAsLensP (OpticP f g) =
  lens (\s -> snd (f s)) (\s b -> g (fst (f s), b))

-- | A cartesian optic as a polynomial lens.
opticAsLens :: Optic (,) (->) a b s r -> Lens s r a b
opticAsLens (Optic o) = opticAsLensP o

-- | A polynomial lens as a cartesian pointed optic.
--
-- The residual is reconstructed as the continuation type @b -> r@ — the
-- classical "existential is a function" encoding.  So @'lensAsOpticP'
-- . 'opticAsLensP'@ changes the residual and is only an identity after the
-- coend quotient; @Axioma.Optic@ checks that it is an identity
-- observationally, which is that quotient in action.
lensAsOpticP :: Lens s r a b -> OpticP (,) (b -> r) (->) a b s r
lensAsOpticP m =
  OpticP
    (\s -> let (a, k) = applyLens m s in (k, a))
    (\(k, b) -> k b)

-- | A polynomial lens as a cartesian optic.
lensAsOptic :: Lens s r a b -> Optic (,) (->) a b s r
lensAsOptic = Optic <. lensAsOpticP

-- | A pointed monomial process as a polynomial lens.
processAsLens :: Process s i o -> Lens s s o i
processAsLens pp = lens get put
  where
    get s = processExtract pp s
    put s = processStep pp s

-- | Build a pointed process from a polynomial lens and a seed.
lensAsProcess :: Lens s s o i -> s -> Process s i o
lensAsProcess m s0 =
  Process
    s0
    (\s i -> snd (applyLens m s) i)
    (\s -> fst (applyLens m s))
