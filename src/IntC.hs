{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module IntC where

import Prelude hiding (id, (.))
import Control.Category (Category(..))
import Data.Tuple (swap)
import Traced (Trace (..), Traced, TracedA (..), run)

-- ---------------------------------------------------------------------------
-- § 1. Morphisms
--
-- A morphism (a,c) → (b,d) in Int(TracedA) is a C-term
--     f :: Traced (a, d) (b, c)
-- i.e., given positive input a and negative input d,
--       produce positive b and negative c.
-- ---------------------------------------------------------------------------

newtype IntC a c b d = IntC { unIntC :: Traced (a, d) (b, c) }

-- ---------------------------------------------------------------------------
-- § 2. Identity and composition
-- ---------------------------------------------------------------------------

-- Identity on (a, c)
intId :: IntC a c a c
intId = IntC (Lift id)

-- Composition in Int(C).
--
-- f : (a,b) → (c,d)  witnessed by  Traced (a, d) (c, b)
-- g : (c,d) → (e,fv) witnessed by  Traced (c, fv) (e, d)
-- h : (a,b) → (e,fv) witnessed by  Traced (a, fv) (e, b)
--
-- We must run f and g at the base level to produce the loop function
-- that Knot wraps. The Knot traces out the shared channel d.
intCompose
  :: forall a b c d e fv.
     IntC a b c d   -- f: (a,b) → (c,d)
  -> IntC c d e fv  -- g: (c,d) → (e,fv)
  -> IntC a b e fv  -- h: (a,b) → (e,fv)
intCompose (IntC f) (IntC g) = IntC $ Knot loop
  where
    rf :: (a, d) -> (c, b)
    rf = run f
    rg :: (c, fv) -> (e, d)
    rg = run g
    loop :: (d, (a, fv)) -> (d, (e, b))
    loop (d, (av, fv)) =
      let (c, b)  = rf (av, d)
          (e, d') = rg (c, fv)
      in  (d', (e, b))

-- ---------------------------------------------------------------------------
-- § 3. Dual object
-- ---------------------------------------------------------------------------

-- Dual of (a, c) is (c, a): flip positive and negative.
-- A morphism (a,c)→(b,d) dualises to (d,b)→(c,a),
-- witnessed by swapping both input and output pairs.

dualMorph :: IntC a c b d -> IntC d b c a
dualMorph (IntC f) = IntC $ Lift swap `Compose` f `Compose` Lift swap

-- ---------------------------------------------------------------------------
-- § 4. Cup and cap
-- ---------------------------------------------------------------------------

-- cup η : () → (a, a) in Int(C)
-- Witnessed by Traced () (a, a).
-- Knot traces out the shared a channel, lazily tying x = x.
cup :: Traced () (a, a)
cup = Knot loop
  where
    loop :: (a, ()) -> (a, (a, a))
    loop (x, ()) = (x, (x, x))

-- cap ε : (a, a) → () in Int(C)
-- Witnessed by Traced (a, a) ().
cap :: Traced (a, a) ()
cap = Lift (const ())

-- ---------------------------------------------------------------------------
-- § 5. Embedding TracedA → Int(TracedA)
-- ---------------------------------------------------------------------------

-- Sends f :: Traced a b to the IntC morphism (a, ()) → (b, ()),
-- witnessed by Traced (a, ()) (b, ()).

embed :: Traced a b -> IntC a () b ()
embed f = IntC $ Lift (\(a, ()) -> (run f a, ()))

-- ---------------------------------------------------------------------------
-- § 6. Smoke test
-- ---------------------------------------------------------------------------

-- | Composition of identity morphisms in Int(C) preserves type shape.
-- >>> :type testIdType
-- testIdType :: IntC Int () Int ()
testIdType :: IntC Int () Int ()
testIdType = intCompose intId intId

-- | Embed two morphisms (+1) and (-1) into Int(C) and compose them.
-- The composition should act as identity on the base value.
-- >>> testEmbed 5
-- (5,())
-- >>> testEmbed 0
-- (0,())
-- >>> testEmbed (-3)
-- (-3,())
testEmbed :: Int -> (Int, ())
testEmbed n = run (unIntC (intCompose (embed (Lift (+1))) (embed (Lift (subtract 1))))) (n, ())

