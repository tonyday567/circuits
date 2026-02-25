{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE BangPatterns #-}

-- |
-- Module      : MealyM
-- Description : Church-encoded Mealy machine as base category for Traced
--
-- Church encoding eliminates the existential state type, allowing GHC to
-- inline and specialise the state completely away. The existential version:
--
-- @
-- data MealyM a b = forall s. MealyM (a -> s) (s -> a -> (b, s)) (s -> b)
-- @
--
-- becomes:
--
-- @
-- newtype MealyM a b = MealyM (forall r. (forall s. (a -> s) -> (s -> a -> (b, s)) -> (s -> b) -> r) -> r)
-- @
--
-- The state type @s@ is universally quantified inside the continuation,
-- so it never appears in @MealyM a b@. GHC can inline the continuation at
-- the call site, revealing the concrete state type, and apply worker-wrapper
-- to unbox it.
--
-- The isomorphism with the existential version is exact — same algebra,
-- different representation. The church encoding is the \"continuation-passing\"
-- form of the existential.

module MealyM
  ( MealyM (..)
  , mkMealy
  , withMealy
    -- * Running
  , stepList
  , lastM
    -- * Combinators
  , stateless
  , accum
  , count
  , delay
  ) where

import Prelude hiding (id, (.))
import qualified Prelude

import Data.List (foldl')
import Control.Category (Category (..))
import Control.Arrow    (Arrow (..), ArrowLoop (..))
import Data.Profunctor  (Profunctor (..), Strong (..))

-- ---------------------------------------------------------------------------
-- The type
-- ---------------------------------------------------------------------------

-- | Church-encoded Mealy machine.
-- @MealyM k@ where @k@ is a continuation over the existential state.
-- GHC can inline @k@ at call sites and specialise the state type.
newtype MealyM a b = MealyM
  { runMealyM :: forall r. (forall s. (a -> s) -> (s -> a -> (b, s)) -> (s -> b) -> r) -> r }

-- | Construct from inject, step, extract.
{-# INLINE mkMealy #-}
mkMealy :: (a -> s) -> (s -> a -> (b, s)) -> (s -> b) -> MealyM a b
mkMealy i s e = MealyM (\k -> k i s e)

-- | Eliminate a MealyM.
{-# INLINE withMealy #-}
withMealy :: MealyM a b
          -> (forall s. (a -> s) -> (s -> a -> (b, s)) -> (s -> b) -> r)
          -> r
withMealy (MealyM k) f = k f

-- ---------------------------------------------------------------------------
-- Category
-- ---------------------------------------------------------------------------

instance Category MealyM where
  {-# INLINE id #-}
  id = mkMealy Prelude.id (\_ a -> (a, a)) Prelude.id

  {-# INLINE (.) #-}
  f . g = withMealy f $ \fi fs fe ->
          withMealy g $ \gi gs ge ->
          mkMealy
            (\a       -> let !t = gi a; !b = ge t; !s = fi b in (s, t))
            (\(s,t) a -> let (mid,!t') = gs t a; (out,!s') = fs s mid in (out,(s',t')))
            (\(s,_)   -> fe s)

-- ---------------------------------------------------------------------------
-- Arrow
-- ---------------------------------------------------------------------------

instance Arrow MealyM where
  {-# INLINE arr #-}
  arr f = mkMealy (\_ -> ()) (\() a -> (f a, ())) (\() -> error "MealyM.arr: extract on unit")

  {-# INLINE first #-}
  first m = withMealy m $ \fi fs fe ->
    mkMealy
      (\(a, c)    -> (fi a, c))
      (\(s, _) (a, c) -> let (b, s') = fs s a in ((b, c), (s', c)))
      (\(s, c)    -> (fe s, c))

-- ---------------------------------------------------------------------------
-- ArrowLoop
-- ---------------------------------------------------------------------------

instance ArrowLoop MealyM where
  {-# INLINE loop #-}
  loop m = withMealy m $ \fi fs fe ->
    mkMealy
      (\a   -> let s0 = fi (a, c0); c0 = snd (fe s0) in s0)
      (\s a -> let c = snd (fe s); ((b,_),s') = fs s (a,c) in (b, s'))
      (\s   -> fst (fe s))

-- ---------------------------------------------------------------------------
-- Profunctor, Strong
-- ---------------------------------------------------------------------------

instance Profunctor MealyM where
  {-# INLINE dimap #-}
  dimap f g m = withMealy m $ \fi fs fe ->
    mkMealy (fi . f)
            (\s a -> let (b, s') = fs s (f a) in (g b, s'))
            (g . fe)

instance Strong MealyM where
  {-# INLINE first' #-}
  first' = first

-- ---------------------------------------------------------------------------
-- Running
-- ---------------------------------------------------------------------------

-- | Run a list through a machine.
{-# INLINE stepList #-}
stepList :: MealyM a b -> [a] -> [b]
stepList m []     = []
stepList m (x:xs) = withMealy m $ \fi fs fe ->
  let !s0 = fi x
  in  fe s0 : go fs fe s0 xs
  where
    go _  _  _  []     = []
    go fs fe !s (y:ys) =
      let (b, !s') = fs s y
      in  b : go fs fe s' ys

-- | Run a list, return only the final value.
{-# INLINE lastM #-}
lastM :: MealyM a b -> [a] -> Maybe b
lastM _ []     = Nothing
lastM m (x:xs) = withMealy m $ \fi fs fe ->
  Just (fe (foldl' (\s a -> snd (fs s a)) (fi x) xs))

-- ---------------------------------------------------------------------------
-- Combinators
-- ---------------------------------------------------------------------------

-- | Stateless function lift.
{-# INLINE stateless #-}
stateless :: (a -> b) -> MealyM a b
stateless = arr

-- | Running accumulation.
accum :: (a -> a -> a) -> MealyM a a
accum f = mkMealy Prelude.id (\s a -> let s' = f s a in (s', s')) Prelude.id

-- | Count inputs.
count :: MealyM a Int
count = mkMealy (\_ -> 1) (\n _ -> (n+1, n+1)) Prelude.id

-- | One-step delay initialised to b.
{-# INLINE delay #-}
delay :: b -> MealyM b b
delay b = mkMealy (\_ -> b) (\_ a -> (a, a)) Prelude.id
