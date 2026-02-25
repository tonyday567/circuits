{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE BangPatterns #-}

-- |
-- Module      : Mealy
-- Description : Church-encoded Mealy machine (inject/step/extract) for Traced
--
-- The existential form:
--
-- @
-- data Mealy a b = forall s. Mealy (a -> s) (s -> a -> s) (s -> b)
-- @
--
-- Church-encoded to eliminate the existential:
--
-- @
-- newtype Mealy a b = Mealy (forall r. (forall s. (a -> s) -> (s -> a -> s) -> (s -> b) -> r) -> r)
-- @
--
-- = Difference from MealyM
--
-- In 'MealyM', step is @s -> a -> (b, s)@ — output and state update are
-- simultaneous. A @b@ must be produced whenever an @a@ arrives.
--
-- In 'Mealy', step is @s -> a -> s@ — state updates independently of output.
-- @extract :: s -> b@ can be called at any time, not just on each input.
-- This is the more free expression: output and state are decoupled.
--
-- = Consequences
--
-- * 'Applicative': parallel state composition is clean — two machines share
--   input, states update independently, extract combines at the end.
--   This does not work for 'MealyM' because step forces simultaneous output.
--
-- * 'Category': composition threads @extract@ of the right machine as input
--   to the left, same as 'MealyM'. But state updates are separate.
--
-- * Running: 'scan' emits @extract s@ at every step. 'fold' emits once at
--   the end. Both are valid runners — the machine doesn't privilege either.
--
-- * 'ArrowLoop': the lazy knot works without an initial seed because
--   @inject (a, c0)@ can be tied lazily — @c0 = extract s0@, @s0 = inject (a, c0)@.
--   No @c@ value needed in @Loop@. This is the fix that allows
--   @Loop :: Traced arr (a,c) (b,c) -> Traced arr a b@ without carrying @c@.

module Mealy
  ( Mealy (..)
  , mkMealy
  , withMealy
    -- * Running
  , scan
  , fold
  , scanMaybe
    -- * Instances
    -- * Combinators
  , stateless
  , accum
  , count
  , delay1
  , delay
  ) where

import Prelude hiding (id, (.), scan, fold)
import qualified Prelude

import Data.List (foldl', scanl')
import Control.Category (Category (..))
import Control.Arrow    (Arrow (..), ArrowLoop (..))
import Data.Profunctor  (Profunctor (..), Strong (..))

-- ---------------------------------------------------------------------------
-- The type
-- ---------------------------------------------------------------------------

-- | Church-encoded Mealy machine with decoupled step and extract.
newtype Mealy a b = Mealy
  { runMealy :: forall r. (forall s. (a -> s) -> (s -> a -> s) -> (s -> b) -> r) -> r }

-- | Construct from inject, step, extract.
{-# INLINE mkMealy #-}
mkMealy :: (a -> s) -> (s -> a -> s) -> (s -> b) -> Mealy a b
mkMealy i s e = Mealy (\k -> k i s e)

-- | Eliminate a Mealy.
{-# INLINE withMealy #-}
withMealy :: Mealy a b
          -> (forall s. (a -> s) -> (s -> a -> s) -> (s -> b) -> r)
          -> r
withMealy (Mealy k) f = k f

-- ---------------------------------------------------------------------------
-- Functor, Applicative
-- ---------------------------------------------------------------------------

instance Functor (Mealy a) where
  {-# INLINE fmap #-}
  fmap f m = withMealy m $ \i s e ->
    mkMealy i s (f . e)

-- | Parallel state composition. Both machines see every input independently.
-- Extract combines their outputs at any point.
-- This instance is not available for MealyM because step forces simultaneous output.
instance Applicative (Mealy a) where
  {-# INLINE pure #-}
  pure b = mkMealy (\_ -> ()) (\() _ -> ()) (\() -> b)

  {-# INLINE (<*>) #-}
  mf <*> ma =
    withMealy mf $ \fi fs fe ->
    withMealy ma $ \ai as ae ->
    mkMealy
      (\a        -> (fi a, ai a))
      (\(sf, sa) a -> (fs sf a, as sa a))
      (\(sf, sa)   -> fe sf (ae sa))

-- ---------------------------------------------------------------------------
-- Category
-- ---------------------------------------------------------------------------

-- | Sequential composition. Right machine runs first, extract feeds left inject.
-- State updates are independent; extract is the bridge between stages.
instance Category Mealy where
  {-# INLINE id #-}
  id = mkMealy Prelude.id (\_ a -> a) Prelude.id

  {-# INLINE (.) #-}
  f . g =
    withMealy f $ \fi fs fe ->
    withMealy g $ \gi gs ge ->
    mkMealy
      (\a         -> let !t = gi a;  !s = fi (ge t) in (s, t))
      (\(s, t) a  -> let !t' = gs t a; !s' = fs s (ge t') in (s', t'))
      (\(s, _)    -> fe s)

-- ---------------------------------------------------------------------------
-- Arrow
-- ---------------------------------------------------------------------------

instance Arrow Mealy where
  {-# INLINE arr #-}
  arr f = mkMealy (\_ -> ()) (\() _ -> ()) (\() -> error "Mealy.arr: extract on unit state")

  {-# INLINE first #-}
  first m = withMealy m $ \fi fs fe ->
    mkMealy
      (\(a, c)      -> (fi a, c))
      (\(s, _) (a, c) -> (fs s a, c))
      (\(s, c)      -> (fe s, c))

-- ---------------------------------------------------------------------------
-- ArrowLoop
-- ---------------------------------------------------------------------------

-- | Feedback loop via lazy knot. No initial seed required.
--
-- @inject (a, c0)@ is tied lazily: @c0 = extract s0@, @s0 = inject (a, c0)@.
-- This works because Haskell is lazy and @inject@ does not strictly force @c@
-- before computing @s@. When it does strictly force @c@, a seed is needed —
-- but that is a property of the specific machine, not of @Loop@.
--
-- This is why @Loop :: Traced arr (a,c) (b,c) -> Traced arr a b@ needs no
-- @c@ value: the knot is tied here in the @ArrowLoop@ instance.
instance ArrowLoop Mealy where
  {-# INLINE loop #-}
  loop m = withMealy m $ \fi fs fe ->
    mkMealy
      (\a   -> let s0 = fi (a, c0); c0 = snd (fe s0) in s0)
      (\s a -> let c = snd (fe s);  s' = fs s (a, c)  in s')
      (\s   -> fst (fe s))

-- ---------------------------------------------------------------------------
-- Profunctor, Strong
-- ---------------------------------------------------------------------------

instance Profunctor Mealy where
  {-# INLINE dimap #-}
  dimap f g m = withMealy m $ \i s e ->
    mkMealy (i . f) (\st a -> s st (f a)) (g . e)

instance Strong Mealy where
  {-# INLINE first' #-}
  first' = first

-- ---------------------------------------------------------------------------
-- Running
-- ---------------------------------------------------------------------------

-- | Emit extract at every step. Length-preserving.
{-# INLINE scan #-}
scan :: Mealy a b -> [a] -> [b]
scan _ []     = []
scan m (x:xs) = withMealy m $ \i s e ->
  let !s0 = i x
  in  e s0 : go s e s0 xs
  where
    go _  _  _   []     = []
    go s  e  !st (y:ys) =
      let !st' = s st y
      in  e st' : go s e st' ys

-- | Emit extract once at the end. Consumes the whole list.
{-# INLINE fold #-}
fold :: Mealy a b -> [a] -> Maybe b
fold _ []     = Nothing
fold m (x:xs) = withMealy m $ \i s e ->
  Just (e (foldl' s (i x) xs))

-- | Scan, filtering Nothings. Useful when extract returns Maybe.
{-# INLINE scanMaybe #-}
scanMaybe :: Mealy a (Maybe b) -> [a] -> [b]
scanMaybe m xs = [ b | Just b <- scan m xs ]

-- ---------------------------------------------------------------------------
-- Combinators
-- ---------------------------------------------------------------------------

-- | Stateless function lift.
-- State carries the last output; extract is identity.
{-# INLINE stateless #-}
stateless :: (a -> b) -> Mealy a b
stateless f = mkMealy f (\_ a -> f a) Prelude.id

-- | Running accumulation. State is the accumulated value.
accum :: (a -> a -> a) -> Mealy a a
accum f = mkMealy Prelude.id (flip f) Prelude.id

-- | Count inputs.
count :: Mealy a Int
count = mkMealy (\_ -> 1) (\n _ -> n + 1) Prelude.id

-- | One-step delay. Initial output is the seed value.
-- State is the previous input.
{-# INLINE delay1 #-}
delay1 :: b -> Mealy b b
delay1 b0 = mkMealy (\_ -> b0) (\_ a -> a) Prelude.id

-- | N-step delay. Initial outputs are the seed list.
-- Mirrors Data.Mealy.delay.
delay :: [a] -> Mealy a a
delay xs0 = mkMealy inject step extract
  where
    inject a      = xs0 ++ [a]
    step buf a    = tail buf ++ [a]
    extract []    = error "Mealy.delay: empty buffer"
    extract (x:_) = x
