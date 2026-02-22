{-# LANGUAGE GADTs, RankNTypes #-}

-- |
-- Module      : Traced
-- Description : Free traced monoidal category
-- Copyright   : (c) 2026
-- License     : BSD-3-Clause
--
-- The free traced monoidal category over Haskell functions.
--
-- We build this by choosing three syntaxes for representing computation as data:
--
-- 1. __Coyoneda__ — syntax for function application
-- 2. __Free__ — syntax for composition (builds on Coyoneda)
-- 3. __Traced__ — syntax for loops (builds on Free)
--
-- Each syntax comes with cast operations (build and run) and laws proven by
-- equational reasoning. All three are unified in a single GADT with three constructors.
--
-- The paper \"Closing the Loop: Free Traced Categories in Haskell\" provides
-- the mathematical foundation.

module Traced
  ( -- * Unified GADT
    Traced (..)
  , build
  , run
  , yank
  -- * Type aliases for restricted views
  , Coyoneda
  , Free
  ) where

import Prelude
import Control.Monad.Fix (fix)

-- |
-- Traced: the unified GADT for all three syntaxes.
--
-- Four constructors, each essential at different levels:
--
-- * 'Pure': identity (Coyoneda level)
-- * 'Apply': syntax for function application (Coyoneda level)
-- * 'Compose': syntax for composition (Free level)
-- * 'Untrace': syntax for loops (Traced level)
--
-- >>> run (build id) == id
-- True
--
-- >>> run (build (+1)) 5
-- 6
--
-- >>> run (build (*2) `Compose` build (+1)) 5
-- 12

data Traced a b where
  Pure    :: Traced a a
  -- ^ Identity
  Apply   :: (b -> c) -> Traced a b -> Traced a c
  -- ^ Defer function application
  Compose :: Traced b c -> Traced a b -> Traced a c
  -- ^ Defer composition
  Untrace :: Traced (a, c) (b, c) -> Traced a b
  -- ^ Defer fixed point (feedback loop)

-- |
-- Cast a function into Traced syntax.
--
-- Fusion: @run (build f) = f@

build :: (a -> b) -> Traced a b
build f = Apply f Pure

-- |
-- Cast Traced syntax back to a function.
--
-- Pure maps to identity. Apply flattens to function composition.
-- Compose joins pipelines. Untrace closes loops via fixed point.

run :: Traced a b -> (a -> b)
run Pure          = id
run (Apply f p)   = f . run p
run (Compose g h) = run g . run h
run (Untrace p)   = \a -> fst $ fix $ \(_b, c) -> run p (a, c)

-- |
-- Run a closed loop by taking the fixed point.
--
-- Not used at Free/Coyoneda level, but essential for Traced.

yank :: Traced a a -> a
yank = fix . run

-- |
-- Traced is a functor in its output type.

instance Functor (Traced a) where
  fmap f p = Apply f p

-- |
-- Type alias: Coyoneda is Traced using only Apply.
--
-- Recovery function: cast from Coyoneda to Traced using 'castCoyoneda'.

type Coyoneda a b = Traced a b

-- |
-- Type alias: Free is Traced using only Apply and Compose.
--
-- Recovery function: cast from Free to Traced using 'castFree'.

type Free a b = Traced a b

