{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

-- |
-- Module      : LexerK
-- Description : Markup lexer via Traced (Kleisli (State AccState))
--
-- Same pipeline as runMarkupStateBS but stages are
-- Kleisli (State AccState) morphisms rather than plain functions.
--
-- Demonstrates:
-- 1. Traced (Kleisli m) works for any Monad m with Category + Costrong
-- 2. Same Traced description, different run target
-- 3. State threading via the monad, not the output type
-- 4. No Loop needed — AccState carries MarkupCtx

module LexerK
  ( runMarkupKleisliBS
  ) where

import Prelude hiding (id, (.))

import Control.Monad.State.Strict (State, evalState, state)

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BSU

import Lexer  ( WI (..), AccState (..), MarkupToken (..), ByteClass
              , accumStep, classifyByte, MarkupCtx (..) )

-- ---------------------------------------------------------------------------
-- Pipeline as direct State operations (no Kleisli wrapper)
-- ---------------------------------------------------------------------------

-- | Compiled step: fuse the pipeline directly as a State function.
-- Using the `state` constructor to wrap the stateful computation.
{-# INLINE stepMarkupK #-}
stepMarkupK :: WI -> State AccState (Maybe (ByteString -> MarkupToken, Int, Int))
stepMarkupK (WI w i) = state $ \acc ->
  let !bc = classifyByte (accCtx acc) w
      (emit, !acc') = accumStep acc bc i
  in  (emit, acc')

-- ---------------------------------------------------------------------------
-- Runner
-- ---------------------------------------------------------------------------

runMarkupKleisliBS :: ByteString -> [MarkupToken]
runMarkupKleisliBS bs
  | BS.null bs = []
  | otherwise  = evalState (go 0 bs) (AccState 0 0 InContent)
  where
    go !i bs'
      | BS.null bs' = pure []
      | otherwise   = do
          let !w = BSU.unsafeHead bs'
          mEmit <- stepMarkupK (WI w i)
          rest  <- go (i+1) (BSU.unsafeTail bs')
          pure $ case mEmit of
            Nothing                -> rest
            Just (con, start, len) ->
              mkTok con start len : rest

    mkTok con start len
      | len == 0  = con BS.empty
      | otherwise = con (BSU.unsafeTake len (BSU.unsafeDrop start bs))
