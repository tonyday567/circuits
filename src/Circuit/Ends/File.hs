{-# LANGUAGE OverloadedStrings #-}

-- | File channels as free 'In'/'Out' ends.
--
-- Two independent 'openFileEnds' introductions, composed with 'par'
-- (independence), crossed with 'swap', grounded with 'openK' + unitors.
-- The whole program is:
--
-- @
--   Trace (,) (Kleisli IO) () ()
-- @
--
-- Run once with @runKleisli (run prog) ()@.
module Circuit.Ends.File
  ( openFileEnds,
    exchangeFiles,
    runExchange,
  )
where

import Circuit.Classes ((>>>))
import Circuit.Ends (openK)
import Circuit.Layer (run)
import Circuit.Monoidal (Action (..), Tensor (..))
import Circuit.Trace (In (..), Out (..), Trace (..), runIn, runOut)
import Control.Arrow (Kleisli (..), runKleisli)
import System.IO (IOMode (..), hGetContents, hClose, openFile)
import Prelude

-- | Strict 'readFile' (lazy handle + later 'writeFile' deadlocks).
readFileStrict :: FilePath -> IO String
readFileStrict path = do
  h <- openFile path ReadMode
  s <- hGetContents h
  length s `seq` hClose h
  pure s

-- | Extrinsic free ends for one file path (same shape as 'openSTM').
--
-- * 'Out' — read whole file contents
-- * 'In' — write whole file, then continue through the opposing 'Out'
openFileEnds :: FilePath -> IO (Out (Kleisli IO) (,) String, In (Kleisli IO) (,) String)
openFileEnds path = pure (outH, inH)
  where
    outH = Out $ \_ -> Arr (Kleisli $ \_ -> readFileStrict path)
    inH =
      In $ \o ->
        Arr
          ( Kleisli $ \bs -> do
              writeFile path bs
              runKleisli (run (runIn o inH)) bs
          )

-- | Swap contents of two files as one monoidal program.
--
-- Two separate 'openFileEnds' + two 'openK' unit pairs: independence is
-- 'par', not sequential @>>>@ alone. The structure:
--
-- >   unitl'
-- >     >>> par (read A) (read B)     -- independent opens, side by side
-- >     >>> swap
-- >     >>> par (write A) (write B)   -- cross: each In gets the other file's Out
-- >     >>> unitl
exchangeFiles ::
  FilePath ->
  FilePath ->
  IO (Trace (,) (Kleisli IO) () ())
exchangeFiles pathA pathB = do
  (outA, inA) <- openFileEnds pathA
  (outB, inB) <- openFileEnds pathB
  let (outU1, inU1) = openK ()
      (outU2, inU2) = openK ()
      -- () → ((), ())
      intro = unitl' :: Trace (,) (Kleisli IO) () ((), ())
      -- independent harvests (par = independence)
      harvest =
        par
          (runIn outA inU1)
          (runIn outB inU2)
      -- cross: after swap, write each file with the other's contents
      feed =
        par
          (runOut inA outU1)
          (runOut inB outU2)
      -- ((), ()) → ()
      elim = unitl :: Trace (,) (Kleisli IO) ((), ()) ()
  pure $
    intro
      >>> harvest
      >>> swap
      >>> feed
      >>> elim

-- | Open, build 'exchangeFiles', run once.
runExchange :: FilePath -> FilePath -> IO ()
runExchange pathA pathB = do
  prog <- exchangeFiles pathA pathB
  runKleisli (run prog) ()