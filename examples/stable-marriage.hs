{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Stable Marriage via coroutines — the "both at once" pattern.
--
-- From Kidney & Wu, "Hyperfunctions: Communicating Continuations" (POPL 2026, §5.3),
-- itself following Allison (1983). Men and women are independent coroutines that
-- communicate by message-passing. Men propose; women accept or jilt. Jilting wakes
-- a suspended man, who proposes to his next choice. The algorithm runs until all
-- men are engaged.
--
-- The "both at once" aspect: men and women are simultaneous processes. Not
-- sequential pipeline — they run concurrently, with control transferring between
-- coroutines via message sends. When a woman jilts a man, control jumps to that
-- man's coroutine, which resumes proposing. Multiple men can be "in flight."

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (elemIndex, find)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

type Man   = String
type Woman = String

-- | Rankings: each person's ordered preference list.
type Rankings a = Map a [a]

-- | A coroutine: state machine with input i and output o.
--   The state s is internal — each step produces output and new state.
data Coro s i o = Coro
  { coStep :: s -> i -> (o, s)
  , coState :: s
  }

-- | Run a coroutine one step with an input, returning output and updated coroutine.
send :: Coro s i o -> i -> (o, Coro s i o)
send co i = let (o, s') = coStep co (coState co) i
            in (o, co { coState = s' })

-- ---------------------------------------------------------------------------
-- Coroutine definitions
-- ---------------------------------------------------------------------------

-- | A man's coroutine state: remaining women to propose to.
--   Input: () — wake-up signal (he's been jilted or it's his turn).
--   Output: Maybe Woman — who to propose to next (Nothing if list exhausted).
manCoro :: Man -> [Woman] -> Coro [Woman] () (Maybe Woman)
manCoro name prefs = Coro
  { coStep = \remaining () ->
      case remaining of
        []    -> (Nothing, [])
        (w:ws) -> (Just w, ws)
  , coState = prefs
  }

-- | A woman's coroutine state: her current fiancé and her preference list.
--   Input: Man — a suitor proposing.
--   Output: Bool — accept? (also produces side-effect of jilting).
--
--   We encode jilting as a separate output channel: the woman's step returns
--   both the accept/reject decision AND the jilted man (if any).
data WomanState = WomanState
  { wsFiance :: Maybe Man       -- current engagement (Nothing = unengaged)
  , wsRanks  :: [Man]           -- preference list (best first)
  , wsName   :: Woman           -- for display
  }

womanCoro :: Woman -> [Man] -> Coro WomanState Man (Bool, Maybe Man)
womanCoro name ranks = Coro
  { coStep = \st@WomanState{wsFiance, wsRanks} suitor ->
      let rankOf m = elemIndex m wsRanks  -- lower = better
          better a b = case (rankOf a, rankOf b) of
            (Just ra, Just rb) -> ra < rb
            _                  -> False
      in case wsFiance of
        Nothing ->
          -- First proposal: always accept
          ((True, Nothing), st { wsFiance = Just suitor })
        Just current ->
          if better suitor current
            then -- Jilt current, accept suitor
              ((True, Just current), st { wsFiance = Just suitor })
            else -- Reject suitor
              ((False, Nothing), st)
  , coState = WomanState Nothing ranks name
  }

-- ---------------------------------------------------------------------------
-- Scheduler: drives the concurrent coroutine system
-- ---------------------------------------------------------------------------

-- | The system state: all coroutines and current engagements.
data System = System
  { sysMen        :: Map Man (Coro [Woman] () (Maybe Woman))
  , sysWomen      :: Map Woman (Coro WomanState Man (Bool, Maybe Man))
  , sysEngaged    :: Map Woman Man         -- woman → her fiancé
  , sysFreeMen    :: [Man]                 -- men waiting to propose
  , sysPending    :: [Man]                 -- men who were jilted, need to repropose
  , sysLog        :: [String]              -- trace log
  }

-- | Step the system: pick a free man, have him propose, handle the response.
--   Returns updated system and whether any man is still free.
step :: System -> System
step sys@System{sysMen, sysWomen, sysEngaged, sysFreeMen, sysPending, sysLog} =
  let -- Pick next man: pending (jilted) takes priority over free
      (man, newPending, newFree) = case sysPending of
        (m:ps) -> (m, ps, sysFreeMen)           -- from pending: remove head
        []     -> case sysFreeMen of
                    (m:fs) -> (m, [], fs)        -- from free: remove head
                    []     -> error "No free men"
  in case Map.lookup man sysMen of
      Nothing -> sys
      Just manCo ->
        let (mproposal, manCo') = send manCo ()
        in case mproposal of
          Nothing ->
            sys { sysMen     = Map.insert man manCo' sysMen
                , sysFreeMen = newFree
                , sysPending = newPending
                , sysLog     = sysLog ++ [man ++ " has no one left to propose to"]
                }
          Just woman ->
            case Map.lookup woman sysWomen of
              Nothing -> sys
              Just womanCo ->
                let ((accepted, mJilted), womanCo') = send womanCo man
                    logEntry = man ++ " proposes to " ++ woman ++ "; "
                               ++ (if accepted then "accepted" else "rejected")
                               ++ case mJilted of
                                    Just j -> "; jilts " ++ j
                                    Nothing -> ""
                in if accepted
                   then
                     let engagements' = Map.insert woman man sysEngaged
                         -- Jilted man goes to pending; remove from free if present
                         (pending', free') = case mJilted of
                           Just j -> (j : newPending, filter (/= j) newFree)
                           Nothing -> (newPending, newFree)
                     in sys { sysMen     = Map.insert man manCo' sysMen
                            , sysWomen   = Map.insert woman womanCo' sysWomen
                            , sysEngaged = engagements'
                            , sysFreeMen = free'
                            , sysPending = pending'
                            , sysLog     = sysLog ++ [logEntry]
                            }
                   else -- Rejected: man goes back to free men
                     sys { sysMen     = Map.insert man manCo' sysMen
                          , sysWomen   = Map.insert woman womanCo' sysWomen
                          , sysFreeMen = man : newFree  -- back of queue
                          , sysPending = newPending
                          , sysLog     = sysLog ++ [logEntry]
                          }

-- | Run the algorithm to completion or maxSteps.
stableMarriage ::
  Rankings Man   ->
  Rankings Woman ->
  ([String], Map Woman Man)
stableMarriage mranks wranks =
  let men   = Map.keys mranks
      women = Map.keys wranks
      initSys = System
        { sysMen     = Map.fromList [(m, manCoro m (mranks Map.! m)) | m <- men]
        , sysWomen   = Map.fromList [(w, womanCoro w (wranks Map.! w)) | w <- women]
        , sysEngaged = Map.empty
        , sysFreeMen = men
        , sysPending = []
        , sysLog     = []
        }
      go sys | null (sysFreeMen sys) && null (sysPending sys) = sys
             | otherwise = go (step sys)
      final = go initSys
  in (sysLog final, sysEngaged final)

-- ---------------------------------------------------------------------------
-- Test data (from the paper)
-- ---------------------------------------------------------------------------

mranks :: Rankings Man
mranks = Map.fromList
  [ ("Aaron", ["Ciara", "Annie", "Betty"])
  , ("Barry", ["Ciara", "Betty", "Annie"])
  , ("Conor", ["Ciara", "Annie", "Betty"])
  ]

wranks :: Rankings Woman
wranks = Map.fromList
  [ ("Annie", ["Barry", "Conor", "Aaron"])
  , ("Betty", ["Aaron", "Barry", "Conor"])
  , ("Ciara", ["Conor", "Aaron", "Barry"])
  ]

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  let (log, result) = stableMarriage mranks wranks
  putStrLn "=== Trace ==="
  mapM_ putStrLn log
  putStrLn ""
  putStrLn "=== Result ==="
  mapM_ (\(w, m) -> putStrLn (w ++ " ⟜ " ++ m)) (Map.toList result)
  putStrLn ""
  putStrLn "Expected (from paper): [(Annie,Aaron),(Betty,Barry),(Ciara,Conor)]"
