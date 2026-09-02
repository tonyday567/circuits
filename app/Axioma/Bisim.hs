-- | Bisimulation machinery: the behavioural quotient of bodies.
--
-- Oracle infrastructure only — these functions are exercised by the axioma
-- suite and have no library home.
module Axioma.Bisim
  ( stepBody,
    isBisimulation,
    maxBisimulation,
    bisimilarStates,
  )
where

import Circuit.Body (Body (..))

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
