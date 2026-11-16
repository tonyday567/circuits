-- | Postal structure, ancestry, delivery, and receipt oracles.
module Axioma.Post
  ( postTopic,
  )
where

import Axioma.Common (Verbosity, checkV)
import Circuit.Post
import Circuit.Shared (Stamped (..))
import Circuit.Stream (These (..))
import Data.Map qualified as Map
import Data.Maybe (isNothing)

p0, p1 :: Post String String
p0 = mkPost "alice" ["bob"] "zero"
p1 = mkPost "bob" ["alice", "carol"] "one"

r1, r2 :: Post String String
r1 = replyTo "carol" 1 p1 "reply"
r2 = replyTo "alice" 2 r1 "next"

cycle0, cycle1 :: Post String ()
cycle0 = (mkPost "a" [] ()) {thread = [1]}
cycle1 = (mkPost "b" [] ()) {thread = [0]}

postTopic :: Verbosity -> IO [Bool]
postTopic verbosity =
  sequence
    [ checkV
        verbosity
        "only the root constructors are parentless; replies and syntheses cite exact ids"
        ( let channelRoot = mkChannelPost "alice" "room" ["bob"] () :: Post String ()
              reply = replyTo "bob" 3 channelRoot ()
              merged = synthesis "sum" [] [2, 0, 2] ()
           in isNothing (channel p0)
                && channel channelRoot == Just "room"
                && to channelRoot == ["bob"]
                && null (thread p0)
                && null (thread channelRoot)
                && thread reply == [3]
                && thread merged == [0, 2]
        ),
      checkV
        verbosity
        "a reply cites its parent, inherits its channel, and readdresses its audience"
        ( let parent = mkChannelPost "alice" "room" ["bob", "carol"] "parent"
              reply = replyTo "bob" 4 parent "reply"
           in thread reply == [4]
                && channel reply == Just "room"
                && to reply == ["alice", "carol"]
        ),
      checkV
        verbosity
        "synthesis normalises parents and carries no channel"
        ( thread (synthesis "sum" ["audience"] [3, 1, 3, 2] ()) == [1, 2, 3]
            && isNothing (channel (synthesis "sum" [] [0] ()))
        ),
      checkV
        verbosity
        "branches unfolds exact parent ids in normalised order"
        ( branchesByIndex [p0, p1] r1 == [["carol", "bob"]]
            && branchesByIndex [p0, p1, r1] r2 == [["alice", "carol", "bob"]]
        ),
      checkV
        verbosity
        "exact ids resolve in an explicit map; positions are a separate convenience"
        ( let seed = mkPost "a" [] (1 :: Int) :: Post String Int
              second = mkPost "b" [] (2 :: Int)
              sparse = Map.fromList [(10, seed), (11, second)]
              byId = (mkPost "c" [] 0) {thread = [11]}
              byPosition = (mkPost "c" [] 0) {thread = [1]}
           in branches sparse byId == [["c", "b"]]
                && null (branches sparse byPosition)
                && branchesByIndex [seed, second] byPosition == [["c", "b"]]
                && null (branchesByIndex [seed, second] byId)
        ),
      checkV
        verbosity
        "cone resolves senders by id, and coneByIndex resolves by position"
        ( let seed = mkPost "a" [] (1 :: Int) :: Post String Int
              second = mkPost "b" [] (2 :: Int)
              sparse = Map.fromList [(10, seed), (11, second)]
              byId = (mkPost "c" [] 0) {thread = [11]}
              byPosition = (mkPost "c" [] 0) {thread = [1]}
           in cone sparse byId == ["b", "c"]
                && null (cone sparse byPosition)
                && coneByIndex [seed, second] byPosition == ["b", "c"]
                && null (coneByIndex [seed, second] byId)
        ),
      checkV
        verbosity
        "devastator's triangular ids resolve by id and not by list position"
        ( let seed = mkPost "c0" [] (0 :: Int) :: Post String Int
              tick1 = (mkPost "c0" [] 1) {thread = [0]}
              tick2 = (mkPost "c0" [] 2) {thread = [1]}
              triangular = Map.fromList [(0, seed), (1, tick1), (3, tick2)]
              next = (mkPost "c0" [] 3) {thread = [3]}
           in branches triangular next == [["c0", "c0", "c0", "c0"]]
                && null (branchesByIndex [seed, tick1, tick2] next)
        ),
      checkV
        verbosity
        "dangling and future parent ids are dropped, never resolved"
        ( let sparse = Map.fromList [(0, p0), (2, p1)]
              gap = (mkPost "c" [] "") {thread = [1]}
              atSelf = (mkPost "c" [] "") {thread = [3]}
           in null (branches sparse gap) && null (branches sparse atSelf)
        ),
      checkV
        verbosity
        "an exact parent id wins over the supplied parent object"
        (branchesByIndex [p0, p1] (replyTo "child" 0 p1 "x") == [["child", "alice"]]),
      checkV
        verbosity
        "synthesis has one path per parent and cone is its normalised union"
        ( let merged = synthesis "sum" [] [2, 0] "sum"
           in branchesByIndex [p0, p1, r1] merged
                == [["sum", "alice"], ["sum", "carol", "bob"]]
                && coneByIndex [p0, p1, r1] merged
                  == ["alice", "bob", "carol", "sum"]
        ),
      checkV
        verbosity
        "two-node ancestry cycles contribute no completed root branch"
        ( let merged = synthesis "c" [] [1] ()
           in null (branchesByIndex [cycle0, cycle1] merged)
                && null (coneByIndex [cycle0, cycle1] merged)
        ),
      checkV
        verbosity
        "self-cycle ancestry contributes no completed root branch"
        ( let selfPost = (mkPost "self" [] ()) {thread = [0]}
           in null (branchesByIndex [selfPost] (replyTo "reply" 0 selfPost ()))
        ),
      checkV
        verbosity
        "channel addressing overrides the resolved audience"
        ( let p = mkChannelPost 1 9 [2, 3] () :: Post Int ()
           in deliversTo p [9]
                && not (deliversTo p [2])
                && not (deliversTo p [3])
        ),
      checkV
        verbosity
        "unchannelled delivery uses audience intersection and empty audiences discard"
        ( let p = mkPost 1 [2, 3] () :: Post Int ()
              discarded = mkPost 1 [] () :: Post Int ()
           in deliversTo p [3]
                && not (deliversTo p [4])
                && not (deliversTo discarded [1, 2])
        ),
      -- The empty-recipient convention is the wire codec's: a decoded audience
      -- holding a single empty name becomes [] before it reaches a post. What
      -- circuits guarantees is that an empty audience delivers nowhere, and
      -- that a named audience delivers by membership alone.
      checkV
        verbosity
        "an empty audience delivers nowhere, whatever the subscriptions are"
        ( let discarded = mkPost "a" [] () :: Post String ()
              named = mkPost "a" ["a"] () :: Post String ()
           in not (any (deliversTo discarded) [[], [""], ["a"], ["a", "b"], ["b"]])
                && deliversTo named ["a"]
                && deliversTo named ["b", "a"]
                && not (deliversTo named ["b"])
                && not (deliversTo named [""])
        ),
      checkV
        verbosity
        "a reply to an unchannelled parent stays unchannelled"
        ( let parent = mkPost "a" ["b"] () :: Post String ()
              reply = replyTo "b" 0 parent ()
           in isNothing (channel reply) && thread reply == [0]
        ),
      checkV
        verbosity
        "post conses newest-first while watch reads addressed posts oldest-first"
        ( let first = mkPost "a" ["me"] (1 :: Int) :: Post String Int
              skipped = mkPost "x" ["other"] 0 :: Post String Int
              second = mkChannelPost "b" "room" [] 2 :: Post String Int
              lg = post second (post skipped (post first (emptyLog @String @Int @[Post String Int])))
           in watch @String @Int @[Post String Int] ["me", "room"] lg == [first, second]
                && watch @String @Int @[Post String Int] ["me"] lg == [first]
                && null (watch @String @Int @[Post String Int] ["me"] (emptyLog @String @Int @[Post String Int]))
        ),
      checkV
        verbosity
        "inbox append and uncons preserve order and skip non-matching posts"
        ( let first = mkPost "a" ["me"] (1 :: Int) :: Post String Int
              skipped = mkPost "x" ["other"] 0 :: Post String Int
              second = mkChannelPost "b" "room" [] 2 :: Post String Int
              inbox0 = emptyInbox @String @Int @[Post String Int] ["room", "me"]
              inbox1 = appendInbox second (appendInbox skipped (appendInbox first inbox0))
           in case unconsInbox @String @Int inbox1 of
                These p rest ->
                  p == first
                    && case unconsInbox @String @Int rest of
                      This q -> q == second
                      _ -> False
                _ -> False
        ),
      checkV
        verbosity
        "inbox subscriptions retain their order and empty inboxes are exhausted"
        ( let inbox = emptyInbox @String @Int @[Post String Int] ["room", "me"]
              anonymous = emptyInbox @String @Int @[Post String Int] []
           in inboxWho inbox == Just "room"
                && inboxSubs inbox == ["room", "me"]
                && isNothing (inboxWho anonymous)
                && case unconsInbox @String @Int inbox of
                  That _ -> True
                  _ -> False
        ),
      checkV
        verbosity
        "Stamped reunion maps post bodies without touching receipts or addresses"
        ( let receipt = Stamped (41 :: Int) (mkPost "alice" ["bob"] "body")
              mapped = fmap (fmap reverse) receipt
           in stamp mapped == 41
                && body (stamped mapped) == "ydob"
                && from (stamped mapped) == "alice"
                && to (stamped mapped) == ["bob"]
        )
    ]
