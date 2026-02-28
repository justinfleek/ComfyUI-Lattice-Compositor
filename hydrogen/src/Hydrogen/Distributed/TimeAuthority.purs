-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // distributed // time-authority
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimeAuthority — Distributed time coordination for billion-agent scale.
-- |
-- | ## Purpose
-- |
-- | At billion-agent scale, time synchronization becomes critical:
-- |
-- | - Agents across the globe must agree on "when" events occur
-- | - Animation frames must be deterministic across viewports
-- | - Causal ordering must be preserved for collaborative editing
-- | - Network latency must be compensated for smooth coordination
-- |
-- | ## Lamport Timestamps
-- |
-- | Logical clocks that establish causal ordering without synchronized wall clocks:
-- |
-- | - Each agent maintains a counter
-- | - On local event: counter++
-- | - On send: attach counter to message
-- | - On receive: counter = max(local, received) + 1
-- |
-- | ## Vector Clocks
-- |
-- | Extension of Lamport timestamps that can detect concurrent events:
-- |
-- | - Each agent maintains a vector of counters (one per known agent)
-- | - Can determine if event A happened-before B, B happened-before A, or concurrent
-- |
-- | ## Network Time Protocol (NTP-style)
-- |
-- | For wall-clock synchronization when needed:
-- |
-- | - Round-trip time measurement
-- | - Clock offset estimation
-- | - Confidence/quality metrics

module Hydrogen.Distributed.TimeAuthority
  ( -- * Core Types
    AgentId
  , FrameTime
  , FrameNumber
  , WallClock
  
  -- * Lamport Timestamps
  , LamportTime
  , mkLamportTime
  , lamportTick
  , lamportSend
  , lamportReceive
  , lamportCompare
  , happenedBefore
  
  -- * Logical Time (with Agent ID)
  , LogicalTime
  , mkLogicalTime
  , logicalTick
  , logicalSend
  , logicalReceive
  , logicalCompare
  , logicalHappenedBefore
  
  -- * Vector Clocks
  , VectorClock
  , mkVectorClock
  , vectorTick
  , vectorSend
  , vectorReceive
  , vectorMerge
  , vectorCompare
  , VectorOrdering
      ( VectorLT
      , VectorGT
      , VectorEQ
      , VectorConcurrent
      )
  , isConcurrent
  , isHappenedBefore
  
  -- * Time Authority
  , TimeAuthority
      ( LocalAuthority
      , NetworkAuthority
      )
  , localAuthority
  , networkAuthority
  , isLocalAuthority
  , isNetworkAuthority
  , getAuthorityTime
  
  -- * Clock Synchronization
  , ClockSync
  , RttSample
  , mkClockSync
  , recordRoundTrip
  , estimateOffset
  , estimateRtt
  , syncQuality
  , SyncQuality
      ( SyncExcellent
      , SyncGood
      , SyncFair
      , SyncPoor
      , SyncUnsynced
      )
  , localToServer
  , serverToLocal
  
  -- * Frame Scheduling
  , FrameSchedule
  , mkFrameSchedule
  , frameToTime
  , timeToFrame
  , frameDuration
  , framesPerSecond
  , nextFrameTime
  , framesSince
  
  -- * Deterministic Frame Identity
  , FrameId
  , mkFrameId
  , frameIdFromTime
  , compareFrameIds
  , sameFrame
  
  -- * Additional Predicates
  , allHappenedBefore
  , syncMeetsMinimum
  , getServerTimeIfSynced
  , isValidSchedule
  , safeTimeToFrame
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, EQ, GT)
  , show
  , compare
  , otherwise
  , not
  , map
  , (&&)
  , (||)
  , (<)
  , (<=)
  , (<>)
  , (>)
  , (>=)
  , (==)
  , (/=)
  , (-)
  , (+)
  , (/)
  , (*)
  , ($)
  , (#)
  )

import Data.Array as Array
import Data.Foldable (foldl, all)
import Data.Int (floor, toNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // core aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique agent identifier (UUID5 string)
type AgentId = String

-- | Time in milliseconds (for frame timing)
type FrameTime = Number

-- | Frame number (monotonically increasing integer)
type FrameNumber = Int

-- | Wall clock time in milliseconds since epoch
type WallClock = Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // lamport timestamps
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lamport timestamp — scalar logical clock
-- |
-- | Provides causal ordering: if event A causally precedes B, then L(A) < L(B).
-- | However, L(A) < L(B) does NOT imply A causally precedes B.
newtype LamportTime = LamportTime Int

derive instance eqLamportTime :: Eq LamportTime
derive instance ordLamportTime :: Ord LamportTime

instance showLamportTime :: Show LamportTime where
  show (LamportTime t) = "L(" <> show t <> ")"

-- | Create initial Lamport timestamp
mkLamportTime :: LamportTime
mkLamportTime = LamportTime 0

-- | Increment for local event
lamportTick :: LamportTime -> LamportTime
lamportTick (LamportTime t) = LamportTime (t + 1)

-- | Prepare timestamp for sending (tick then return)
lamportSend :: LamportTime -> Tuple LamportTime LamportTime
lamportSend lt = 
  let newTime = lamportTick lt
  in Tuple newTime newTime

-- | Update on receiving a message with remote timestamp
lamportReceive :: LamportTime -> LamportTime -> LamportTime
lamportReceive (LamportTime local) (LamportTime remote) =
  LamportTime (maxInt local remote + 1)

-- | Compare two Lamport timestamps
lamportCompare :: LamportTime -> LamportTime -> Ordering
lamportCompare (LamportTime a) (LamportTime b) = compare a b

-- | Check if first timestamp happened-before second
-- |
-- | Note: This is a necessary but not sufficient condition for causality.
happenedBefore :: LamportTime -> LamportTime -> Boolean
happenedBefore (LamportTime a) (LamportTime b) = a < b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // logical time
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logical time combining Lamport timestamp with agent identity
-- |
-- | Includes wall clock for debugging/logging, but ordering uses Lamport only.
type LogicalTime =
  { wallClock :: WallClock
  , logicalCounter :: Int
  , agentId :: AgentId
  }

-- | Create initial logical time
mkLogicalTime :: AgentId -> WallClock -> LogicalTime
mkLogicalTime agentId wallClock =
  { wallClock
  , logicalCounter: 0
  , agentId
  }

-- | Tick logical time for local event
logicalTick :: WallClock -> LogicalTime -> LogicalTime
logicalTick newWallClock lt = lt
  { wallClock = newWallClock
  , logicalCounter = lt.logicalCounter + 1
  }

-- | Prepare logical time for sending
logicalSend :: WallClock -> LogicalTime -> Tuple LogicalTime LogicalTime
logicalSend wallClock lt =
  let newTime = logicalTick wallClock lt
  in Tuple newTime newTime

-- | Update logical time on receiving message
logicalReceive :: WallClock -> LogicalTime -> LogicalTime -> LogicalTime
logicalReceive wallClock local remote = local
  { wallClock = wallClock
  , logicalCounter = maxInt local.logicalCounter remote.logicalCounter + 1
  }

-- | Compare logical times (by counter, then agent ID for tiebreak)
logicalCompare :: LogicalTime -> LogicalTime -> Ordering
logicalCompare a b =
  case compare a.logicalCounter b.logicalCounter of
    EQ -> compare a.agentId b.agentId
    other -> other

-- | Check if first logical time happened-before second
logicalHappenedBefore :: LogicalTime -> LogicalTime -> Boolean
logicalHappenedBefore a b = a.logicalCounter < b.logicalCounter

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // vector clocks
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vector clock — detects concurrent events
-- |
-- | Maps each known agent to their logical counter.
-- | Can determine happened-before, happened-after, or concurrent relationships.
newtype VectorClock = VectorClock (Map AgentId Int)

derive instance eqVectorClock :: Eq VectorClock

instance showVectorClock :: Show VectorClock where
  show (VectorClock m) = "VC(" <> show (Map.toUnfoldable m :: Array (Tuple AgentId Int)) <> ")"

-- | Create empty vector clock for an agent
mkVectorClock :: AgentId -> VectorClock
mkVectorClock agentId = VectorClock (Map.singleton agentId 0)

-- | Tick vector clock for local event
vectorTick :: AgentId -> VectorClock -> VectorClock
vectorTick agentId (VectorClock m) =
  let current = fromMaybe 0 (Map.lookup agentId m)
  in VectorClock (Map.insert agentId (current + 1) m)

-- | Prepare vector clock for sending (tick then return)
vectorSend :: AgentId -> VectorClock -> Tuple VectorClock VectorClock
vectorSend agentId vc =
  let newVc = vectorTick agentId vc
  in Tuple newVc newVc

-- | Update vector clock on receiving message
vectorReceive :: AgentId -> VectorClock -> VectorClock -> VectorClock
vectorReceive agentId local remote =
  vectorTick agentId (vectorMerge local remote)

-- | Merge two vector clocks (point-wise maximum)
vectorMerge :: VectorClock -> VectorClock -> VectorClock
vectorMerge (VectorClock a) (VectorClock b) =
  VectorClock (Map.unionWith maxInt a b)

-- | Ordering relationship between vector clocks
data VectorOrdering
  = VectorLT       -- First happened strictly before second
  | VectorGT       -- First happened strictly after second
  | VectorEQ       -- Identical clocks
  | VectorConcurrent  -- Neither happened before the other

derive instance eqVectorOrdering :: Eq VectorOrdering

instance showVectorOrdering :: Show VectorOrdering where
  show VectorLT = "HappenedBefore"
  show VectorGT = "HappenedAfter"
  show VectorEQ = "Equal"
  show VectorConcurrent = "Concurrent"

-- | Compare two vector clocks
vectorCompare :: VectorClock -> VectorClock -> VectorOrdering
vectorCompare (VectorClock a) (VectorClock b) =
  let
    -- Get all keys from both maps (deduplicated)
    allKeysRaw = Array.concat 
      [ Map.keys a # Array.fromFoldable
      , Map.keys b # Array.fromFoldable
      ]
    allKeys = arrayNub allKeysRaw
    
    -- Compare each component
    comparisons = map (\k -> 
      let va = fromMaybe 0 (Map.lookup k a)
          vb = fromMaybe 0 (Map.lookup k b)
      in compare va vb
    ) allKeys
    
    hasLT = Array.any (_ == LT) comparisons
    hasGT = Array.any (_ == GT) comparisons
  in
    case Tuple hasLT hasGT of
      Tuple false false -> VectorEQ
      Tuple true false -> VectorLT
      Tuple false true -> VectorGT
      Tuple true true -> VectorConcurrent

-- | Check if events are concurrent (neither happened-before the other)
isConcurrent :: VectorClock -> VectorClock -> Boolean
isConcurrent a b = vectorCompare a b == VectorConcurrent

-- | Check if first clock strictly happened-before second
isHappenedBefore :: VectorClock -> VectorClock -> Boolean
isHappenedBefore a b = vectorCompare a b == VectorLT

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // time authority
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time authority — determines whose clock is authoritative
data TimeAuthority
  = LocalAuthority
      { agentId :: AgentId
      , currentTime :: FrameTime
      }
  | NetworkAuthority
      { serverId :: AgentId
      , serverTime :: FrameTime
      , localOffset :: FrameTime   -- Server - Local
      , rtt :: FrameTime           -- Round-trip time
      , confidence :: Number       -- 0.0-1.0 sync quality
      }

derive instance eqTimeAuthority :: Eq TimeAuthority

instance showTimeAuthority :: Show TimeAuthority where
  show (LocalAuthority r) = "LocalAuthority(" <> r.agentId <> ")"
  show (NetworkAuthority r) = "NetworkAuthority(" <> r.serverId <> ", offset=" <> show r.localOffset <> "ms)"

-- | Create local authority (single agent, no sync needed)
localAuthority :: AgentId -> FrameTime -> TimeAuthority
localAuthority agentId currentTime = LocalAuthority { agentId, currentTime }

-- | Create network authority (coordinated cluster)
networkAuthority :: AgentId -> FrameTime -> FrameTime -> FrameTime -> Number -> TimeAuthority
networkAuthority serverId serverTime localOffset rtt confidence =
  NetworkAuthority { serverId, serverTime, localOffset, rtt, confidence }

-- | Check if using local authority
isLocalAuthority :: TimeAuthority -> Boolean
isLocalAuthority (LocalAuthority _) = true
isLocalAuthority _ = false

-- | Check if using network authority
isNetworkAuthority :: TimeAuthority -> Boolean
isNetworkAuthority (NetworkAuthority _) = true
isNetworkAuthority _ = false

-- | Get authoritative time
getAuthorityTime :: TimeAuthority -> FrameTime
getAuthorityTime (LocalAuthority r) = r.currentTime
getAuthorityTime (NetworkAuthority r) = r.serverTime

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // clock synchronization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clock synchronization state (NTP-style)
-- |
-- | Maintains history of round-trip measurements to estimate offset and quality.
type ClockSync =
  { serverId :: AgentId
  , samples :: Array RttSample
  , maxSamples :: Int
  , estimatedOffset :: FrameTime
  , estimatedRtt :: FrameTime
  , quality :: SyncQuality
  }

-- | Single RTT measurement sample
type RttSample =
  { sendTime :: WallClock      -- Local time when request sent
  , receiveTime :: WallClock   -- Local time when response received
  , serverTime :: WallClock    -- Server's timestamp in response
  }

-- | Synchronization quality level
data SyncQuality
  = SyncExcellent    -- RTT < 10ms, low variance
  | SyncGood         -- RTT < 50ms, reasonable variance
  | SyncFair         -- RTT < 200ms
  | SyncPoor         -- RTT < 1000ms
  | SyncUnsynced     -- No valid samples or RTT >= 1000ms

derive instance eqSyncQuality :: Eq SyncQuality
derive instance ordSyncQuality :: Ord SyncQuality

instance showSyncQuality :: Show SyncQuality where
  show SyncExcellent = "Excellent"
  show SyncGood = "Good"
  show SyncFair = "Fair"
  show SyncPoor = "Poor"
  show SyncUnsynced = "Unsynced"

-- | Create initial clock sync state
mkClockSync :: AgentId -> ClockSync
mkClockSync serverId =
  { serverId
  , samples: []
  , maxSamples: 8  -- Keep last 8 samples
  , estimatedOffset: 0.0
  , estimatedRtt: 0.0
  , quality: SyncUnsynced
  }

-- | Record a round-trip measurement
recordRoundTrip :: WallClock -> WallClock -> WallClock -> ClockSync -> ClockSync
recordRoundTrip sendTime receiveTime serverTime sync =
  let
    sample = { sendTime, receiveTime, serverTime }
    newSamples = Array.take sync.maxSamples (Array.cons sample sync.samples)
    newRtt = computeRtt newSamples
    newOffset = computeOffset newSamples
    newQuality = computeQuality newRtt
  in sync
    { samples = newSamples
    , estimatedRtt = newRtt
    , estimatedOffset = newOffset
    , quality = newQuality
    }

-- | Get estimated offset (server - local)
estimateOffset :: ClockSync -> FrameTime
estimateOffset sync = sync.estimatedOffset

-- | Get estimated round-trip time
estimateRtt :: ClockSync -> FrameTime
estimateRtt sync = sync.estimatedRtt

-- | Get sync quality
syncQuality :: ClockSync -> SyncQuality
syncQuality sync = sync.quality

-- | Convert local time to estimated server time
localToServer :: ClockSync -> WallClock -> WallClock
localToServer sync localTime = localTime + sync.estimatedOffset

-- | Convert server time to estimated local time
serverToLocal :: ClockSync -> WallClock -> WallClock
serverToLocal sync serverTime = serverTime - sync.estimatedOffset

-- | Compute average RTT from samples
computeRtt :: Array RttSample -> FrameTime
computeRtt samples =
  if Array.null samples
    then 0.0
    else
      let rtts = map (\s -> s.receiveTime - s.sendTime) samples
          total = foldl (+) 0.0 rtts
      in total / toNumber (Array.length samples)

-- | Compute offset using NTP formula: offset = ((t2-t1) + (t3-t4)) / 2
-- | Where t1=send, t2=server receive (approx), t3=server send (approx), t4=receive
-- | Simplified: offset = serverTime - (sendTime + RTT/2)
computeOffset :: Array RttSample -> FrameTime
computeOffset samples =
  if Array.null samples
    then 0.0
    else
      let offsets = map (\s ->
            let rtt = s.receiveTime - s.sendTime
                localMidpoint = s.sendTime + rtt / 2.0
            in s.serverTime - localMidpoint
          ) samples
          total = foldl (+) 0.0 offsets
      in total / toNumber (Array.length samples)

-- | Determine quality based on RTT
computeQuality :: FrameTime -> SyncQuality
computeQuality rtt
  | rtt < 10.0 = SyncExcellent
  | rtt < 50.0 = SyncGood
  | rtt < 200.0 = SyncFair
  | rtt < 1000.0 = SyncPoor
  | otherwise = SyncUnsynced

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // frame scheduling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frame schedule for deterministic timing
-- |
-- | Given a global start time and frame rate, any agent can compute
-- | the exact time of any frame number.
type FrameSchedule =
  { globalStart :: WallClock   -- Epoch for frame counting
  , fps :: Number              -- Target frames per second
  , frameDurationMs :: Number  -- 1000 / fps
  }

-- | Create frame schedule
mkFrameSchedule :: WallClock -> Number -> FrameSchedule
mkFrameSchedule globalStart fps =
  { globalStart
  , fps
  , frameDurationMs: 1000.0 / fps
  }

-- | Get frame duration in milliseconds
frameDuration :: FrameSchedule -> FrameTime
frameDuration sched = sched.frameDurationMs

-- | Get frames per second
framesPerSecond :: FrameSchedule -> Number
framesPerSecond sched = sched.fps

-- | Compute wall clock time for a frame number
frameToTime :: FrameSchedule -> FrameNumber -> WallClock
frameToTime sched frame = 
  sched.globalStart + (toNumber frame * sched.frameDurationMs)

-- | Compute frame number from wall clock time
timeToFrame :: FrameSchedule -> WallClock -> FrameNumber
timeToFrame sched time =
  floor ((time - sched.globalStart) / sched.frameDurationMs)

-- | Get time of next frame after given time
nextFrameTime :: FrameSchedule -> WallClock -> WallClock
nextFrameTime sched currentTime =
  let currentFrame = timeToFrame sched currentTime
  in frameToTime sched (currentFrame + 1)

-- | Count frames elapsed since a given time
framesSince :: FrameSchedule -> WallClock -> WallClock -> Int
framesSince sched startTime currentTime =
  timeToFrame sched currentTime - timeToFrame sched startTime

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // deterministic frame identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deterministic frame identifier
-- |
-- | Combines frame number with schedule identity for globally unique frame IDs.
-- | Two agents with the same schedule will generate identical frame IDs.
type FrameId =
  { frameNumber :: FrameNumber
  , scheduleEpoch :: WallClock
  , fps :: Number
  }

-- | Create frame ID
mkFrameId :: FrameNumber -> FrameSchedule -> FrameId
mkFrameId frameNumber sched =
  { frameNumber
  , scheduleEpoch: sched.globalStart
  , fps: sched.fps
  }

-- | Create frame ID from wall clock time
frameIdFromTime :: WallClock -> FrameSchedule -> FrameId
frameIdFromTime time sched = mkFrameId (timeToFrame sched time) sched

-- | Compare frame IDs
compareFrameIds :: FrameId -> FrameId -> Ordering
compareFrameIds a b =
  case compare a.scheduleEpoch b.scheduleEpoch of
    EQ -> case compare a.fps b.fps of
      EQ -> compare a.frameNumber b.frameNumber
      other -> other
    other -> other

-- | Check if two frame IDs reference the same frame
sameFrame :: FrameId -> FrameId -> Boolean
sameFrame a b =
  a.frameNumber == b.frameNumber &&
  a.scheduleEpoch == b.scheduleEpoch &&
  a.fps == b.fps

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // helper functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum of two integers
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Placeholder for Array.nub (deduplicate)
-- | Using simple implementation - real codebase may have optimized version
arrayNub :: forall a. Eq a => Array a -> Array a
arrayNub = foldl (\acc x -> if elemArray x acc then acc else Array.snoc acc x) []

-- | Check if element is in array
elemArray :: forall a. Eq a => a -> Array a -> Boolean
elemArray x arr = Array.any (_ == x) arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // additional predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if all vector clocks in array have happened-before reference
allHappenedBefore :: VectorClock -> Array VectorClock -> Boolean
allHappenedBefore reference clocks = all (\c -> isHappenedBefore c reference) clocks

-- | Check if sync quality meets minimum threshold
syncMeetsMinimum :: SyncQuality -> ClockSync -> Boolean
syncMeetsMinimum minimum sync = sync.quality <= minimum

-- | Try to get server time if sync quality is acceptable
getServerTimeIfSynced :: SyncQuality -> WallClock -> ClockSync -> Maybe WallClock
getServerTimeIfSynced minQuality localTime sync =
  if sync.quality <= minQuality
    then Just (localToServer sync localTime)
    else Nothing

-- | Check if frame schedule is valid (positive fps)
isValidSchedule :: FrameSchedule -> Boolean
isValidSchedule sched = sched.fps > 0.0 && sched.frameDurationMs > 0.0

-- | Get frame number if schedule is valid
safeTimeToFrame :: FrameSchedule -> WallClock -> Maybe FrameNumber
safeTimeToFrame sched time =
  if isValidSchedule sched
    then Just (timeToFrame sched time)
    else Nothing
