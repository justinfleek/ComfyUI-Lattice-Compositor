-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // distributed // viewport-sync
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ViewportSync — Multi-viewport coordination for distributed rendering.
-- |
-- | ## Purpose
-- |
-- | When multiple viewports render the same scene (collaborative editing,
-- | multi-monitor displays, distributed rendering farms), they must:
-- |
-- | - Agree on the current frame
-- | - Compensate for drift between local clocks
-- | - Share effect state (animations, transitions)
-- | - Handle disconnection gracefully
-- |
-- | ## Architecture
-- |
-- | Each viewport has a ViewportSync state that tracks:
-- |
-- | 1. Which time authority it follows
-- | 2. How many frames ahead/behind the authority it is
-- | 3. Current sync state (synchronized, drifting, resynchronizing, disconnected)
-- | 4. Subscriptions to shared effects
-- |
-- | ## Drift Compensation
-- |
-- | Drift occurs when:
-- | - Local clock runs faster/slower than authority
-- | - Network latency varies
-- | - Frame drops cause desync
-- |
-- | Compensation strategies:
-- | - Skip frames to catch up
-- | - Interpolate to smooth transitions
-- | - Pause and wait for authority

module Hydrogen.Distributed.ViewportSync
  ( -- * Core Types
    ViewportId
  , EffectId
  , FrameOffset
  
  -- * Sync State
  , SyncState
      ( Synchronized
      , Drifting
      , Resynchronizing
      , Disconnected
      )
  , DriftDirection
      ( DriftingAhead
      , DriftingBehind
      )
  , isSynchronized
  , isDrifting
  , isResynchronizing
  , isDisconnected
  
  -- * Viewport Sync
  , ViewportSync
  , mkViewportSync
  , updateSyncState
  , setFrameOffset
  , recordDrift
  , markSynchronized
  , markDisconnected
  , getSyncQuality
  
  -- * Drift Compensation
  , DriftCompensation
      ( NoCompensation
      , SkipFrames
      , InterpolateFrames
      , PauseAndWait
      , HardResync
      )
  , computeCompensation
  , applyCompensation
  , DriftThresholds
  , defaultDriftThresholds
  
  -- * Shared Effect State
  , SharedEffectState
  , EffectPhase
      ( EffectIdle
      , EffectRunning
      , EffectComplete
      , EffectPaused
      )
  , mkSharedEffect
  , subscribeViewport
  , unsubscribeViewport
  , updateEffectPhase
  , isEffectOwner
  , getSubscribers
  
  -- * Effect Registry
  , EffectRegistry
  , mkEffectRegistry
  , registerEffect
  , unregisterEffect
  , getEffect
  , getEffectsForViewport
  , tickEffects
  
  -- * Multi-Viewport Coordination
  , ViewportCluster
  , mkViewportCluster
  , addViewport
  , removeViewport
  , getViewport
  , getAllViewports
  , broadcastFrame
  , computeClusterState
  , ClusterState
      ( ClusterSynced
      , ClusterPartialSync
      , ClusterDesync
      , ClusterEmpty
      )
  
  -- * Frame Reconciliation
  , FrameReconciliation
  , reconcileFrames
  , ReconciliationStrategy
      ( NoReconciliation
      , CatchUp
      , SlowDown
      , MeetInMiddle
      , ForceResync
      )
  , applyReconciliation
  
  -- * Time Authority Integration
  , mkViewportSyncLocal
  , mkViewportSyncNetwork
  , viewportUsesNetwork
  , viewportUsesLocal
  , getViewportAuthorityTime
  
  -- * Frame Schedule Integration
  , computeExpectedFrame
  , computeNextFrameTime
  , viewportIsBehind
  , viewportIsAhead
  , getScheduleFps
  , getScheduleFrameDuration
  
  -- * Clock Sync Integration
  , mkViewportSyncWithClockSync
  , syncQualityToNumber
  , viewportMeetsSyncQuality
  , viewportLocalToServer
  , viewportServerToLocal
  
  -- * Vector Clock Integration
  , ViewportSyncWithCausality
  , mkViewportSyncWithCausality
  , tickCausality
  , receiveCausality
  , checkCausalOrder
  , areConcurrent
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
  , negate
  )

import Data.Number (abs)

import Data.Array as Array
import Data.Foldable (foldl, all, any)
import Data.Int (toNumber, floor)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Distributed.TimeAuthority 
  ( TimeAuthority
      ( LocalAuthority
      , NetworkAuthority
      )
  , FrameTime
  , FrameNumber
  , AgentId
  , WallClock
  , isNetworkAuthority
  , isLocalAuthority
  , getAuthorityTime
  , localAuthority
  , networkAuthority
  , FrameSchedule
  , mkFrameSchedule
  , frameToTime
  , timeToFrame
  , frameDuration
  , framesPerSecond
  , ClockSync
  , mkClockSync
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
  , LamportTime
  , mkLamportTime
  , lamportTick
  , lamportReceive
  , VectorClock
  , mkVectorClock
  , vectorTick
  , vectorReceive
  , vectorCompare
  , VectorOrdering
      ( VectorLT
      , VectorGT
      , VectorEQ
      , VectorConcurrent
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // core aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique viewport identifier
type ViewportId = String

-- | Unique effect identifier
type EffectId = String

-- | Frame offset (positive = ahead, negative = behind)
type FrameOffset = Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // sync state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Synchronization state of a viewport relative to authority
data SyncState
  = Synchronized                      -- Within tolerance of authority
  | Drifting 
      { driftMs :: Number             -- Milliseconds drifting per frame
      , direction :: DriftDirection   -- Getting ahead or behind
      }
  | Resynchronizing
      { targetFrame :: FrameNumber    -- Frame we're trying to reach
      , progress :: Number            -- 0.0-1.0 resync progress
      }
  | Disconnected
      { since :: FrameTime            -- When disconnect was detected
      , lastKnownFrame :: FrameNumber -- Last synchronized frame
      }

derive instance eqSyncState :: Eq SyncState

instance showSyncState :: Show SyncState where
  show Synchronized = "Synchronized"
  show (Drifting r) = "Drifting(" <> show r.driftMs <> "ms/" <> show r.direction <> ")"
  show (Resynchronizing r) = "Resynchronizing(target=" <> show r.targetFrame <> ")"
  show (Disconnected r) = "Disconnected(since=" <> show r.since <> "ms)"

-- | Direction of drift
data DriftDirection
  = DriftingAhead   -- Local clock running fast
  | DriftingBehind  -- Local clock running slow

derive instance eqDriftDirection :: Eq DriftDirection

instance showDriftDirection :: Show DriftDirection where
  show DriftingAhead = "Ahead"
  show DriftingBehind = "Behind"

-- | Check if synchronized
isSynchronized :: SyncState -> Boolean
isSynchronized Synchronized = true
isSynchronized _ = false

-- | Check if drifting
isDrifting :: SyncState -> Boolean
isDrifting (Drifting _) = true
isDrifting _ = false

-- | Check if resynchronizing
isResynchronizing :: SyncState -> Boolean
isResynchronizing (Resynchronizing _) = true
isResynchronizing _ = false

-- | Check if disconnected
isDisconnected :: SyncState -> Boolean
isDisconnected (Disconnected _) = true
isDisconnected _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // viewport sync
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport synchronization state
type ViewportSync =
  { viewportId :: ViewportId
  , authority :: TimeAuthority
  , frameOffset :: FrameOffset        -- Frames ahead (+) or behind (-) authority
  , syncState :: SyncState
  , lastSyncTime :: FrameTime         -- When last sync occurred
  , driftHistory :: Array Number      -- Recent drift measurements (for averaging)
  , maxHistorySize :: Int
  }

-- | Create new viewport sync state
mkViewportSync :: ViewportId -> TimeAuthority -> ViewportSync
mkViewportSync viewportId authority =
  { viewportId
  , authority
  , frameOffset: 0
  , syncState: Synchronized
  , lastSyncTime: getAuthorityTime authority
  , driftHistory: []
  , maxHistorySize: 10
  }

-- | Update sync state
updateSyncState :: SyncState -> ViewportSync -> ViewportSync
updateSyncState newState sync = sync { syncState = newState }

-- | Set frame offset
setFrameOffset :: FrameOffset -> ViewportSync -> ViewportSync
setFrameOffset offset sync = sync { frameOffset = offset }

-- | Record a drift measurement and update state
recordDrift :: Number -> FrameTime -> ViewportSync -> ViewportSync
recordDrift driftMs currentTime sync =
  let
    newHistory = Array.take sync.maxHistorySize 
                   (Array.cons driftMs sync.driftHistory)
    avgDrift = averageDrift newHistory
    newState = computeSyncState avgDrift sync.syncState
  in sync
    { driftHistory = newHistory
    , syncState = newState
    , lastSyncTime = currentTime
    }

-- | Mark viewport as synchronized
markSynchronized :: FrameTime -> ViewportSync -> ViewportSync
markSynchronized currentTime sync = sync
  { syncState = Synchronized
  , frameOffset = 0
  , lastSyncTime = currentTime
  , driftHistory = []
  }

-- | Mark viewport as disconnected
markDisconnected :: FrameTime -> FrameNumber -> ViewportSync -> ViewportSync
markDisconnected currentTime lastFrame sync = sync
  { syncState = Disconnected { since: currentTime, lastKnownFrame: lastFrame }
  }

-- | Get overall sync quality (0.0 = disconnected, 1.0 = perfect sync)
getSyncQuality :: ViewportSync -> Number
getSyncQuality sync = case sync.syncState of
  Synchronized -> 1.0
  Drifting r -> clamp01 (1.0 - abs r.driftMs / 100.0)
  Resynchronizing r -> r.progress * 0.5
  Disconnected _ -> 0.0

-- | Compute sync state from average drift
-- |
-- | Note: currentState parameter reserved for hysteresis in future
-- | (e.g., require sustained drift before changing state)
computeSyncState :: Number -> SyncState -> SyncState
computeSyncState avgDrift _currentState
  | abs avgDrift < 1.0 = Synchronized
  | avgDrift > 0.0 = Drifting { driftMs: avgDrift, direction: DriftingAhead }
  | otherwise = Drifting { driftMs: abs avgDrift, direction: DriftingBehind }

-- | Compute average drift from history
averageDrift :: Array Number -> Number
averageDrift arr =
  if Array.null arr
    then 0.0
    else foldl (+) 0.0 arr / toNumber (Array.length arr)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // drift compensation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drift compensation action
data DriftCompensation
  = NoCompensation              -- Within tolerance
  | SkipFrames Int              -- Skip N frames to catch up
  | InterpolateFrames Number    -- Interpolate between frames
  | PauseAndWait FrameTime      -- Pause for N ms
  | HardResync FrameNumber      -- Jump to frame immediately

derive instance eqDriftCompensation :: Eq DriftCompensation

instance showDriftCompensation :: Show DriftCompensation where
  show NoCompensation = "NoCompensation"
  show (SkipFrames n) = "SkipFrames(" <> show n <> ")"
  show (InterpolateFrames t) = "InterpolateFrames(" <> show t <> ")"
  show (PauseAndWait ms) = "PauseAndWait(" <> show ms <> "ms)"
  show (HardResync frame) = "HardResync(" <> show frame <> ")"

-- | Thresholds for drift compensation decisions
type DriftThresholds =
  { toleranceMs :: Number       -- Drift below this is ignored
  , skipThresholdMs :: Number   -- Above this, skip frames
  , hardResyncMs :: Number      -- Above this, hard resync
  , maxSkipFrames :: Int        -- Maximum frames to skip at once
  }

-- | Default drift thresholds
defaultDriftThresholds :: DriftThresholds
defaultDriftThresholds =
  { toleranceMs: 5.0
  , skipThresholdMs: 50.0
  , hardResyncMs: 500.0
  , maxSkipFrames: 5
  }

-- | Compute compensation needed for current drift
computeCompensation :: DriftThresholds -> Number -> FrameTime -> DriftCompensation
computeCompensation thresholds driftMs frameDuration
  | abs driftMs < thresholds.toleranceMs = NoCompensation
  | abs driftMs >= thresholds.hardResyncMs = HardResync 0  -- Caller should set frame
  | driftMs > thresholds.skipThresholdMs =
      let framesToSkip = minInt thresholds.maxSkipFrames 
                           (floor (driftMs / frameDuration))
      in if framesToSkip > 0 then SkipFrames framesToSkip else InterpolateFrames 1.5
  | driftMs < negate thresholds.skipThresholdMs =
      PauseAndWait (abs driftMs)
  | otherwise = 
      InterpolateFrames (1.0 + driftMs / frameDuration / 10.0)

-- | Apply compensation to get target frame
applyCompensation :: DriftCompensation -> FrameNumber -> FrameNumber
applyCompensation comp currentFrame = case comp of
  NoCompensation -> currentFrame
  SkipFrames n -> currentFrame + n
  InterpolateFrames _ -> currentFrame  -- Interpolation doesn't change frame
  PauseAndWait _ -> currentFrame       -- Pause doesn't change frame
  HardResync frame -> frame

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // shared effect state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shared effect state for cross-viewport coordination
type SharedEffectState =
  { effectId :: EffectId
  , owningViewport :: ViewportId
  , subscribedViewports :: Set ViewportId
  , currentPhase :: EffectPhase
  , lastSyncFrame :: FrameNumber
  , priority :: Int                   -- Higher priority effects sync first
  }

-- | Effect phase (simplified animation phase)
data EffectPhase
  = EffectIdle
  | EffectRunning Number    -- Progress 0.0-1.0
  | EffectComplete
  | EffectPaused Number     -- Progress when paused

derive instance eqEffectPhase :: Eq EffectPhase

instance showEffectPhase :: Show EffectPhase where
  show EffectIdle = "Idle"
  show (EffectRunning p) = "Running(" <> show p <> ")"
  show EffectComplete = "Complete"
  show (EffectPaused p) = "Paused(" <> show p <> ")"

-- | Create shared effect
mkSharedEffect :: EffectId -> ViewportId -> Int -> SharedEffectState
mkSharedEffect effectId owningViewport priority =
  { effectId
  , owningViewport
  , subscribedViewports: Set.singleton owningViewport
  , currentPhase: EffectIdle
  , lastSyncFrame: 0
  , priority
  }

-- | Subscribe viewport to effect
subscribeViewport :: ViewportId -> SharedEffectState -> SharedEffectState
subscribeViewport viewportId effect = effect
  { subscribedViewports = Set.insert viewportId effect.subscribedViewports }

-- | Unsubscribe viewport from effect
unsubscribeViewport :: ViewportId -> SharedEffectState -> SharedEffectState
unsubscribeViewport viewportId effect = effect
  { subscribedViewports = Set.delete viewportId effect.subscribedViewports }

-- | Update effect phase
updateEffectPhase :: EffectPhase -> FrameNumber -> SharedEffectState -> SharedEffectState
updateEffectPhase phase frame effect = effect
  { currentPhase = phase
  , lastSyncFrame = frame
  }

-- | Check if viewport owns this effect
isEffectOwner :: ViewportId -> SharedEffectState -> Boolean
isEffectOwner viewportId effect = effect.owningViewport == viewportId

-- | Get all subscribed viewports
getSubscribers :: SharedEffectState -> Array ViewportId
getSubscribers effect = Set.toUnfoldable effect.subscribedViewports

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect registry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Registry of shared effects
type EffectRegistry =
  { effects :: Map EffectId SharedEffectState
  , nextId :: Int
  }

-- | Create empty effect registry
mkEffectRegistry :: EffectRegistry
mkEffectRegistry =
  { effects: Map.empty
  , nextId: 1
  }

-- | Register new effect
registerEffect :: ViewportId -> Int -> EffectRegistry -> Tuple EffectId EffectRegistry
registerEffect owningViewport priority registry =
  let
    effectId = "effect-" <> show registry.nextId
    effect = mkSharedEffect effectId owningViewport priority
    newRegistry =
      { effects: Map.insert effectId effect registry.effects
      , nextId: registry.nextId + 1
      }
  in Tuple effectId newRegistry

-- | Unregister effect
unregisterEffect :: EffectId -> EffectRegistry -> EffectRegistry
unregisterEffect effectId registry = registry
  { effects = Map.delete effectId registry.effects }

-- | Get effect by ID
getEffect :: EffectId -> EffectRegistry -> Maybe SharedEffectState
getEffect effectId registry = Map.lookup effectId registry.effects

-- | Get all effects owned by or subscribed to by a viewport
getEffectsForViewport :: ViewportId -> EffectRegistry -> Array SharedEffectState
getEffectsForViewport viewportId registry =
  Array.filter (viewportInEffect viewportId) 
    (Map.values registry.effects # Array.fromFoldable)

-- | Check if viewport is involved in effect
viewportInEffect :: ViewportId -> SharedEffectState -> Boolean
viewportInEffect viewportId effect =
  effect.owningViewport == viewportId || 
  Set.member viewportId effect.subscribedViewports

-- | Tick all effects (advance running effects)
tickEffects :: FrameNumber -> Number -> EffectRegistry -> EffectRegistry
tickEffects frame deltaProgress registry = registry
  { effects = map (tickEffect frame deltaProgress) registry.effects }

-- | Tick single effect
tickEffect :: FrameNumber -> Number -> SharedEffectState -> SharedEffectState
tickEffect frame deltaProgress effect = case effect.currentPhase of
  EffectRunning progress ->
    let newProgress = progress + deltaProgress
    in if newProgress >= 1.0
         then effect { currentPhase = EffectComplete, lastSyncFrame = frame }
         else effect { currentPhase = EffectRunning newProgress, lastSyncFrame = frame }
  _ -> effect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // multi-viewport coordination
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cluster of synchronized viewports
type ViewportCluster =
  { viewports :: Map ViewportId ViewportSync
  , effects :: EffectRegistry
  , authorityId :: AgentId
  , currentFrame :: FrameNumber
  }

-- | Create viewport cluster
mkViewportCluster :: AgentId -> ViewportCluster
mkViewportCluster authorityId =
  { viewports: Map.empty
  , effects: mkEffectRegistry
  , authorityId
  , currentFrame: 0
  }

-- | Add viewport to cluster
addViewport :: ViewportSync -> ViewportCluster -> ViewportCluster
addViewport sync cluster = cluster
  { viewports = Map.insert sync.viewportId sync cluster.viewports }

-- | Remove viewport from cluster
removeViewport :: ViewportId -> ViewportCluster -> ViewportCluster
removeViewport viewportId cluster = cluster
  { viewports = Map.delete viewportId cluster.viewports }

-- | Get viewport by ID
getViewport :: ViewportId -> ViewportCluster -> Maybe ViewportSync
getViewport viewportId cluster = Map.lookup viewportId cluster.viewports

-- | Get all viewports
getAllViewports :: ViewportCluster -> Array ViewportSync
getAllViewports cluster = Map.values cluster.viewports # Array.fromFoldable

-- | Broadcast frame update to all viewports
broadcastFrame :: FrameNumber -> FrameTime -> ViewportCluster -> ViewportCluster
broadcastFrame frame time cluster = cluster
  { viewports = map (updateViewportFrame frame time) cluster.viewports
  , currentFrame = frame
  }

-- | Update viewport with new frame
updateViewportFrame :: FrameNumber -> FrameTime -> ViewportSync -> ViewportSync
updateViewportFrame _ time sync = sync { lastSyncTime = time }

-- | Overall cluster synchronization state
data ClusterState
  = ClusterSynced             -- All viewports synchronized
  | ClusterPartialSync Int    -- N viewports out of sync
  | ClusterDesync             -- Majority out of sync
  | ClusterEmpty              -- No viewports

derive instance eqClusterState :: Eq ClusterState

instance showClusterState :: Show ClusterState where
  show ClusterSynced = "Synced"
  show (ClusterPartialSync n) = "PartialSync(" <> show n <> " drifting)"
  show ClusterDesync = "Desync"
  show ClusterEmpty = "Empty"

-- | Compute overall cluster state
computeClusterState :: ViewportCluster -> ClusterState
computeClusterState cluster =
  let
    viewports = getAllViewports cluster
    total = Array.length viewports
    synced = Array.length $ Array.filter (\v -> isSynchronized v.syncState) viewports
    drifting = total - synced
  in
    if total == 0 then ClusterEmpty
    else if synced == total then ClusterSynced
    else if synced > total / 2 then ClusterPartialSync drifting
    else ClusterDesync

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // frame reconciliation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frame reconciliation result
type FrameReconciliation =
  { targetFrame :: FrameNumber
  , strategy :: ReconciliationStrategy
  , affectedViewports :: Array ViewportId
  }

-- | Reconciliation strategy
data ReconciliationStrategy
  = NoReconciliation            -- All in sync
  | CatchUp                     -- Slow viewports catch up
  | SlowDown                    -- Fast viewports slow down
  | MeetInMiddle                -- Both adjust
  | ForceResync                 -- All jump to authority frame

derive instance eqReconciliationStrategy :: Eq ReconciliationStrategy

instance showReconciliationStrategy :: Show ReconciliationStrategy where
  show NoReconciliation = "NoReconciliation"
  show CatchUp = "CatchUp"
  show SlowDown = "SlowDown"
  show MeetInMiddle = "MeetInMiddle"
  show ForceResync = "ForceResync"

-- | Reconcile frames across viewports
reconcileFrames :: ViewportCluster -> FrameReconciliation
reconcileFrames cluster =
  let
    viewports = getAllViewports cluster
    offsets = map _.frameOffset viewports
    maxOffset = foldl maxInt 0 offsets
    minOffset = foldl minInt 0 offsets
    spread = maxOffset - minOffset
    affected = Array.filter (\v -> v.frameOffset /= 0) viewports
                 # map _.viewportId
  in
    if spread == 0 then
      { targetFrame: cluster.currentFrame
      , strategy: NoReconciliation
      , affectedViewports: []
      }
    else if spread > 10 then
      { targetFrame: cluster.currentFrame
      , strategy: ForceResync
      , affectedViewports: map _.viewportId viewports
      }
    else if absInt minOffset > absInt maxOffset then
      { targetFrame: cluster.currentFrame
      , strategy: CatchUp
      , affectedViewports: affected
      }
    else if absInt maxOffset > absInt minOffset then
      { targetFrame: cluster.currentFrame
      , strategy: SlowDown
      , affectedViewports: affected
      }
    else
      { targetFrame: cluster.currentFrame
      , strategy: MeetInMiddle
      , affectedViewports: affected
      }

-- | Apply reconciliation to cluster
applyReconciliation :: FrameReconciliation -> ViewportCluster -> ViewportCluster
applyReconciliation recon cluster = case recon.strategy of
  NoReconciliation -> cluster
  ForceResync -> cluster
    { viewports = map (\v -> v { frameOffset = 0, syncState = Synchronized }) 
                      cluster.viewports 
    }
  _ -> cluster
    { viewports = map (adjustViewportOffset recon.strategy) cluster.viewports }

-- | Adjust viewport offset based on strategy
adjustViewportOffset :: ReconciliationStrategy -> ViewportSync -> ViewportSync
adjustViewportOffset strategy sync = case strategy of
  CatchUp -> 
    if sync.frameOffset < 0 
      then sync { frameOffset = sync.frameOffset + 1 }
      else sync
  SlowDown -> 
    if sync.frameOffset > 0 
      then sync { frameOffset = sync.frameOffset - 1 }
      else sync
  MeetInMiddle -> 
    if sync.frameOffset > 0 
      then sync { frameOffset = sync.frameOffset - 1 }
      else if sync.frameOffset < 0 
        then sync { frameOffset = sync.frameOffset + 1 }
        else sync
  _ -> sync

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // helper functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Minimum of two integers
minInt :: Int -> Int -> Int
minInt a b = if a <= b then a else b

-- | Maximum of two integers
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Absolute value for Int
absInt :: Int -> Int
absInt n = if n < 0 then negate n else n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // time authority integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create viewport sync with local authority
mkViewportSyncLocal :: ViewportId -> AgentId -> WallClock -> ViewportSync
mkViewportSyncLocal viewportId agentId currentTime =
  mkViewportSync viewportId (localAuthority agentId currentTime)

-- | Create viewport sync with network authority
mkViewportSyncNetwork :: ViewportId -> AgentId -> FrameTime -> FrameTime -> FrameTime -> Number -> ViewportSync
mkViewportSyncNetwork viewportId serverId serverTime offset rtt confidence =
  mkViewportSync viewportId (networkAuthority serverId serverTime offset rtt confidence)

-- | Check if viewport is using network authority
viewportUsesNetwork :: ViewportSync -> Boolean
viewportUsesNetwork sync = isNetworkAuthority sync.authority

-- | Check if viewport is using local authority
viewportUsesLocal :: ViewportSync -> Boolean
viewportUsesLocal sync = isLocalAuthority sync.authority

-- | Get viewport's authority time
getViewportAuthorityTime :: ViewportSync -> FrameTime
getViewportAuthorityTime sync = getAuthorityTime sync.authority

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // frame schedule integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute expected frame for viewport at given time
computeExpectedFrame :: FrameSchedule -> WallClock -> ViewportSync -> FrameNumber
computeExpectedFrame schedule currentTime sync =
  timeToFrame schedule currentTime + sync.frameOffset

-- | Compute time of next frame for viewport
computeNextFrameTime :: FrameSchedule -> WallClock -> FrameTime
computeNextFrameTime schedule currentTime =
  let currentFrame = timeToFrame schedule currentTime
  in frameToTime schedule (currentFrame + 1)

-- | Check if viewport is behind schedule
viewportIsBehind :: FrameSchedule -> WallClock -> FrameNumber -> ViewportSync -> Boolean
viewportIsBehind schedule currentTime actualFrame sync =
  let expected = computeExpectedFrame schedule currentTime sync
  in actualFrame < expected

-- | Check if viewport is ahead of schedule
viewportIsAhead :: FrameSchedule -> WallClock -> FrameNumber -> ViewportSync -> Boolean
viewportIsAhead schedule currentTime actualFrame sync =
  let expected = computeExpectedFrame schedule currentTime sync
  in actualFrame > expected

-- | Get frames per second from schedule
getScheduleFps :: FrameSchedule -> Number
getScheduleFps = framesPerSecond

-- | Get frame duration from schedule
getScheduleFrameDuration :: FrameSchedule -> FrameTime
getScheduleFrameDuration = frameDuration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // clock sync integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create viewport sync with clock sync state
mkViewportSyncWithClockSync :: ViewportId -> AgentId -> ClockSync -> WallClock -> ViewportSync
mkViewportSyncWithClockSync viewportId serverId clockSync localTime =
  let quality = syncQuality clockSync
      serverTime = localToServer clockSync localTime
      offset = serverTime - localTime
      rtt = 0.0  -- Not tracked here, would come from ClockSync
      confidence = syncQualityToNumber quality
  in mkViewportSyncNetwork viewportId serverId serverTime offset rtt confidence

-- | Convert sync quality to numeric confidence
syncQualityToNumber :: SyncQuality -> Number
syncQualityToNumber q = case q of
  SyncExcellent -> 1.0
  SyncGood -> 0.8
  SyncFair -> 0.5
  SyncPoor -> 0.2
  SyncUnsynced -> 0.0

-- | Check if viewport sync quality meets minimum
viewportMeetsSyncQuality :: SyncQuality -> ViewportSync -> Boolean
viewportMeetsSyncQuality minQuality sync = case sync.authority of
  LocalAuthority _ -> true  -- Local is always "synced" with itself
  NetworkAuthority r -> r.confidence >= syncQualityToNumber minQuality

-- | Convert local time to server time for viewport
viewportLocalToServer :: ClockSync -> WallClock -> WallClock
viewportLocalToServer = localToServer

-- | Convert server time to local time for viewport  
viewportServerToLocal :: ClockSync -> WallClock -> WallClock
viewportServerToLocal = serverToLocal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // vector clock integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | ViewportSync with vector clock for causal ordering
type ViewportSyncWithCausality =
  { sync :: ViewportSync
  , vectorClock :: VectorClock
  , lamportTime :: LamportTime
  }

-- | Create viewport sync with causality tracking
mkViewportSyncWithCausality :: ViewportId -> TimeAuthority -> ViewportSyncWithCausality
mkViewportSyncWithCausality viewportId authority =
  { sync: mkViewportSync viewportId authority
  , vectorClock: mkVectorClock viewportId
  , lamportTime: mkLamportTime
  }

-- | Tick causality clocks for local event
tickCausality :: ViewportSyncWithCausality -> ViewportSyncWithCausality
tickCausality vsc = vsc
  { vectorClock = vectorTick vsc.sync.viewportId vsc.vectorClock
  , lamportTime = lamportTick vsc.lamportTime
  }

-- | Receive causality update from another viewport
receiveCausality :: VectorClock -> LamportTime -> ViewportSyncWithCausality -> ViewportSyncWithCausality
receiveCausality remoteVc remoteLt vsc = vsc
  { vectorClock = vectorReceive vsc.sync.viewportId vsc.vectorClock remoteVc
  , lamportTime = lamportReceive vsc.lamportTime remoteLt
  }

-- | Check causal ordering between two viewport states
checkCausalOrder :: ViewportSyncWithCausality -> ViewportSyncWithCausality -> VectorOrdering
checkCausalOrder a b = vectorCompare a.vectorClock b.vectorClock

-- | Are two viewport states causally concurrent?
areConcurrent :: ViewportSyncWithCausality -> ViewportSyncWithCausality -> Boolean
areConcurrent a b = case checkCausalOrder a b of
  VectorConcurrent -> true
  _ -> false
