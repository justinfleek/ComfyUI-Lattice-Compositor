-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // reactive // presence-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PresenceState - component mount/unmount lifecycle and animation states.
-- |
-- | Models the presence lifecycle for animated enter/exit transitions.
-- | Critical for Framer Motion-style AnimatePresence patterns.

module Hydrogen.Schema.Reactive.PresenceState
  ( -- * Presence Phase
    PresencePhase(..)
  , isEntering
  , isEntered
  , isExiting
  , isExited
  , isPresent
  , isAnimating
  -- * Mount Status
  , MountStatus(..)
  , isMounted
  , isUnmounted
  , isMounting
  , isUnmounting
  -- * Animation Direction
  , AnimationDirection(..)
  , isForward
  , isBackward
  , isNoDirection
  -- * Presence Config
  , PresenceConfig
  , presenceConfig
  , defaultPresenceConfig
  , instantConfig
  , withEnterDuration
  , withExitDuration
  -- * Presence State (Molecule)
  , PresenceState
  , presenceState
  , initialPresence
  , enteringPresence
  , enteredPresence
  , exitingPresence
  , exitedPresence
  -- * Presence Lifecycle
  , startEnter
  , completeEnter
  , startExit
  , completeExit
  , cancelAnimation
  -- * Computed Properties
  , shouldRender
  , shouldAnimate
  , animationProgress
  , animationRemainingTime
  -- * Presence Group (Compound)
  , PresenceGroup
  , presenceGroup
  , emptyGroup
  , addToGroup
  , removeFromGroup
  , groupPendingExits
  , isGroupAnimating
  ) where

import Prelude

import Data.Array (filter, length, snoc)
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // presence phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lifecycle phase of component presence
data PresencePhase
  = PhaseEntering   -- ^ Enter animation in progress
  | PhaseEntered    -- ^ Fully visible and interactive
  | PhaseExiting    -- ^ Exit animation in progress
  | PhaseExited     -- ^ Animation complete, ready to unmount

derive instance eqPresencePhase :: Eq PresencePhase
derive instance ordPresencePhase :: Ord PresencePhase

instance showPresencePhase :: Show PresencePhase where
  show PhaseEntering = "entering"
  show PhaseEntered = "entered"
  show PhaseExiting = "exiting"
  show PhaseExited = "exited"

isEntering :: PresencePhase -> Boolean
isEntering PhaseEntering = true
isEntering _ = false

isEntered :: PresencePhase -> Boolean
isEntered PhaseEntered = true
isEntered _ = false

isExiting :: PresencePhase -> Boolean
isExiting PhaseExiting = true
isExiting _ = false

isExited :: PresencePhase -> Boolean
isExited PhaseExited = true
isExited _ = false

-- | Is component currently present (visible)?
isPresent :: PresencePhase -> Boolean
isPresent PhaseEntering = true
isPresent PhaseEntered = true
isPresent PhaseExiting = true
isPresent PhaseExited = false

-- | Is animation in progress?
isAnimating :: PresencePhase -> Boolean
isAnimating PhaseEntering = true
isAnimating PhaseExiting = true
isAnimating _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // mount status
-- ═════════════════════════════════════════════════════════════════════════════

-- | DOM mount lifecycle status
data MountStatus
  = Unmounted    -- ^ Not in DOM
  | Mounting     -- ^ Being added to DOM
  | Mounted      -- ^ In DOM
  | Unmounting   -- ^ Being removed from DOM

derive instance eqMountStatus :: Eq MountStatus
derive instance ordMountStatus :: Ord MountStatus

instance showMountStatus :: Show MountStatus where
  show Unmounted = "unmounted"
  show Mounting = "mounting"
  show Mounted = "mounted"
  show Unmounting = "unmounting"

isMounted :: MountStatus -> Boolean
isMounted Mounted = true
isMounted _ = false

isUnmounted :: MountStatus -> Boolean
isUnmounted Unmounted = true
isUnmounted _ = false

isMounting :: MountStatus -> Boolean
isMounting Mounting = true
isMounting _ = false

isUnmounting :: MountStatus -> Boolean
isUnmounting Unmounting = true
isUnmounting _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animation direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of navigation/animation
data AnimationDirection
  = Forward    -- ^ Moving forward in navigation (enter from right)
  | Backward   -- ^ Moving backward in navigation (enter from left)
  | NoDirection -- ^ No directional animation

derive instance eqAnimationDirection :: Eq AnimationDirection
derive instance ordAnimationDirection :: Ord AnimationDirection

instance showAnimationDirection :: Show AnimationDirection where
  show Forward = "forward"
  show Backward = "backward"
  show NoDirection = "none"

isForward :: AnimationDirection -> Boolean
isForward Forward = true
isForward _ = false

isBackward :: AnimationDirection -> Boolean
isBackward Backward = true
isBackward _ = false

isNoDirection :: AnimationDirection -> Boolean
isNoDirection NoDirection = true
isNoDirection _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // presence config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for presence animations
type PresenceConfig =
  { enterDurationMs :: Number     -- ^ Enter animation duration
  , exitDurationMs :: Number      -- ^ Exit animation duration
  , enterDelay :: Number          -- ^ Delay before enter starts
  , exitDelay :: Number           -- ^ Delay before exit starts
  , animateOnMount :: Boolean     -- ^ Animate first appearance
  , exitBeforeEnter :: Boolean    -- ^ Wait for exit before enter (mode="wait")
  }

-- | Create presence config
presenceConfig :: Number -> Number -> PresenceConfig
presenceConfig enterDuration exitDuration =
  { enterDurationMs: max 0.0 enterDuration
  , exitDurationMs: max 0.0 exitDuration
  , enterDelay: 0.0
  , exitDelay: 0.0
  , animateOnMount: true
  , exitBeforeEnter: false
  }

-- | Default presence config (300ms enter/exit)
defaultPresenceConfig :: PresenceConfig
defaultPresenceConfig = presenceConfig 300.0 300.0

-- | Instant transitions (no animation)
instantConfig :: PresenceConfig
instantConfig = presenceConfig 0.0 0.0

-- | Set enter duration
withEnterDuration :: Number -> PresenceConfig -> PresenceConfig
withEnterDuration ms config = config { enterDurationMs = max 0.0 ms }

-- | Set exit duration
withExitDuration :: Number -> PresenceConfig -> PresenceConfig
withExitDuration ms config = config { exitDurationMs = max 0.0 ms }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // presence state molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete presence state for a component
type PresenceState =
  { phase :: PresencePhase
  , mount :: MountStatus
  , direction :: AnimationDirection
  , config :: PresenceConfig
  , startedAt :: Maybe Number       -- ^ Animation start timestamp
  , progress :: Number              -- ^ Animation progress 0.0 - 1.0
  }

-- | Create presence state
presenceState :: PresencePhase -> MountStatus -> PresenceConfig -> PresenceState
presenceState phase mount config =
  { phase
  , mount
  , direction: NoDirection
  , config
  , startedAt: Nothing
  , progress: if isEntered phase then 1.0 else 0.0
  }

-- | Initial presence (not yet mounted)
initialPresence :: PresenceConfig -> PresenceState
initialPresence = presenceState PhaseExited Unmounted

-- | Entering presence
enteringPresence :: PresenceConfig -> PresenceState
enteringPresence config = (presenceState PhaseEntering Mounting config)
  { progress = 0.0 }

-- | Fully entered presence
enteredPresence :: PresenceConfig -> PresenceState
enteredPresence config = (presenceState PhaseEntered Mounted config)
  { progress = 1.0 }

-- | Exiting presence
exitingPresence :: PresenceConfig -> PresenceState
exitingPresence config = (presenceState PhaseExiting Unmounting config)
  { progress = 1.0 }

-- | Fully exited presence
exitedPresence :: PresenceConfig -> PresenceState
exitedPresence config = (presenceState PhaseExited Unmounted config)
  { progress = 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // presence lifecycle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Begin enter animation
startEnter :: Number -> PresenceState -> PresenceState
startEnter timestamp ps = ps
  { phase = PhaseEntering
  , mount = Mounting
  , startedAt = Just timestamp
  , progress = 0.0
  }

-- | Complete enter animation
completeEnter :: PresenceState -> PresenceState
completeEnter ps = ps
  { phase = PhaseEntered
  , mount = Mounted
  , startedAt = Nothing
  , progress = 1.0
  }

-- | Begin exit animation
startExit :: Number -> PresenceState -> PresenceState
startExit timestamp ps = ps
  { phase = PhaseExiting
  , mount = Unmounting
  , startedAt = Just timestamp
  , progress = 1.0
  }

-- | Complete exit animation
completeExit :: PresenceState -> PresenceState
completeExit ps = ps
  { phase = PhaseExited
  , mount = Unmounted
  , startedAt = Nothing
  , progress = 0.0
  }

-- | Cancel ongoing animation
cancelAnimation :: PresenceState -> PresenceState
cancelAnimation ps = ps { startedAt = Nothing }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Should component be rendered in DOM?
shouldRender :: PresenceState -> Boolean
shouldRender ps = isPresent ps.phase

-- | Should component be animating?
shouldAnimate :: PresenceState -> Boolean
shouldAnimate ps = isAnimating ps.phase

-- | Get current animation progress (0.0 - 1.0)
animationProgress :: PresenceState -> Number
animationProgress ps = ps.progress

-- | Calculate remaining animation time in ms
animationRemainingTime :: Number -> PresenceState -> Number
animationRemainingTime currentTime ps = case ps.startedAt of
  Nothing -> 0.0
  Just start ->
    let duration = if isEntering ps.phase 
          then ps.config.enterDurationMs 
          else ps.config.exitDurationMs
        elapsed = currentTime - start
    in max 0.0 (duration - elapsed)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // presence group compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Manages multiple presence states (for AnimatePresence)
type PresenceGroup =
  { items :: Array { key :: String, presence :: PresenceState }
  , pendingExits :: Array String    -- ^ Keys waiting to exit
  , exitBeforeEnter :: Boolean      -- ^ Wait for exits before enters
  }

-- | Create presence group
presenceGroup :: Boolean -> PresenceGroup
presenceGroup exitBeforeEnter =
  { items: []
  , pendingExits: []
  , exitBeforeEnter
  }

-- | Empty group (default mode)
emptyGroup :: PresenceGroup
emptyGroup = presenceGroup false

-- | Add item to group
addToGroup :: String -> PresenceState -> PresenceGroup -> PresenceGroup
addToGroup key presence group =
  group { items = snoc group.items { key, presence } }

-- | Mark item for removal (start exit)
removeFromGroup :: String -> PresenceGroup -> PresenceGroup
removeFromGroup key group =
  group { pendingExits = snoc group.pendingExits key }

-- | Get items pending exit
groupPendingExits :: PresenceGroup -> Array String
groupPendingExits group = group.pendingExits

-- | Is any item in group animating?
isGroupAnimating :: PresenceGroup -> Boolean
isGroupAnimating group = 
  length (filter (\item -> shouldAnimate item.presence) group.items) > 0
