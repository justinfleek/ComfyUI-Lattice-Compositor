-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // gestural // gesture // swipe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Swipe - directional swipe gesture recognition.
-- |
-- | Models quick directional movements with velocity thresholds.
-- | Supports four cardinal directions with velocity-based detection.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Math.Core (abs, sqrt)
-- | - Gestural.Gesture.Phase (GesturePhase, isEnded)
-- |
-- | ## Dependents
-- | - Gestural.Gesture (re-exports)
-- | - Component.* (swipe-enabled components)

module Hydrogen.Schema.Gestural.Gesture.Swipe
  ( -- * Swipe Direction
    SwipeDirection(SwipeUp, SwipeDown, SwipeLeft, SwipeRight)
  , allSwipeDirections
  , isSwipeHorizontal
  , isSwipeVertical
  , oppositeSwipe
  , swipeDirectionFromDelta
    -- * Swipe Threshold
  , SwipeVelocityThreshold(SwipeVelocityThreshold)
  , swipeVelocityThreshold
  , defaultSwipeThreshold
  , unwrapSwipeThreshold
    -- * Swipe State
  , SwipeState
  , swipeState
  , noSwipe
  , swipeVelocity
  , isSwipeRecognized
    -- * Bounds
  , swipeVelocityThresholdBounds
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Math.Core (abs, sqrt)
import Hydrogen.Schema.Gestural.Gesture.Phase 
  ( GesturePhase(Possible)
  , isEnded
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // swipe // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cardinal direction for swipe gestures
-- |
-- | Simplified to four cardinal directions for common use cases.
-- | For diagonal detection, use Motion.Direction instead.
data SwipeDirection
  = SwipeUp
  | SwipeDown
  | SwipeLeft
  | SwipeRight

derive instance eqSwipeDirection :: Eq SwipeDirection
derive instance ordSwipeDirection :: Ord SwipeDirection

instance showSwipeDirection :: Show SwipeDirection where
  show SwipeUp = "up"
  show SwipeDown = "down"
  show SwipeLeft = "left"
  show SwipeRight = "right"

-- | All swipe directions for enumeration
allSwipeDirections :: Array SwipeDirection
allSwipeDirections = [ SwipeUp, SwipeDown, SwipeLeft, SwipeRight ]

-- | Is swipe horizontal?
isSwipeHorizontal :: SwipeDirection -> Boolean
isSwipeHorizontal SwipeLeft = true
isSwipeHorizontal SwipeRight = true
isSwipeHorizontal _ = false

-- | Is swipe vertical?
isSwipeVertical :: SwipeDirection -> Boolean
isSwipeVertical SwipeUp = true
isSwipeVertical SwipeDown = true
isSwipeVertical _ = false

-- | Get opposite swipe direction
oppositeSwipe :: SwipeDirection -> SwipeDirection
oppositeSwipe SwipeUp = SwipeDown
oppositeSwipe SwipeDown = SwipeUp
oppositeSwipe SwipeLeft = SwipeRight
oppositeSwipe SwipeRight = SwipeLeft

-- | Determine swipe direction from delta values
-- |
-- | Uses dominant axis to determine cardinal direction.
swipeDirectionFromDelta :: Number -> Number -> SwipeDirection
swipeDirectionFromDelta dx dy
  | abs dx > abs dy = if dx > 0.0 then SwipeRight else SwipeLeft
  | otherwise = if dy > 0.0 then SwipeDown else SwipeUp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // swipe // threshold
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum velocity threshold for swipe recognition (px/ms)
-- |
-- | Default: 0.5 px/ms (500 px/s)
newtype SwipeVelocityThreshold = SwipeVelocityThreshold Number

derive instance eqSwipeVelocityThreshold :: Eq SwipeVelocityThreshold
derive instance ordSwipeVelocityThreshold :: Ord SwipeVelocityThreshold

instance showSwipeVelocityThreshold :: Show SwipeVelocityThreshold where
  show (SwipeVelocityThreshold v) = show v <> " px/ms threshold"

-- | Create swipe velocity threshold (clamps to [0.1, 5.0])
swipeVelocityThreshold :: Number -> SwipeVelocityThreshold
swipeVelocityThreshold v = SwipeVelocityThreshold (max 0.1 (min 5.0 v))

-- | Default swipe velocity threshold (0.5 px/ms)
defaultSwipeThreshold :: SwipeVelocityThreshold
defaultSwipeThreshold = SwipeVelocityThreshold 0.5

-- | Extract threshold value
unwrapSwipeThreshold :: SwipeVelocityThreshold -> Number
unwrapSwipeThreshold (SwipeVelocityThreshold v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for SwipeVelocityThreshold [0.1, 5.0] px/ms
-- |
-- | Default: 0.5 px/ms (500 px/s)
-- | Range allows for both slow deliberate swipes and fast flicks.
swipeVelocityThresholdBounds :: Bounded.NumberBounds
swipeVelocityThresholdBounds = Bounded.numberBounds 0.1 5.0 "SwipeVelocityThreshold"
  "Minimum velocity threshold for swipe recognition in pixels per millisecond"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // swipe // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of a swipe gesture recognizer
type SwipeState =
  { phase :: GesturePhase          -- ^ Current recognition phase
  , direction :: SwipeDirection    -- ^ Detected swipe direction
  , startX :: Number               -- ^ Start X position
  , startY :: Number               -- ^ Start Y position
  , endX :: Number                 -- ^ End X position
  , endY :: Number                 -- ^ End Y position
  , velocityX :: Number            -- ^ X velocity (px/ms)
  , velocityY :: Number            -- ^ Y velocity (px/ms)
  , distance :: Number             -- ^ Total distance traveled
  , duration :: Number             -- ^ Swipe duration (ms)
  }

-- | Create swipe state
swipeState 
  :: GesturePhase 
  -> SwipeDirection 
  -> Number 
  -> Number 
  -> Number 
  -> Number 
  -> SwipeState
swipeState phase dir startX startY endX endY =
  { phase
  , direction: dir
  , startX
  , startY
  , endX
  , endY
  , velocityX: 0.0
  , velocityY: 0.0
  , distance: 0.0
  , duration: 0.0
  }

-- | No swipe detected
noSwipe :: SwipeState
noSwipe =
  { phase: Possible
  , direction: SwipeRight
  , startX: 0.0
  , startY: 0.0
  , endX: 0.0
  , endY: 0.0
  , velocityX: 0.0
  , velocityY: 0.0
  , distance: 0.0
  , duration: 0.0
  }

-- | Get swipe velocity magnitude
swipeVelocity :: SwipeState -> Number
swipeVelocity ss = 
  let vx = ss.velocityX
      vy = ss.velocityY
  in sqrt (vx * vx + vy * vy)

-- | Is swipe gesture recognized?
isSwipeRecognized :: SwipeState -> Boolean
isSwipeRecognized ss = isEnded ss.phase
