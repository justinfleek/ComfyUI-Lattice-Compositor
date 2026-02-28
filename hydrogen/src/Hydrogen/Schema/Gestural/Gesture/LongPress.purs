-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // gestural // gesture // longpress
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LongPress - press-and-hold gesture recognition.
-- |
-- | Models long press gestures with configurable threshold.
-- | Tracks progress toward threshold for visual feedback.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Gestural.Gesture.Phase (GesturePhase, isActive)
-- |
-- | ## Dependents
-- | - Gestural.Gesture (re-exports)
-- | - Component.* (long press enabled components)

module Hydrogen.Schema.Gestural.Gesture.LongPress
  ( -- * Long Press Threshold
    LongPressThreshold(LongPressThreshold)
  , longPressThreshold
  , defaultLongPressThreshold
  , unwrapLongPressThreshold
    -- * Long Press State
  , LongPressState
  , longPressState
  , noLongPress
  , updateLongPressDuration
  , longPressPosition
  , isLongPressTriggered
  , isLongPressActive
    -- * Bounds
  , longPressThresholdBounds
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Gestural.Gesture.Phase 
  ( GesturePhase(Possible)
  , isActive
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // long // press threshold
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum duration threshold for long press (ms)
-- |
-- | Standard thresholds:
-- | - iOS: 500ms
-- | - Android: 400ms
-- | - Web: configurable, typically 500ms
newtype LongPressThreshold = LongPressThreshold Number

derive instance eqLongPressThreshold :: Eq LongPressThreshold
derive instance ordLongPressThreshold :: Ord LongPressThreshold

instance showLongPressThreshold :: Show LongPressThreshold where
  show (LongPressThreshold ms) = show ms <> "ms threshold"

-- | Create long press threshold (clamps to [100, 2000])
longPressThreshold :: Number -> LongPressThreshold
longPressThreshold ms = LongPressThreshold (max 100.0 (min 2000.0 ms))

-- | Default long press threshold (500ms)
defaultLongPressThreshold :: LongPressThreshold
defaultLongPressThreshold = LongPressThreshold 500.0

-- | Extract threshold value
unwrapLongPressThreshold :: LongPressThreshold -> Number
unwrapLongPressThreshold (LongPressThreshold ms) = ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for LongPressThreshold [100, 2000] ms
-- |
-- | Standard thresholds:
-- | - iOS: 500ms
-- | - Android: 400ms
-- | - Web: configurable, typically 500ms
longPressThresholdBounds :: Bounded.NumberBounds
longPressThresholdBounds = Bounded.numberBounds 100.0 2000.0 "LongPressThreshold"
  "Minimum duration threshold for long press in milliseconds"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // long // press state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of a long press gesture recognizer
-- |
-- | Tracks press position, duration, and progress toward threshold.
type LongPressState =
  { phase :: GesturePhase           -- ^ Current recognition phase
  , x :: Number                     -- ^ Press X position (client coords)
  , y :: Number                     -- ^ Press Y position (client coords)
  , startTime :: Number             -- ^ Time press began (ms)
  , currentDuration :: Number       -- ^ How long pressed (ms)
  , threshold :: LongPressThreshold -- ^ Duration required for recognition
  , progress :: Number              -- ^ Progress toward threshold (0-1)
  }

-- | Create long press state
longPressState 
  :: GesturePhase 
  -> Number 
  -> Number 
  -> Number 
  -> LongPressThreshold 
  -> LongPressState
longPressState phase x y startTime threshold =
  { phase
  , x
  , y
  , startTime
  , currentDuration: 0.0
  , threshold
  , progress: 0.0
  }

-- | No long press active
noLongPress :: LongPressState
noLongPress =
  { phase: Possible
  , x: 0.0
  , y: 0.0
  , startTime: 0.0
  , currentDuration: 0.0
  , threshold: defaultLongPressThreshold
  , progress: 0.0
  }

-- | Update long press duration and progress
updateLongPressDuration :: Number -> LongPressState -> LongPressState
updateLongPressDuration currentTime lps =
  let duration = currentTime - lps.startTime
      thresholdMs = unwrapLongPressThreshold lps.threshold
      prog = min 1.0 (duration / thresholdMs)
  in lps { currentDuration = duration, progress = prog }

-- | Get long press position
longPressPosition :: LongPressState -> { x :: Number, y :: Number }
longPressPosition lps = { x: lps.x, y: lps.y }

-- | Has long press threshold been reached?
isLongPressTriggered :: LongPressState -> Boolean
isLongPressTriggered lps = lps.progress >= 1.0

-- | Is long press currently active (held but not yet triggered)?
isLongPressActive :: LongPressState -> Boolean
isLongPressActive lps = isActive lps.phase && lps.progress < 1.0
