-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // gestural // gesture // tap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tap - single/double/triple tap gesture recognition.
-- |
-- | Models tap gestures with configurable tap count.
-- | Supports single, double, and triple tap detection.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Gestural.Gesture.Phase (GesturePhase)
-- |
-- | ## Dependents
-- | - Gestural.Gesture (re-exports)
-- | - Component.* (tap-enabled components)

module Hydrogen.Schema.Gestural.Gesture.Tap
  ( -- * Tap Count
    TapCount(TapCount)
  , tapCount
  , singleTap
  , doubleTap
  , tripleTap
  , unwrapTapCount
  , isSingleTap
  , isDoubleTap
  , isTripleTap
    -- * Tap State
  , TapState
  , tapState
  , noTap
  , tapPosition
  , isTapRecognized
    -- * Bounds
  , tapCountBounds
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Gestural.Gesture.Phase 
  ( GesturePhase(Possible)
  , isEnded
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // tap // count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of taps in a multi-tap gesture [1, 3]
-- |
-- | - 1: Single tap
-- | - 2: Double tap
-- | - 3: Triple tap (select paragraph in text)
newtype TapCount = TapCount Int

derive instance eqTapCount :: Eq TapCount
derive instance ordTapCount :: Ord TapCount

instance showTapCount :: Show TapCount where
  show (TapCount n) = show n <> " tap(s)"

-- | Create tap count (clamps to [1, 3])
tapCount :: Int -> TapCount
tapCount n = TapCount (max 1 (min 3 n))

-- | Single tap
singleTap :: TapCount
singleTap = TapCount 1

-- | Double tap
doubleTap :: TapCount
doubleTap = TapCount 2

-- | Triple tap
tripleTap :: TapCount
tripleTap = TapCount 3

-- | Extract raw count
unwrapTapCount :: TapCount -> Int
unwrapTapCount (TapCount n) = n

-- | Is this a single tap?
isSingleTap :: TapCount -> Boolean
isSingleTap (TapCount n) = n == 1

-- | Is this a double tap?
isDoubleTap :: TapCount -> Boolean
isDoubleTap (TapCount n) = n == 2

-- | Is this a triple tap?
isTripleTap :: TapCount -> Boolean
isTripleTap (TapCount n) = n == 3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for TapCount [1, 3]
-- |
-- | - 1: Single tap
-- | - 2: Double tap
-- | - 3: Triple tap (select paragraph in text)
tapCountBounds :: Bounded.IntBounds
tapCountBounds = Bounded.intBounds 1 3 "TapCount"
  "Number of taps in a multi-tap gesture (1=single, 2=double, 3=triple)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // tap // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of a tap gesture recognizer
-- |
-- | Tracks tap position, timing, and count for multi-tap detection.
type TapState =
  { phase :: GesturePhase       -- ^ Current recognition phase
  , count :: TapCount           -- ^ Number of taps detected
  , x :: Number                 -- ^ Tap X position (client coords)
  , y :: Number                 -- ^ Tap Y position (client coords)
  , timestamp :: Number         -- ^ Time of last tap (ms)
  , interval :: Number          -- ^ Time between taps (ms)
  }

-- | Create tap state
tapState :: GesturePhase -> TapCount -> Number -> Number -> Number -> TapState
tapState phase count x y ts =
  { phase
  , count
  , x
  , y
  , timestamp: ts
  , interval: 0.0
  }

-- | No tap detected
noTap :: TapState
noTap =
  { phase: Possible
  , count: singleTap
  , x: 0.0
  , y: 0.0
  , timestamp: 0.0
  , interval: 0.0
  }

-- | Get tap position
tapPosition :: TapState -> { x :: Number, y :: Number }
tapPosition ts = { x: ts.x, y: ts.y }

-- | Is tap gesture recognized?
isTapRecognized :: TapState -> Boolean
isTapRecognized ts = isEnded ts.phase
