-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // gestural // touch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Touch - multi-touch tracking and pinch/rotate/scale states.
-- |
-- | Models multi-finger gestures for mobile and trackpad interactions.
-- | Provides the foundation for pinch-to-zoom, rotate, and pan gestures.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Array (length, head, filter)
-- | - Data.Maybe (Maybe)
-- | - Gestural.Pointer (PointerPosition, Pressure, PointerSize)
-- | - Gestural.Motion (Velocity2D, Distance)
-- |
-- | ## Dependents
-- | - Gestural.Gesture (uses TouchState for gesture recognition)
-- | - Component.* (touch-enabled components)

module Hydrogen.Schema.Gestural.Touch
  ( -- * Touch Point
    TouchPoint
  , touchPoint
  , touchId
  , touchPosition
  , touchPressure
  , touchSize
    -- * Touch Count
  , TouchCount(TouchCount)
  , touchCount
  , maxTouches
  , unwrapTouchCount
  , isSingleTouch
  , isMultiTouch
    -- * Pinch State
  , PinchState
  , pinchState
  , noPinch
  , pinchScale
  , pinchCenter
  , pinchDistance
  , isPinching
  , isPinchingIn
  , isPinchingOut
    -- * Rotate State
  , RotateState
  , rotateState
  , noRotation
  , rotationAngle
  , rotationDelta
  , rotationCenter
  , isRotating
    -- * Touch State (Compound)
  , TouchState
  , touchState
  , noTouches
  , singleTouchState
  , twoFingerState
  , addTouch
  , removeTouch
  , updateTouch
  , touchPointCount
  , primaryTouch
  , allTouches
    -- * Edge Swipe
  , ScreenEdge(EdgeTop, EdgeBottom, EdgeLeft, EdgeRight)
  , EdgeSwipeState
  , edgeSwipe
  , noEdgeSwipe
  , beginEdgeSwipe
  , updateEdgeSwipe
  , isEdgeSwipePastThreshold
  , cancelEdgeSwipe
    -- * Three-Finger Swipe
  , ThreeFingerDirection(ThreeFingerUp, ThreeFingerDown, ThreeFingerLeft, ThreeFingerRight)
  , ThreeFingerSwipeState
  , noThreeFingerSwipe
  , beginThreeFingerSwipe
  , updateThreeFingerSwipe
  , isThreeFingerSwipeRecognized
  , cancelThreeFingerSwipe
    -- * Two-Finger Tap
  , TwoFingerTapState
  , noTwoFingerTap
  , recognizeTwoFingerTap
  
  -- * Bounds
  , touchCountBounds
  ) where

import Prelude

import Data.Array (filter, head, length, snoc)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core (sqrt, atan2)
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Gestural.Pointer 
  ( PointerPosition
  , Pressure
  , PointerSize
  , clientX
  , clientY
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // touch point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Individual touch point on the screen
-- |
-- | Each finger contact creates a unique TouchPoint with:
-- | - Unique identifier (stable during touch lifetime)
-- | - Position in multiple coordinate systems
-- | - Pressure and contact area
type TouchPoint =
  { id :: Int                    -- ^ Unique touch identifier
  , position :: PointerPosition  -- ^ Position in all coordinate systems
  , pressure :: Pressure         -- ^ Touch pressure (0-1)
  , size :: PointerSize          -- ^ Contact area dimensions
  , timestamp :: Number          -- ^ Event timestamp (ms)
  }

-- | Create touch point
touchPoint :: Int -> PointerPosition -> Pressure -> PointerSize -> Number -> TouchPoint
touchPoint id pos pres sz ts =
  { id
  , position: pos
  , pressure: pres
  , size: sz
  , timestamp: ts
  }

-- | Get touch identifier
touchId :: TouchPoint -> Int
touchId tp = tp.id

-- | Get touch position
touchPosition :: TouchPoint -> PointerPosition
touchPosition tp = tp.position

-- | Get touch pressure
touchPressure :: TouchPoint -> Pressure
touchPressure tp = tp.pressure

-- | Get touch contact size
touchSize :: TouchPoint -> PointerSize
touchSize tp = tp.size

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // touch count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of active touch points [0, 10]
-- |
-- | Most devices support up to 10 simultaneous touches.
-- | Bounded to prevent overflow in multi-touch calculations.
newtype TouchCount = TouchCount Int

derive instance eqTouchCount :: Eq TouchCount
derive instance ordTouchCount :: Ord TouchCount

instance showTouchCount :: Show TouchCount where
  show (TouchCount n) = show n <> " touches"

-- | Create touch count (clamps to [0, 10])
touchCount :: Int -> TouchCount
touchCount n = TouchCount (max 0 (min 10 n))

-- | Maximum supported touch count
maxTouches :: TouchCount
maxTouches = TouchCount 10

-- | Extract raw count
unwrapTouchCount :: TouchCount -> Int
unwrapTouchCount (TouchCount n) = n

-- | Is single touch?
isSingleTouch :: TouchCount -> Boolean
isSingleTouch (TouchCount n) = n == 1

-- | Is multi-touch? (2 or more)
isMultiTouch :: TouchCount -> Boolean
isMultiTouch (TouchCount n) = n >= 2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // pinch state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of a pinch (two-finger scale) gesture
-- |
-- | Tracks the scale factor relative to initial distance.
-- | Scale > 1.0 = zooming in, scale < 1.0 = zooming out.
type PinchState =
  { scale :: Number              -- ^ Current scale factor (1.0 = no change)
  , initialDistance :: Number    -- ^ Distance between fingers at start
  , currentDistance :: Number    -- ^ Current distance between fingers
  , centerX :: Number            -- ^ Center X of pinch (midpoint)
  , centerY :: Number            -- ^ Center Y of pinch (midpoint)
  , active :: Boolean            -- ^ Is pinch gesture active
  }

-- | Create pinch state
pinchState :: Number -> Number -> Number -> Number -> Number -> PinchState
pinchState initDist currDist cx cy scale' =
  { scale: scale'
  , initialDistance: max 1.0 initDist
  , currentDistance: max 1.0 currDist
  , centerX: cx
  , centerY: cy
  , active: true
  }

-- | No active pinch
noPinch :: PinchState
noPinch =
  { scale: 1.0
  , initialDistance: 0.0
  , currentDistance: 0.0
  , centerX: 0.0
  , centerY: 0.0
  , active: false
  }

-- | Get current scale factor
pinchScale :: PinchState -> Number
pinchScale ps = ps.scale

-- | Get pinch center point
pinchCenter :: PinchState -> { x :: Number, y :: Number }
pinchCenter ps = { x: ps.centerX, y: ps.centerY }

-- | Get current distance between fingers
pinchDistance :: PinchState -> Number
pinchDistance ps = ps.currentDistance

-- | Is pinch gesture active?
isPinching :: PinchState -> Boolean
isPinching ps = ps.active

-- | Is pinching in (zooming out)?
isPinchingIn :: PinchState -> Boolean
isPinchingIn ps = ps.active && ps.scale < 0.95

-- | Is pinching out (zooming in)?
isPinchingOut :: PinchState -> Boolean
isPinchingOut ps = ps.active && ps.scale > 1.05

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // rotate state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of a two-finger rotation gesture
-- |
-- | Tracks rotation angle in radians.
type RotateState =
  { angle :: Number           -- ^ Current rotation angle (radians)
  , initialAngle :: Number    -- ^ Angle at gesture start
  , delta :: Number           -- ^ Change since last update
  , centerX :: Number         -- ^ Center X of rotation
  , centerY :: Number         -- ^ Center Y of rotation
  , active :: Boolean         -- ^ Is rotation gesture active
  }

-- | Create rotate state
rotateState :: Number -> Number -> Number -> Number -> Number -> RotateState
rotateState initAngle currAngle delta cx cy =
  { angle: currAngle
  , initialAngle: initAngle
  , delta
  , centerX: cx
  , centerY: cy
  , active: true
  }

-- | No active rotation
noRotation :: RotateState
noRotation =
  { angle: 0.0
  , initialAngle: 0.0
  , delta: 0.0
  , centerX: 0.0
  , centerY: 0.0
  , active: false
  }

-- | Get current rotation angle (radians)
rotationAngle :: RotateState -> Number
rotationAngle rs = rs.angle

-- | Get rotation delta since last update
rotationDelta :: RotateState -> Number
rotationDelta rs = rs.delta

-- | Get rotation center point
rotationCenter :: RotateState -> { x :: Number, y :: Number }
rotationCenter rs = { x: rs.centerX, y: rs.centerY }

-- | Is rotation gesture active?
isRotating :: RotateState -> Boolean
isRotating rs = rs.active

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // touch state (compound)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete multi-touch state
-- |
-- | Tracks all active touches and derived gesture states (pinch, rotate).
type TouchState =
  { touches :: Array TouchPoint     -- ^ All active touch points
  , count :: TouchCount             -- ^ Number of active touches
  , pinch :: PinchState             -- ^ Pinch gesture state
  , rotate :: RotateState           -- ^ Rotate gesture state
  , timestamp :: Number             -- ^ Last update timestamp
  }

-- | Create touch state from touch points
touchState :: Array TouchPoint -> Number -> TouchState
touchState tps ts =
  let cnt = touchCount (length tps)
      pinch' = computePinch tps
      rotate' = computeRotation tps
  in { touches: tps
     , count: cnt
     , pinch: pinch'
     , rotate: rotate'
     , timestamp: ts
     }

-- | No active touches
noTouches :: TouchState
noTouches = touchState [] 0.0

-- | Single touch state
singleTouchState :: TouchPoint -> TouchState
singleTouchState tp = touchState [tp] tp.timestamp

-- | Two-finger touch state (for pinch/rotate)
twoFingerState :: TouchPoint -> TouchPoint -> TouchState
twoFingerState tp1 tp2 = 
  touchState [tp1, tp2] (max tp1.timestamp tp2.timestamp)

-- | Add a new touch point
addTouch :: TouchPoint -> TouchState -> TouchState
addTouch tp ts = 
  touchState (snoc ts.touches tp) tp.timestamp

-- | Remove a touch point by ID
removeTouch :: Int -> TouchState -> TouchState
removeTouch id ts =
  touchState (filter (\t -> t.id /= id) ts.touches) ts.timestamp

-- | Update an existing touch point
updateTouch :: TouchPoint -> TouchState -> TouchState
updateTouch tp ts =
  let updated = map (\t -> if t.id == tp.id then tp else t) ts.touches
  in touchState updated tp.timestamp

-- | Get number of active touches
touchPointCount :: TouchState -> Int
touchPointCount ts = unwrapTouchCount ts.count

-- | Get primary (first) touch point
primaryTouch :: TouchState -> Maybe TouchPoint
primaryTouch ts = head ts.touches

-- | Get all active touch points
allTouches :: TouchState -> Array TouchPoint
allTouches ts = ts.touches

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // internal computations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute pinch state from touch points
computePinch :: Array TouchPoint -> PinchState
computePinch tps
  | length tps < 2 = noPinch
  | otherwise = case head tps of
      Nothing -> noPinch
      Just t1 -> case head (filter (\t -> t.id /= t1.id) tps) of
        Nothing -> noPinch
        Just t2 ->
          let x1 = clientX t1.position
              y1 = clientY t1.position
              x2 = clientX t2.position
              y2 = clientY t2.position
              dx = x2 - x1
              dy = y2 - y1
              dist = sqrt (dx * dx + dy * dy)
              cx = (x1 + x2) / 2.0
              cy = (y1 + y2) / 2.0
          in pinchState dist dist cx cy 1.0

-- | Compute rotation state from touch points
computeRotation :: Array TouchPoint -> RotateState
computeRotation tps
  | length tps < 2 = noRotation
  | otherwise = case head tps of
      Nothing -> noRotation
      Just t1 -> case head (filter (\t -> t.id /= t1.id) tps) of
        Nothing -> noRotation
        Just t2 ->
          let x1 = clientX t1.position
              y1 = clientY t1.position
              x2 = clientX t2.position
              y2 = clientY t2.position
              dx = x2 - x1
              dy = y2 - y1
              angle = atan2 dy dx
              cx = (x1 + x2) / 2.0
              cy = (y1 + y2) / 2.0
          in rotateState angle angle 0.0 cx cy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for TouchCount
-- |
-- | Min: 0 (no touches)
-- | Max: 10 (practical multi-touch limit)
touchCountBounds :: Bounded.IntBounds
touchCountBounds = Bounded.intBounds 0 10 "touchCount" "Number of active touches (0-10)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // multi-finger gestures
-- ═════════════════════════════════════════════════════════════════════════════

-- | Edge for edge swipe gestures
data ScreenEdge
  = EdgeTop
  | EdgeBottom
  | EdgeLeft
  | EdgeRight

derive instance eqScreenEdge :: Eq ScreenEdge
derive instance ordScreenEdge :: Ord ScreenEdge

instance showScreenEdge :: Show ScreenEdge where
  show EdgeTop = "top"
  show EdgeBottom = "bottom"
  show EdgeLeft = "left"
  show EdgeRight = "right"

-- | Edge swipe gesture state (swipe from screen edge)
-- |
-- | Used for system gestures like:
-- | - iOS: swipe from bottom for home, left edge for back
-- | - Android: swipe from left edge for drawer
type EdgeSwipeState =
  { edge :: ScreenEdge           -- ^ Which edge the swipe started from
  , distance :: Number           -- ^ Distance traveled from edge (px)
  , progress :: Number           -- ^ Progress 0-1 toward threshold
  , threshold :: Number          -- ^ Distance to trigger action (px)
  , velocity :: Number           -- ^ Current swipe velocity (px/s)
  , active :: Boolean            -- ^ Is edge swipe active
  }

-- | Create edge swipe state
edgeSwipe :: ScreenEdge -> Number -> EdgeSwipeState
edgeSwipe edge threshold =
  { edge
  , distance: 0.0
  , progress: 0.0
  , threshold
  , velocity: 0.0
  , active: false
  }

-- | No active edge swipe
noEdgeSwipe :: EdgeSwipeState
noEdgeSwipe = edgeSwipe EdgeLeft 50.0

-- | Begin edge swipe from position
beginEdgeSwipe :: ScreenEdge -> Number -> Number -> EdgeSwipeState -> EdgeSwipeState
beginEdgeSwipe edge edgeDistance threshold es = es
  { edge = edge
  , distance = edgeDistance
  , progress = if threshold > 0.0 then min 1.0 (edgeDistance / threshold) else 0.0
  , threshold = threshold
  , active = true
  }

-- | Update edge swipe distance
updateEdgeSwipe :: Number -> Number -> EdgeSwipeState -> EdgeSwipeState
updateEdgeSwipe newDistance newVelocity es = es
  { distance = newDistance
  , progress = if es.threshold > 0.0 then min 1.0 (newDistance / es.threshold) else 0.0
  , velocity = newVelocity
  }

-- | Is edge swipe past threshold?
isEdgeSwipePastThreshold :: EdgeSwipeState -> Boolean
isEdgeSwipePastThreshold es = es.progress >= 1.0

-- | Cancel edge swipe
cancelEdgeSwipe :: EdgeSwipeState -> EdgeSwipeState
cancelEdgeSwipe es = es { active = false, distance = 0.0, progress = 0.0 }

-- | Three-finger swipe direction
data ThreeFingerDirection
  = ThreeFingerUp      -- ^ Mission Control / App Switcher
  | ThreeFingerDown    -- ^ App Expose
  | ThreeFingerLeft    -- ^ Next desktop
  | ThreeFingerRight   -- ^ Previous desktop

derive instance eqThreeFingerDirection :: Eq ThreeFingerDirection
derive instance ordThreeFingerDirection :: Ord ThreeFingerDirection

instance showThreeFingerDirection :: Show ThreeFingerDirection where
  show ThreeFingerUp = "three-finger-up"
  show ThreeFingerDown = "three-finger-down"
  show ThreeFingerLeft = "three-finger-left"
  show ThreeFingerRight = "three-finger-right"

-- | Three-finger swipe state (system navigation gestures)
-- |
-- | Used for trackpad gestures:
-- | - macOS: three-finger swipe for desktop navigation
-- | - iOS: three-finger swipe on iPad for app switching
type ThreeFingerSwipeState =
  { direction :: Maybe ThreeFingerDirection  -- ^ Detected direction
  , distance :: Number                       -- ^ Total distance traveled
  , velocity :: Number                       -- ^ Current velocity (px/s)
  , touchCount :: TouchCount                 -- ^ Number of fingers (should be 3)
  , active :: Boolean                        -- ^ Is gesture active
  , centerX :: Number                        -- ^ Center point X
  , centerY :: Number                        -- ^ Center point Y
  }

-- | No active three-finger swipe
noThreeFingerSwipe :: ThreeFingerSwipeState
noThreeFingerSwipe =
  { direction: Nothing
  , distance: 0.0
  , velocity: 0.0
  , touchCount: touchCount 0
  , active: false
  , centerX: 0.0
  , centerY: 0.0
  }

-- | Begin three-finger swipe
beginThreeFingerSwipe :: Number -> Number -> ThreeFingerSwipeState
beginThreeFingerSwipe centerX centerY =
  { direction: Nothing
  , distance: 0.0
  , velocity: 0.0
  , touchCount: touchCount 3
  , active: true
  , centerX
  , centerY
  }

-- | Update three-finger swipe with delta
updateThreeFingerSwipe :: Number -> Number -> Number -> ThreeFingerSwipeState -> ThreeFingerSwipeState
updateThreeFingerSwipe deltaX deltaY velocity tfs =
  let
    newDistance = sqrt (deltaX * deltaX + deltaY * deltaY)
    dir = detectThreeFingerDirection deltaX deltaY
  in tfs
    { direction = dir
    , distance = tfs.distance + newDistance
    , velocity = velocity
    , centerX = tfs.centerX + deltaX
    , centerY = tfs.centerY + deltaY
    }

-- | Detect three-finger direction from delta
detectThreeFingerDirection :: Number -> Number -> Maybe ThreeFingerDirection
detectThreeFingerDirection dx dy
  | abs dx < 10.0 && abs dy < 10.0 = Nothing  -- Not enough movement
  | abs dy > abs dx && dy < 0.0 = Just ThreeFingerUp
  | abs dy > abs dx && dy > 0.0 = Just ThreeFingerDown
  | abs dx > abs dy && dx < 0.0 = Just ThreeFingerLeft
  | abs dx > abs dy && dx > 0.0 = Just ThreeFingerRight
  | otherwise = Nothing

-- | Is three-finger swipe recognized?
isThreeFingerSwipeRecognized :: ThreeFingerSwipeState -> Boolean
isThreeFingerSwipeRecognized tfs = 
  tfs.active 
  && tfs.distance > 50.0 
  && case tfs.direction of
       Just _ -> true
       Nothing -> false

-- | Cancel three-finger swipe
cancelThreeFingerSwipe :: ThreeFingerSwipeState -> ThreeFingerSwipeState
cancelThreeFingerSwipe tfs = tfs { active = false }

-- | Two-finger tap gesture state
-- |
-- | Right-click equivalent on trackpads and touchscreens.
type TwoFingerTapState =
  { recognized :: Boolean         -- ^ Was gesture recognized
  , centerX :: Number             -- ^ Center X of the two fingers
  , centerY :: Number             -- ^ Center Y of the two fingers
  , timestamp :: Number           -- ^ When gesture was recognized
  }

-- | No two-finger tap
noTwoFingerTap :: TwoFingerTapState
noTwoFingerTap =
  { recognized: false
  , centerX: 0.0
  , centerY: 0.0
  , timestamp: 0.0
  }

-- | Recognize two-finger tap
recognizeTwoFingerTap :: Number -> Number -> Number -> TwoFingerTapState
recognizeTwoFingerTap centerX centerY timestamp =
  { recognized: true
  , centerX
  , centerY
  , timestamp
  }

-- | Helper: absolute value
abs :: Number -> Number
abs n = if n < 0.0 then (-n) else n
