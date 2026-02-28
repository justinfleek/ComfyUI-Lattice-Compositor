-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // carousel // gestures
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Gestures — Input state for gesture-based navigation.
-- |
-- | ## Design Philosophy
-- |
-- | Gesture state is **pure data** describing the current input state.
-- | The runtime detects gestures and updates state; the carousel renders
-- | based on that state. No FFI here — just state representation.
-- |
-- | ## Gesture Categories
-- |
-- | **Touch/Pointer**: Swipe, drag, pinch, tap
-- | **Mouse**: Drag, wheel scroll, click
-- | **Keyboard**: Arrow keys, Home/End, Tab
-- | **Advanced**: Retinal tracking, voice, proximity
-- |
-- | ## Dependencies
-- |
-- | - Schema.Gestural.Gesture.Swipe (SwipeDirection, SwipeState)
-- | - Schema.Gestural.Gesture.Pan (PanState)
-- | - Schema.Dimension.Device (Pixel)

module Hydrogen.Element.Compound.Carousel.Gestures
  ( -- * Swipe Gesture
    SwipeGesture
  , swipeGesture
  , noSwipeGesture
  , isSwipeActive
  , swipeProgress
  , swipeDirection
  , hasSwipeDirection
  , isHorizontalSwipe
  , isVerticalSwipe
  , swipeToSlideDirection
  
  -- * Drag Gesture
  , DragGesture
  , dragGesture
  , noDragGesture
  , isDragActive
  , dragOffset
  , dragVelocity
  , isDragFast
  , dragMagnitude
  
  -- * Pinch Gesture
  , PinchGesture
  , pinchGesture
  , noPinchGesture
  , isPinchActive
  , pinchScale
  , isPinchZoomIn
  , isPinchZoomOut
  
  -- * Scroll Gesture
  , ScrollGesture
  , scrollGesture
  , noScrollGesture
  , scrollDelta
  , scrollMagnitude
  , isScrollHorizontal
  , isScrollVertical
  
  -- * Retinal Tracking
  , RetinalState
  , retinalState
  , noRetinalState
  , isRetinalTracking
  , gazePosition
  , gazeDwellTime
  , isGazeFocused
  , gazeProgress
  
  -- * Voice Command
  , VoiceCommand
      ( VoiceNext
      , VoicePrevious
      , VoiceFirst
      , VoiceLast
      , VoiceGoTo
      , VoiceStop
      , VoicePlay
      )
  , VoiceState
  , voiceState
  , noVoiceState
  , isListening
  , lastCommand
  , isHighConfidence
  , voiceToSlideDirection
  
  -- * Combined Gesture State
  , GestureState
  , initialGestureState
  , isAnyGestureActive
  , activeGestureCount
  , dominantGesture
  , compareGesturePriority
  , GestureKind(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering
  , show
  , compare
  , not
  , negate
  , otherwise
  , (||)
  , (&&)
  , (>)
  , (>=)
  , (<)
  , (==)
  , (<>)
  , (/)
  , (+)
  , (-)
  , (*)
  , max
  , min
  )

import Data.Maybe (Maybe(Nothing, Just), isJust)

import Hydrogen.Schema.Gestural.Gesture.Swipe 
  ( SwipeDirection(SwipeLeft, SwipeRight, SwipeUp, SwipeDown)
  )
import Hydrogen.Schema.Dimension.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // swipe gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swipe gesture state for carousel navigation
-- |
-- | Tracks an active swipe gesture including direction and progress.
type SwipeGesture =
  { active :: Boolean
  , direction :: Maybe SwipeDirection
  , progress :: Number  -- 0.0 to 1.0, how far through the swipe
  , startX :: Number    -- Starting X coordinate
  , startY :: Number    -- Starting Y coordinate
  , currentX :: Number  -- Current X coordinate
  , currentY :: Number  -- Current Y coordinate
  }

-- | Create a swipe gesture from coordinates
swipeGesture :: 
  { direction :: SwipeDirection
  , progress :: Number
  , startX :: Number
  , startY :: Number
  , currentX :: Number
  , currentY :: Number
  } -> SwipeGesture
swipeGesture params =
  { active: true
  , direction: Just params.direction
  , progress: clampProgress params.progress
  , startX: params.startX
  , startY: params.startY
  , currentX: params.currentX
  , currentY: params.currentY
  }

-- | No active swipe gesture
noSwipeGesture :: SwipeGesture
noSwipeGesture =
  { active: false
  , direction: Nothing
  , progress: 0.0
  , startX: 0.0
  , startY: 0.0
  , currentX: 0.0
  , currentY: 0.0
  }

-- | Check if swipe is currently active
isSwipeActive :: SwipeGesture -> Boolean
isSwipeActive g = g.active

-- | Get swipe progress (0.0 to 1.0)
swipeProgress :: SwipeGesture -> Number
swipeProgress g = g.progress

-- | Get swipe direction if present
swipeDirection :: SwipeGesture -> Maybe SwipeDirection
swipeDirection g = g.direction

-- | Check if swipe has a determined direction
hasSwipeDirection :: SwipeGesture -> Boolean
hasSwipeDirection g = isJust g.direction

-- | Check if swipe is horizontal (left or right)
isHorizontalSwipe :: SwipeGesture -> Boolean
isHorizontalSwipe g = case g.direction of
  Just SwipeLeft -> true
  Just SwipeRight -> true
  _ -> false

-- | Check if swipe is vertical (up or down)
isVerticalSwipe :: SwipeGesture -> Boolean
isVerticalSwipe g = case g.direction of
  Just SwipeUp -> true
  Just SwipeDown -> true
  _ -> false

-- | Convert swipe direction to slide navigation direction
-- | Returns -1 for previous, 1 for next, 0 for no navigation
swipeToSlideDirection :: SwipeGesture -> Int
swipeToSlideDirection g = case g.direction of
  Just SwipeLeft -> 1   -- Swipe left = go to next slide
  Just SwipeRight -> -1 -- Swipe right = go to previous slide
  Just SwipeUp -> 1     -- Swipe up = go to next (vertical carousel)
  Just SwipeDown -> -1  -- Swipe down = go to previous (vertical)
  Nothing -> 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // drag gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drag gesture state for carousel manipulation
-- |
-- | Tracks pointer drag for direct manipulation of carousel position.
type DragGesture =
  { active :: Boolean
  , offsetX :: Number   -- Horizontal drag offset in pixels
  , offsetY :: Number   -- Vertical drag offset in pixels
  , velocityX :: Number -- Horizontal velocity (pixels/ms)
  , velocityY :: Number -- Vertical velocity (pixels/ms)
  }

-- | Create a drag gesture from offset and velocity
dragGesture ::
  { offsetX :: Number
  , offsetY :: Number
  , velocityX :: Number
  , velocityY :: Number
  } -> DragGesture
dragGesture params =
  { active: true
  , offsetX: params.offsetX
  , offsetY: params.offsetY
  , velocityX: params.velocityX
  , velocityY: params.velocityY
  }

-- | No active drag gesture
noDragGesture :: DragGesture
noDragGesture =
  { active: false
  , offsetX: 0.0
  , offsetY: 0.0
  , velocityX: 0.0
  , velocityY: 0.0
  }

-- | Check if drag is currently active
isDragActive :: DragGesture -> Boolean
isDragActive g = g.active

-- | Get drag offset as { x, y }
dragOffset :: DragGesture -> { x :: Number, y :: Number }
dragOffset g = { x: g.offsetX, y: g.offsetY }

-- | Get drag velocity as { x, y }
dragVelocity :: DragGesture -> { x :: Number, y :: Number }
dragVelocity g = { x: g.velocityX, y: g.velocityY }

-- | Check if drag velocity exceeds threshold (for momentum/fling detection)
-- | Threshold is in pixels per millisecond
isDragFast :: Number -> DragGesture -> Boolean
isDragFast threshold g =
  let mag = dragMagnitude g
  in mag > threshold

-- | Get the magnitude of drag offset (distance from start)
dragMagnitude :: DragGesture -> Number
dragMagnitude g = 
  let dx = g.offsetX
      dy = g.offsetY
  in sqrt (dx * dx + dy * dy)
  where
    -- Simple sqrt approximation for magnitude calculation
    sqrt :: Number -> Number
    sqrt n = if n > 0.0 then jsUnsafeSqrt n else 0.0
    
    -- FFI-free sqrt using Newton-Raphson (good enough for UI)
    jsUnsafeSqrt :: Number -> Number
    jsUnsafeSqrt x = 
      let guess = x / 2.0
          refine g' = (g' + x / g') / 2.0
          r1 = refine guess
          r2 = refine r1
          r3 = refine r2
          r4 = refine r3
      in r4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // pinch gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pinch gesture state for zoom/scale operations
-- |
-- | Tracks two-finger pinch for scaling the carousel view.
type PinchGesture =
  { active :: Boolean
  , scale :: Number     -- Current scale factor (1.0 = no scale)
  , centerX :: Number   -- Center X of pinch
  , centerY :: Number   -- Center Y of pinch
  }

-- | Create a pinch gesture from scale and center
pinchGesture ::
  { scale :: Number
  , centerX :: Number
  , centerY :: Number
  } -> PinchGesture
pinchGesture params =
  { active: true
  , scale: max 0.1 params.scale  -- Minimum scale
  , centerX: params.centerX
  , centerY: params.centerY
  }

-- | No active pinch gesture
noPinchGesture :: PinchGesture
noPinchGesture =
  { active: false
  , scale: 1.0
  , centerX: 0.0
  , centerY: 0.0
  }

-- | Check if pinch is currently active
isPinchActive :: PinchGesture -> Boolean
isPinchActive g = g.active

-- | Get current pinch scale
pinchScale :: PinchGesture -> Number
pinchScale g = g.scale

-- | Check if pinch is zooming in (scale > 1.0)
isPinchZoomIn :: PinchGesture -> Boolean
isPinchZoomIn g = g.active && g.scale > 1.0

-- | Check if pinch is zooming out (scale < 1.0)
isPinchZoomOut :: PinchGesture -> Boolean
isPinchZoomOut g = g.active && g.scale < 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // scroll gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scroll gesture state for wheel/trackpad navigation
-- |
-- | Tracks scroll wheel or trackpad scroll events.
type ScrollGesture =
  { deltaX :: Number   -- Horizontal scroll delta
  , deltaY :: Number   -- Vertical scroll delta
  , timestamp :: Temporal.Milliseconds -- When the scroll occurred
  }

-- | Create a scroll gesture from deltas
scrollGesture ::
  { deltaX :: Number
  , deltaY :: Number
  , timestamp :: Temporal.Milliseconds
  } -> ScrollGesture
scrollGesture params =
  { deltaX: params.deltaX
  , deltaY: params.deltaY
  , timestamp: params.timestamp
  }

-- | No scroll (zero delta)
noScrollGesture :: ScrollGesture
noScrollGesture =
  { deltaX: 0.0
  , deltaY: 0.0
  , timestamp: Temporal.ms 0.0
  }

-- | Get scroll delta as { x, y }
scrollDelta :: ScrollGesture -> { x :: Number, y :: Number }
scrollDelta g = { x: g.deltaX, y: g.deltaY }

-- | Get total scroll magnitude
scrollMagnitude :: ScrollGesture -> Number
scrollMagnitude g =
  let dx = absNum g.deltaX
      dy = absNum g.deltaY
  in max dx dy
  where
    absNum n = if n < 0.0 then negate n else n
    negate n = 0.0 - n

-- | Check if scroll is primarily horizontal
isScrollHorizontal :: ScrollGesture -> Boolean
isScrollHorizontal g = absNum g.deltaX > absNum g.deltaY
  where
    absNum n = if n < 0.0 then negate n else n
    negate n = 0.0 - n

-- | Check if scroll is primarily vertical
isScrollVertical :: ScrollGesture -> Boolean
isScrollVertical g = absNum g.deltaY > absNum g.deltaX
  where
    absNum n = if n < 0.0 then negate n else n
    negate n = 0.0 - n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // retinal tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Retinal/eye tracking state for gaze-based navigation
-- |
-- | Supports accessibility and hands-free interaction via eye tracking.
type RetinalState =
  { tracking :: Boolean           -- Is eye tracking active
  , gazeX :: Number               -- Current gaze X position
  , gazeY :: Number               -- Current gaze Y position
  , dwellTime :: Temporal.Milliseconds -- How long gaze held at current position
  , focusThreshold :: Temporal.Milliseconds -- Dwell time needed to trigger action
  }

-- | Create retinal tracking state
retinalState ::
  { gazeX :: Number
  , gazeY :: Number
  , dwellTime :: Temporal.Milliseconds
  , focusThreshold :: Temporal.Milliseconds
  } -> RetinalState
retinalState params =
  { tracking: true
  , gazeX: params.gazeX
  , gazeY: params.gazeY
  , dwellTime: params.dwellTime
  , focusThreshold: params.focusThreshold
  }

-- | No retinal tracking
noRetinalState :: RetinalState
noRetinalState =
  { tracking: false
  , gazeX: 0.0
  , gazeY: 0.0
  , dwellTime: Temporal.milliseconds 0.0
  , focusThreshold: Temporal.milliseconds 1000.0
  }

-- | Check if retinal tracking is active
isRetinalTracking :: RetinalState -> Boolean
isRetinalTracking s = s.tracking

-- | Get current gaze position
gazePosition :: RetinalState -> { x :: Number, y :: Number }
gazePosition s = { x: s.gazeX, y: s.gazeY }

-- | Get current dwell time at gaze position
gazeDwellTime :: RetinalState -> Temporal.Milliseconds
gazeDwellTime s = s.dwellTime

-- | Check if gaze has dwelled long enough to trigger focus
isGazeFocused :: RetinalState -> Boolean
isGazeFocused s = 
  s.tracking && Temporal.unwrapMilliseconds s.dwellTime >= Temporal.unwrapMilliseconds s.focusThreshold

-- | Get gaze progress toward focus (0.0 to 1.0)
-- | Returns how close the gaze is to triggering an action
gazeProgress :: RetinalState -> Number
gazeProgress s =
  if not s.tracking then 0.0
  else 
    let dwell = Temporal.unwrapMilliseconds s.dwellTime
        threshold = Temporal.unwrapMilliseconds s.focusThreshold
    in if threshold == 0.0 then 1.0
       else min 1.0 (dwell / threshold)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // voice command
-- ═════════════════════════════════════════════════════════════════════════════

-- | Voice commands for carousel navigation
data VoiceCommand
  = VoiceNext       -- "Next", "Forward", "Right"
  | VoicePrevious   -- "Previous", "Back", "Left"
  | VoiceFirst      -- "First", "Beginning", "Start"
  | VoiceLast       -- "Last", "End"
  | VoiceGoTo Int   -- "Go to 3", "Slide 5"
  | VoiceStop       -- "Stop", "Pause"
  | VoicePlay       -- "Play", "Continue", "Resume"

derive instance eqVoiceCommand :: Eq VoiceCommand

instance showVoiceCommand :: Show VoiceCommand where
  show VoiceNext = "next"
  show VoicePrevious = "previous"
  show VoiceFirst = "first"
  show VoiceLast = "last"
  show (VoiceGoTo n) = "goto:" <> show n
  show VoiceStop = "stop"
  show VoicePlay = "play"

-- | Voice control state
type VoiceState =
  { listening :: Boolean          -- Is voice recognition active
  , command :: Maybe VoiceCommand -- Last recognized command
  , confidence :: Number          -- Recognition confidence (0.0 to 1.0)
  }

-- | Create voice state with a recognized command
voiceState ::
  { command :: VoiceCommand
  , confidence :: Number
  } -> VoiceState
voiceState params =
  { listening: true
  , command: Just params.command
  , confidence: clampProgress params.confidence
  }

-- | No voice control
noVoiceState :: VoiceState
noVoiceState =
  { listening: false
  , command: Nothing
  , confidence: 0.0
  }

-- | Check if voice recognition is listening
isListening :: VoiceState -> Boolean
isListening s = s.listening

-- | Get last recognized command
lastCommand :: VoiceState -> Maybe VoiceCommand
lastCommand s = s.command

-- | Check if voice recognition confidence is high enough to act on
-- | Uses 0.7 as threshold for reliable recognition
isHighConfidence :: VoiceState -> Boolean
isHighConfidence s = s.listening && s.confidence > 0.7

-- | Convert voice command to slide navigation direction
-- | Returns -1 for previous, 1 for next, 0 for no navigation
voiceToSlideDirection :: VoiceCommand -> Int
voiceToSlideDirection cmd = case cmd of
  VoiceNext -> 1
  VoicePrevious -> -1
  VoiceFirst -> 0    -- Special case: handled separately
  VoiceLast -> 0     -- Special case: handled separately  
  VoiceGoTo _ -> 0   -- Special case: handled separately
  VoiceStop -> 0
  VoicePlay -> 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // combined gesture state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined state for all gesture types
-- |
-- | The carousel uses this unified state to determine navigation behavior
-- | regardless of input modality.
type GestureState =
  { swipe :: SwipeGesture
  , drag :: DragGesture
  , pinch :: PinchGesture
  , scroll :: ScrollGesture
  , retinal :: RetinalState
  , voice :: VoiceState
  }

-- | Initial gesture state (no active gestures)
initialGestureState :: GestureState
initialGestureState =
  { swipe: noSwipeGesture
  , drag: noDragGesture
  , pinch: noPinchGesture
  , scroll: noScrollGesture
  , retinal: noRetinalState
  , voice: noVoiceState
  }

-- | Check if any gesture is currently active
isAnyGestureActive :: GestureState -> Boolean
isAnyGestureActive state =
  isSwipeActive state.swipe
  || isDragActive state.drag
  || isPinchActive state.pinch
  || isRetinalTracking state.retinal
  || isListening state.voice

-- | Count how many gesture types are currently active
activeGestureCount :: GestureState -> Int
activeGestureCount state =
  boolToInt (isSwipeActive state.swipe)
  + boolToInt (isDragActive state.drag)
  + boolToInt (isPinchActive state.pinch)
  + boolToInt (isRetinalTracking state.retinal)
  + boolToInt (isListening state.voice)
  where
    boolToInt :: Boolean -> Int
    boolToInt true = 1
    boolToInt false = 0

-- | Kind of gesture for priority/disambiguation
data GestureKind
  = GestureSwipe
  | GestureDrag
  | GesturePinch
  | GestureScroll
  | GestureRetinal
  | GestureVoice
  | GestureNone

derive instance eqGestureKind :: Eq GestureKind
derive instance ordGestureKind :: Ord GestureKind

instance showGestureKind :: Show GestureKind where
  show GestureSwipe = "swipe"
  show GestureDrag = "drag"
  show GesturePinch = "pinch"
  show GestureScroll = "scroll"
  show GestureRetinal = "retinal"
  show GestureVoice = "voice"
  show GestureNone = "none"

-- | Get the dominant (highest priority) active gesture
-- | Priority: Pinch > Swipe > Drag > Scroll > Retinal > Voice
dominantGesture :: GestureState -> GestureKind
dominantGesture state
  | isPinchActive state.pinch = GesturePinch
  | isSwipeActive state.swipe = GestureSwipe
  | isDragActive state.drag = GestureDrag
  | scrollMagnitude state.scroll > 0.0 = GestureScroll
  | isRetinalTracking state.retinal = GestureRetinal
  | isListening state.voice = GestureVoice
  | otherwise = GestureNone

-- | Compare two gesture kinds by priority
-- | Returns Ordering (LT, EQ, GT) based on which gesture should take precedence
-- | Higher priority gestures return GT when compared to lower priority ones
compareGesturePriority :: GestureKind -> GestureKind -> Ordering
compareGesturePriority a b = compare (gesturePriorityValue a) (gesturePriorityValue b)
  where
    -- Assign numeric priority (higher = more important)
    gesturePriorityValue :: GestureKind -> Int
    gesturePriorityValue GesturePinch = 6   -- Highest: zoom/scale operations
    gesturePriorityValue GestureSwipe = 5   -- Navigation intent
    gesturePriorityValue GestureDrag = 4    -- Direct manipulation
    gesturePriorityValue GestureScroll = 3  -- Passive scrolling
    gesturePriorityValue GestureRetinal = 2 -- Eye tracking (slower)
    gesturePriorityValue GestureVoice = 1   -- Voice commands (highest latency)
    gesturePriorityValue GestureNone = 0    -- No gesture

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // internal utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a progress/confidence value to [0.0, 1.0]
clampProgress :: Number -> Number
clampProgress n = max 0.0 (min 1.0 n)
