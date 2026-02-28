-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // motion // gesture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Touch and mouse gesture recognition
-- |
-- | Unified gesture system supporting touch, mouse, and pointer events
-- | with velocity tracking and gesture composition.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.Gesture as G
-- |
-- | -- Create a pan gesture recognizer
-- | panGesture <- G.createPanGesture element
-- |   { onStart: \state -> Console.log "Pan started"
-- |   , onMove: \state -> Console.log $ "Moving: " <> show state.delta
-- |   , onEnd: \state -> Console.log "Pan ended"
-- |   , threshold: 10.0
-- |   }
-- |
-- | -- Create a pinch gesture for zooming
-- | pinchGesture <- G.createPinchGesture element
-- |   { onPinch: \state -> setScale state.scale
-- |   , onEnd: \state -> commitScale state.scale
-- |   }
-- |
-- | -- Swipe gesture with direction
-- | swipeGesture <- G.createSwipeGesture element
-- |   { onSwipe: \dir -> case dir of
-- |       G.SwipeLeft -> prevSlide
-- |       G.SwipeRight -> nextSlide
-- |       _ -> pure unit
-- |   , velocityThreshold: 0.5
-- |   }
-- |
-- | -- Compose gestures
-- | G.composeGestures [panGesture, pinchGesture]
-- |
-- | -- Clean up
-- | G.destroyGesture panGesture
-- | ```
module Hydrogen.Motion.Gesture
  ( -- * Gesture State
    GestureState(..)
  , Point
  , Velocity
    -- * Pan Gesture
  , PanGesture
  , PanConfig
  , PanState
  , createPanGesture
  , defaultPanConfig
    -- * Pinch Gesture
  , PinchGesture
  , PinchConfig
  , PinchState
  , createPinchGesture
  , defaultPinchConfig
    -- * Rotate Gesture
  , RotateGesture
  , RotateConfig
  , RotateState
  , createRotateGesture
  , defaultRotateConfig
    -- * Swipe Gesture
  , SwipeGesture
  , SwipeConfig
  , SwipeDirection(..)
  , createSwipeGesture
  , defaultSwipeConfig
    -- * Long Press
  , LongPressGesture
  , LongPressConfig
  , createLongPressGesture
  , defaultLongPressConfig
    -- * Double Tap
  , DoubleTapGesture
  , DoubleTapConfig
  , createDoubleTapGesture
  , defaultDoubleTapConfig
    -- * Gesture Composition
  , GestureRecognizer
  , composeGestures
  , enableGesture
  , disableGesture
  , destroyGesture
    -- * Velocity Tracking
  , VelocityTracker
  , createVelocityTracker
  , trackPoint
  , getVelocity
  , resetTracker
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Data.Time.Duration (Milliseconds(Milliseconds))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Web.DOM.Element (Element)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gesture lifecycle state
data GestureState
  = Idle       -- ^ No gesture in progress
  | Active     -- ^ Gesture is active
  | Ended      -- ^ Gesture has ended

derive instance eqGestureState :: Eq GestureState

instance showGestureState :: Show GestureState where
  show Idle = "Idle"
  show Active = "Active"
  show Ended = "Ended"

-- | 2D point
type Point =
  { x :: Number
  , y :: Number
  }

-- | 2D velocity (units per second)
type Velocity =
  { vx :: Number
  , vy :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // pan gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pan gesture recognizer
foreign import data PanGesture :: Type

-- | Pan gesture state
type PanState =
  { state :: GestureState
  , start :: Point
  , current :: Point
  , delta :: Point
  , offset :: Point
  , velocity :: Velocity
  }

-- | Pan gesture configuration
type PanConfig =
  { onStart :: PanState -> Effect Unit
  , onMove :: PanState -> Effect Unit
  , onEnd :: PanState -> Effect Unit
  , threshold :: Number           -- ^ Minimum distance before pan starts
  , lockAxis :: Boolean           -- ^ Lock to dominant axis
  , preventScroll :: Boolean      -- ^ Prevent page scrolling
  }

-- | Default pan configuration
defaultPanConfig :: PanConfig
defaultPanConfig =
  { onStart: \_ -> pure unit
  , onMove: \_ -> pure unit
  , onEnd: \_ -> pure unit
  , threshold: 0.0
  , lockAxis: false
  , preventScroll: true
  }

-- | Create a pan gesture recognizer on an element
foreign import createPanGestureImpl
  :: Element
  -> { onStart :: PanStateJS -> Effect Unit
     , onMove :: PanStateJS -> Effect Unit
     , onEnd :: PanStateJS -> Effect Unit
     , threshold :: Number
     , lockAxis :: Boolean
     , preventScroll :: Boolean
     }
  -> Effect PanGesture

-- Internal JS state type
type PanStateJS =
  { state :: String
  , startX :: Number
  , startY :: Number
  , currentX :: Number
  , currentY :: Number
  , deltaX :: Number
  , deltaY :: Number
  , offsetX :: Number
  , offsetY :: Number
  , velocityX :: Number
  , velocityY :: Number
  }

panStateFromJS :: PanStateJS -> PanState
panStateFromJS js =
  { state: stateFromString js.state
  , start: { x: js.startX, y: js.startY }
  , current: { x: js.currentX, y: js.currentY }
  , delta: { x: js.deltaX, y: js.deltaY }
  , offset: { x: js.offsetX, y: js.offsetY }
  , velocity: { vx: js.velocityX, vy: js.velocityY }
  }
  where
  stateFromString "active" = Active
  stateFromString "ended" = Ended
  stateFromString _ = Idle

createPanGesture :: Element -> PanConfig -> Effect PanGesture
createPanGesture element config =
  createPanGestureImpl element
    { onStart: \js -> config.onStart (panStateFromJS js)
    , onMove: \js -> config.onMove (panStateFromJS js)
    , onEnd: \js -> config.onEnd (panStateFromJS js)
    , threshold: config.threshold
    , lockAxis: config.lockAxis
    , preventScroll: config.preventScroll
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // pinch gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pinch gesture recognizer
foreign import data PinchGesture :: Type

-- | Pinch gesture state
type PinchState =
  { state :: GestureState
  , scale :: Number           -- ^ Current scale (1.0 = no scale)
  , initialScale :: Number    -- ^ Scale at gesture start
  , center :: Point           -- ^ Center point between fingers
  , distance :: Number        -- ^ Distance between fingers
  }

-- | Pinch gesture configuration
type PinchConfig =
  { onStart :: PinchState -> Effect Unit
  , onPinch :: PinchState -> Effect Unit
  , onEnd :: PinchState -> Effect Unit
  , minScale :: Number        -- ^ Minimum scale limit
  , maxScale :: Number        -- ^ Maximum scale limit
  }

-- | Default pinch configuration
defaultPinchConfig :: PinchConfig
defaultPinchConfig =
  { onStart: \_ -> pure unit
  , onPinch: \_ -> pure unit
  , onEnd: \_ -> pure unit
  , minScale: 0.1
  , maxScale: 10.0
  }

-- Internal JS state type
type PinchStateJS =
  { state :: String
  , scale :: Number
  , initialScale :: Number
  , centerX :: Number
  , centerY :: Number
  , distance :: Number
  }

pinchStateFromJS :: PinchStateJS -> PinchState
pinchStateFromJS js =
  { state: stateFromString js.state
  , scale: js.scale
  , initialScale: js.initialScale
  , center: { x: js.centerX, y: js.centerY }
  , distance: js.distance
  }
  where
  stateFromString "active" = Active
  stateFromString "ended" = Ended
  stateFromString _ = Idle

foreign import createPinchGestureImpl
  :: Element
  -> { onStart :: PinchStateJS -> Effect Unit
     , onPinch :: PinchStateJS -> Effect Unit
     , onEnd :: PinchStateJS -> Effect Unit
     , minScale :: Number
     , maxScale :: Number
     }
  -> Effect PinchGesture

createPinchGesture :: Element -> PinchConfig -> Effect PinchGesture
createPinchGesture element config =
  createPinchGestureImpl element
    { onStart: \js -> config.onStart (pinchStateFromJS js)
    , onPinch: \js -> config.onPinch (pinchStateFromJS js)
    , onEnd: \js -> config.onEnd (pinchStateFromJS js)
    , minScale: config.minScale
    , maxScale: config.maxScale
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // rotate gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate gesture recognizer
foreign import data RotateGesture :: Type

-- | Rotate gesture state
type RotateState =
  { state :: GestureState
  , rotation :: Number        -- ^ Current rotation in degrees
  , initialRotation :: Number -- ^ Rotation at gesture start
  , center :: Point           -- ^ Center point of rotation
  , velocity :: Number        -- ^ Angular velocity (degrees/second)
  }

-- | Rotate gesture configuration
type RotateConfig =
  { onStart :: RotateState -> Effect Unit
  , onRotate :: RotateState -> Effect Unit
  , onEnd :: RotateState -> Effect Unit
  , threshold :: Number       -- ^ Minimum rotation before gesture activates
  }

-- | Default rotate configuration
defaultRotateConfig :: RotateConfig
defaultRotateConfig =
  { onStart: \_ -> pure unit
  , onRotate: \_ -> pure unit
  , onEnd: \_ -> pure unit
  , threshold: 0.0
  }

-- Internal JS state type
type RotateStateJS =
  { state :: String
  , rotation :: Number
  , initialRotation :: Number
  , centerX :: Number
  , centerY :: Number
  , velocity :: Number
  }

rotateStateFromJS :: RotateStateJS -> RotateState
rotateStateFromJS js =
  { state: stateFromString js.state
  , rotation: js.rotation
  , initialRotation: js.initialRotation
  , center: { x: js.centerX, y: js.centerY }
  , velocity: js.velocity
  }
  where
  stateFromString "active" = Active
  stateFromString "ended" = Ended
  stateFromString _ = Idle

foreign import createRotateGestureImpl
  :: Element
  -> { onStart :: RotateStateJS -> Effect Unit
     , onRotate :: RotateStateJS -> Effect Unit
     , onEnd :: RotateStateJS -> Effect Unit
     , threshold :: Number
     }
  -> Effect RotateGesture

createRotateGesture :: Element -> RotateConfig -> Effect RotateGesture
createRotateGesture element config =
  createRotateGestureImpl element
    { onStart: \js -> config.onStart (rotateStateFromJS js)
    , onRotate: \js -> config.onRotate (rotateStateFromJS js)
    , onEnd: \js -> config.onEnd (rotateStateFromJS js)
    , threshold: config.threshold
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // swipe gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swipe gesture recognizer
foreign import data SwipeGesture :: Type

-- | Swipe direction
data SwipeDirection
  = SwipeLeft
  | SwipeRight
  | SwipeUp
  | SwipeDown

derive instance eqSwipeDirection :: Eq SwipeDirection

instance showSwipeDirection :: Show SwipeDirection where
  show SwipeLeft = "SwipeLeft"
  show SwipeRight = "SwipeRight"
  show SwipeUp = "SwipeUp"
  show SwipeDown = "SwipeDown"

swipeDirectionFromString :: String -> Maybe SwipeDirection
swipeDirectionFromString "left" = Just SwipeLeft
swipeDirectionFromString "right" = Just SwipeRight
swipeDirectionFromString "up" = Just SwipeUp
swipeDirectionFromString "down" = Just SwipeDown
swipeDirectionFromString _ = Nothing

-- | Swipe gesture configuration
type SwipeConfig =
  { onSwipe :: SwipeDirection -> Effect Unit
  , velocityThreshold :: Number   -- ^ Minimum velocity to trigger swipe
  , distanceThreshold :: Number   -- ^ Minimum distance for swipe
  , maxDuration :: Milliseconds   -- ^ Maximum swipe duration
  }

-- | Default swipe configuration
defaultSwipeConfig :: SwipeConfig
defaultSwipeConfig =
  { onSwipe: \_ -> pure unit
  , velocityThreshold: 0.5
  , distanceThreshold: 50.0
  , maxDuration: Milliseconds 300.0
  }

foreign import createSwipeGestureImpl
  :: Element
  -> { onSwipe :: String -> Effect Unit
     , velocityThreshold :: Number
     , distanceThreshold :: Number
     , maxDuration :: Number
     }
  -> Effect SwipeGesture

createSwipeGesture :: Element -> SwipeConfig -> Effect SwipeGesture
createSwipeGesture element config =
  createSwipeGestureImpl element
    { onSwipe: \dir -> case swipeDirectionFromString dir of
        Just d -> config.onSwipe d
        Nothing -> pure unit
    , velocityThreshold: config.velocityThreshold
    , distanceThreshold: config.distanceThreshold
    , maxDuration: unwrapMs config.maxDuration
    }
  where
  unwrapMs (Milliseconds ms) = ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // long press
-- ═════════════════════════════════════════════════════════════════════════════

-- | Long press gesture recognizer
foreign import data LongPressGesture :: Type

-- | Long press configuration
type LongPressConfig =
  { onLongPress :: Point -> Effect Unit
  , onStart :: Point -> Effect Unit    -- ^ Touch started (before threshold)
  , onCancel :: Effect Unit            -- ^ Touch moved too much or ended early
  , duration :: Milliseconds           -- ^ Hold duration to trigger
  , maxDistance :: Number              -- ^ Max movement allowed during press
  }

-- | Default long press configuration
defaultLongPressConfig :: LongPressConfig
defaultLongPressConfig =
  { onLongPress: \_ -> pure unit
  , onStart: \_ -> pure unit
  , onCancel: pure unit
  , duration: Milliseconds 500.0
  , maxDistance: 10.0
  }

foreign import createLongPressGestureImpl
  :: Element
  -> { onLongPress :: { x :: Number, y :: Number } -> Effect Unit
     , onStart :: { x :: Number, y :: Number } -> Effect Unit
     , onCancel :: Effect Unit
     , duration :: Number
     , maxDistance :: Number
     }
  -> Effect LongPressGesture

createLongPressGesture :: Element -> LongPressConfig -> Effect LongPressGesture
createLongPressGesture element config =
  createLongPressGestureImpl element
    { onLongPress: config.onLongPress
    , onStart: config.onStart
    , onCancel: config.onCancel
    , duration: unwrapMs config.duration
    , maxDistance: config.maxDistance
    }
  where
  unwrapMs (Milliseconds ms) = ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // double tap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Double tap gesture recognizer
foreign import data DoubleTapGesture :: Type

-- | Double tap configuration
type DoubleTapConfig =
  { onDoubleTap :: Point -> Effect Unit
  , onSingleTap :: Point -> Effect Unit   -- ^ Called if no second tap
  , maxDelay :: Milliseconds              -- ^ Max time between taps
  , maxDistance :: Number                 -- ^ Max distance between taps
  }

-- | Default double tap configuration
defaultDoubleTapConfig :: DoubleTapConfig
defaultDoubleTapConfig =
  { onDoubleTap: \_ -> pure unit
  , onSingleTap: \_ -> pure unit
  , maxDelay: Milliseconds 300.0
  , maxDistance: 40.0
  }

foreign import createDoubleTapGestureImpl
  :: Element
  -> { onDoubleTap :: { x :: Number, y :: Number } -> Effect Unit
     , onSingleTap :: { x :: Number, y :: Number } -> Effect Unit
     , maxDelay :: Number
     , maxDistance :: Number
     }
  -> Effect DoubleTapGesture

createDoubleTapGesture :: Element -> DoubleTapConfig -> Effect DoubleTapGesture
createDoubleTapGesture element config =
  createDoubleTapGestureImpl element
    { onDoubleTap: config.onDoubleTap
    , onSingleTap: config.onSingleTap
    , maxDelay: unwrapMs config.maxDelay
    , maxDistance: config.maxDistance
    }
  where
  unwrapMs (Milliseconds ms) = ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gesture composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic gesture recognizer (for composition)
foreign import data GestureRecognizer :: Type

-- | Compose multiple gestures to work together
-- | Handles conflicts between gestures (e.g., pan vs swipe)
foreign import composeGestures :: Array GestureRecognizer -> Effect Unit

-- | Enable a gesture recognizer
foreign import enableGesture :: GestureRecognizer -> Effect Unit

-- | Disable a gesture recognizer
foreign import disableGesture :: GestureRecognizer -> Effect Unit

-- | Destroy a gesture recognizer and clean up event listeners
foreign import destroyGesture :: GestureRecognizer -> Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // velocity tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity tracker for smooth gesture animations
type VelocityTracker =
  { points :: Ref (Array { point :: Point, time :: Number })
  , maxSamples :: Int
  }

-- | Create a velocity tracker
createVelocityTracker :: Int -> Effect VelocityTracker
createVelocityTracker maxSamples = do
  points <- Ref.new []
  pure { points, maxSamples }

-- | Track a point at current time
foreign import trackPointImpl
  :: Ref (Array { point :: Point, time :: Number })
  -> Int
  -> Point
  -> Effect Unit

trackPoint :: VelocityTracker -> Point -> Effect Unit
trackPoint tracker point =
  trackPointImpl tracker.points tracker.maxSamples point

-- | Calculate current velocity from tracked points
foreign import getVelocityImpl
  :: Ref (Array { point :: Point, time :: Number })
  -> Effect Velocity

getVelocity :: VelocityTracker -> Effect Velocity
getVelocity tracker = getVelocityImpl tracker.points

-- | Reset the velocity tracker
resetTracker :: VelocityTracker -> Effect Unit
resetTracker tracker = Ref.write [] tracker.points
