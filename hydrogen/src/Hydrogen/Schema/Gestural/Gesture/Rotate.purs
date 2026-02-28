-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // gestural // gesture // rotate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rotate - two-finger rotation gesture recognition.
-- |
-- | Models rotation gestures for rotating images, maps, and other content.
-- | Tracks rotation angle, center point, and gesture phase.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Gestural.Gesture.Phase
-- | - Hydrogen.Math.Core (atan2, pi)
-- |
-- | ## Dependents
-- | - Component.Image (rotate image)
-- | - Component.Map (map rotation)
-- | - Component.Canvas (viewport rotation)

module Hydrogen.Schema.Gestural.Gesture.Rotate
  ( -- * Rotate Config
    RotateConfig
  , rotateConfig
  , defaultRotateConfig
  , rotateSnapAngles
    -- * Rotate Gesture State
  , RotateGesture
  , rotateGesture
  , noRotateGesture
  , beginRotate
  , updateRotate
  , endRotate
  , cancelRotate
    -- * Accessors
  , rotateGestureAngle
  , rotateGestureAngleDegrees
  , rotateGestureDelta
  , rotateGestureCenter
  , rotateGestureVelocity
  , isRotateActive
  , isRotateEnded
    -- * Angle Utilities
  , normalizeAngle
  , radiansToDegrees
  , degreesToRadians
  , snapToAngle
  ) where

import Prelude

import Data.Array (foldl)
import Hydrogen.Schema.Gestural.Gesture.Phase (GesturePhase(Possible, Began, Changed, Ended, Cancelled))
import Hydrogen.Math.Core (atan2, pi, abs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // rotate config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for rotation gesture
type RotateConfig =
  { snapEnabled :: Boolean       -- ^ Snap to angles when near
  , snapAngles :: Array Number   -- ^ Snap angles in radians
  , snapThreshold :: Number      -- ^ Proximity to snap (radians)
  , velocityThreshold :: Number  -- ^ Minimum velocity to register (rad/s)
  }

-- | Create rotate config
rotateConfig :: Boolean -> Array Number -> Number -> Number -> RotateConfig
rotateConfig snapEnabled snapAngles snapThreshold velocityThreshold =
  { snapEnabled
  , snapAngles
  , snapThreshold
  , velocityThreshold
  }

-- | Default rotate config
-- |
-- | Snap enabled to 90-degree increments
defaultRotateConfig :: RotateConfig
defaultRotateConfig = rotateConfig 
  true 
  [0.0, pi / 2.0, pi, 3.0 * pi / 2.0, 2.0 * pi]  -- 0, 90, 180, 270, 360 degrees
  0.1  -- ~6 degrees snap threshold
  0.1  -- rad/s velocity threshold

-- | Get snap angles from config
rotateSnapAngles :: RotateConfig -> Array Number
rotateSnapAngles rc = rc.snapAngles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // rotate gesture state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete rotation gesture state
type RotateGesture =
  { phase :: GesturePhase        -- ^ Gesture lifecycle phase
  , angle :: Number              -- ^ Current rotation angle (radians)
  , initialAngle :: Number       -- ^ Angle when gesture began
  , fingerAngle :: Number        -- ^ Current angle between fingers
  , initialFingerAngle :: Number -- ^ Initial angle between fingers
  , delta :: Number              -- ^ Change since last update
  , centerX :: Number            -- ^ Center X between fingers
  , centerY :: Number            -- ^ Center Y between fingers
  , velocity :: Number           -- ^ Angular velocity (rad/s)
  , config :: RotateConfig       -- ^ Configuration
  }

-- | Create rotation gesture state
rotateGesture :: RotateConfig -> RotateGesture
rotateGesture config =
  { phase: Possible
  , angle: 0.0
  , initialAngle: 0.0
  , fingerAngle: 0.0
  , initialFingerAngle: 0.0
  , delta: 0.0
  , centerX: 0.0
  , centerY: 0.0
  , velocity: 0.0
  , config
  }

-- | No active rotation gesture
noRotateGesture :: RotateGesture
noRotateGesture = rotateGesture defaultRotateConfig

-- | Begin rotation gesture
beginRotate 
  :: Number -> Number  -- ^ Finger 1 position
  -> Number -> Number  -- ^ Finger 2 position
  -> Number            -- ^ Current content rotation
  -> RotateGesture 
  -> RotateGesture
beginRotate x1 y1 x2 y2 currentAngle rg =
  let
    dx = x2 - x1
    dy = y2 - y1
    fingerAngle = atan2 dy dx
    cx = (x1 + x2) / 2.0
    cy = (y1 + y2) / 2.0
  in rg
    { phase = Began
    , angle = currentAngle
    , initialAngle = currentAngle
    , fingerAngle = fingerAngle
    , initialFingerAngle = fingerAngle
    , delta = 0.0
    , centerX = cx
    , centerY = cy
    , velocity = 0.0
    }

-- | Update rotation gesture
updateRotate 
  :: Number -> Number  -- ^ Finger 1 position
  -> Number -> Number  -- ^ Finger 2 position
  -> Number            -- ^ Time delta (ms)
  -> RotateGesture 
  -> RotateGesture
updateRotate x1 y1 x2 y2 dt rg =
  let
    dx = x2 - x1
    dy = y2 - y1
    newFingerAngle = atan2 dy dx
    cx = (x1 + x2) / 2.0
    cy = (y1 + y2) / 2.0
    
    -- Calculate rotation delta
    angleDelta = normalizeAngle (newFingerAngle - rg.fingerAngle)
    newAngle = rg.angle + angleDelta
    
    -- Calculate velocity
    vel = if dt > 0.0 then (angleDelta / dt) * 1000.0 else 0.0
  in rg
    { phase = Changed
    , angle = newAngle
    , fingerAngle = newFingerAngle
    , delta = angleDelta
    , centerX = cx
    , centerY = cy
    , velocity = vel
    }

-- | End rotation gesture (with optional snap)
endRotate :: RotateGesture -> RotateGesture
endRotate rg =
  let
    finalAngle = if rg.config.snapEnabled
      then snapToAngle rg.config.snapAngles rg.config.snapThreshold rg.angle
      else rg.angle
  in rg 
    { phase = Ended
    , angle = finalAngle
    }

-- | Cancel rotation gesture
cancelRotate :: RotateGesture -> RotateGesture
cancelRotate rg = rg 
  { phase = Cancelled
  , angle = rg.initialAngle  -- Revert to initial angle
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current angle (radians)
rotateGestureAngle :: RotateGesture -> Number
rotateGestureAngle rg = rg.angle

-- | Get current angle (degrees)
rotateGestureAngleDegrees :: RotateGesture -> Number
rotateGestureAngleDegrees rg = radiansToDegrees rg.angle

-- | Get rotation delta since last update
rotateGestureDelta :: RotateGesture -> Number
rotateGestureDelta rg = rg.delta

-- | Get center point
rotateGestureCenter :: RotateGesture -> { x :: Number, y :: Number }
rotateGestureCenter rg = { x: rg.centerX, y: rg.centerY }

-- | Get angular velocity
rotateGestureVelocity :: RotateGesture -> Number
rotateGestureVelocity rg = rg.velocity

-- | Is rotation currently active?
isRotateActive :: RotateGesture -> Boolean
isRotateActive rg = rg.phase == Began || rg.phase == Changed

-- | Has rotation ended?
isRotateEnded :: RotateGesture -> Boolean
isRotateEnded rg = rg.phase == Ended || rg.phase == Cancelled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // angle utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalize angle to [-pi, pi]
normalizeAngle :: Number -> Number
normalizeAngle a
  | a > pi = normalizeAngle (a - 2.0 * pi)
  | a < (-pi) = normalizeAngle (a + 2.0 * pi)
  | otherwise = a

-- | Convert radians to degrees
radiansToDegrees :: Number -> Number
radiansToDegrees rad = rad * 180.0 / pi

-- | Convert degrees to radians
degreesToRadians :: Number -> Number
degreesToRadians deg = deg * pi / 180.0

-- | Snap angle to nearest snap point if within threshold
snapToAngle :: Array Number -> Number -> Number -> Number
snapToAngle snapAngles threshold angle =
  let
    normalized = normalizeAngle angle
    nearest = findNearest snapAngles normalized
  in case nearest of
    { found: true, value: v } ->
      if abs (normalized - v) <= threshold then v else normalized
    { found: false, value: _ } -> normalized
  where
  findNearest :: Array Number -> Number -> { found :: Boolean, value :: Number }
  findNearest angles target = foldl closer { found: false, value: 0.0 } angles
    where
    closer acc a =
      let dist = abs (normalizeAngle (a - target))
      in if not acc.found || dist < abs (normalizeAngle (acc.value - target))
        then { found: true, value: a }
        else acc
