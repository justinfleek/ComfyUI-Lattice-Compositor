-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // gestural // motion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Motion - velocity, acceleration, and momentum atoms for gestures.
-- |
-- | Models motion physics for gesture recognition and inertial scrolling.
-- | Essential for Frame.io-level smooth gesture handling.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Math.Core (sqrt, abs)
-- |
-- | ## Dependents
-- | - Gestural.Gesture (uses Velocity for swipe detection)
-- | - Gestural.Touch (uses Motion for pinch/pan)
-- | - Interaction.InfiniteScroll (uses momentum)

module Hydrogen.Schema.Gestural.Motion
  ( -- * Velocity
    Velocity2D
  , velocity2D
  , zeroVelocity
  , velocityX
  , velocityY
  , velocityMagnitude
  , velocityAngle
  , isMoving
  , isFastMotion
    -- * Acceleration
  , Acceleration2D
  , acceleration2D
  , zeroAcceleration
  , accelerationX
  , accelerationY
  , accelerationMagnitude
  , isDecelerating
    -- * Distance
  , Distance
  , distance
  , distanceBetween
  , unwrapDistance
  , isSignificantDistance
    -- * Direction
  , Direction
      ( DirectionUp
      , DirectionDown
      , DirectionLeft
      , DirectionRight
      , DirectionUpLeft
      , DirectionUpRight
      , DirectionDownLeft
      , DirectionDownRight
      , DirectionNone
      )
  , directionFromAngle
  , directionFromDelta
  , isHorizontal
  , isVertical
  , oppositeDirection
    -- * Gesture Vector (Molecule)
  , GestureVector
  , gestureVector
  , gestureFromPoints
  , vectorDistance
  , vectorDirection
  , vectorVelocity
    -- * Momentum (Molecule)
  , Momentum
  , momentum
  , applyFriction
  , momentumVelocity
  , momentumPosition
  , isMomentumActive
    -- * Motion State (Compound)
  , MotionState
  , motionState
  , idleMotion
  , activeMotion
  , updateMotion
  , stopMotion
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core (sqrt, atan2, cos, sin, abs, pi)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // velocity
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D velocity in pixels per second
-- |
-- | Used for gesture recognition:
-- | - Swipe: requires velocity above threshold
-- | - Fling: uses velocity for momentum
-- | - Pan: tracks current motion speed
type Velocity2D =
  { vx :: Number    -- ^ Horizontal velocity (px/s)
  , vy :: Number    -- ^ Vertical velocity (px/s)
  }

-- | Create velocity vector
velocity2D :: Number -> Number -> Velocity2D
velocity2D vx vy = { vx, vy }

-- | Zero velocity (stationary)
zeroVelocity :: Velocity2D
zeroVelocity = velocity2D 0.0 0.0

-- | Get horizontal velocity
velocityX :: Velocity2D -> Number
velocityX v = v.vx

-- | Get vertical velocity
velocityY :: Velocity2D -> Number
velocityY v = v.vy

-- | Calculate velocity magnitude (speed)
velocityMagnitude :: Velocity2D -> Number
velocityMagnitude v = sqrt (v.vx * v.vx + v.vy * v.vy)

-- | Calculate velocity angle in radians (-π to π)
velocityAngle :: Velocity2D -> Number
velocityAngle v = atan2 v.vy v.vx

-- | Is there any motion?
isMoving :: Velocity2D -> Boolean
isMoving v = velocityMagnitude v > 1.0

-- | Is motion fast? (> 500 px/s, typical swipe threshold)
isFastMotion :: Velocity2D -> Boolean
isFastMotion v = velocityMagnitude v > 500.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // acceleration
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D acceleration in pixels per second squared
-- |
-- | Used for:
-- | - Detecting gesture intent (speeding up vs slowing down)
-- | - Inertial scrolling deceleration
type Acceleration2D =
  { ax :: Number    -- ^ Horizontal acceleration (px/s²)
  , ay :: Number    -- ^ Vertical acceleration (px/s²)
  }

-- | Create acceleration vector
acceleration2D :: Number -> Number -> Acceleration2D
acceleration2D ax ay = { ax, ay }

-- | Zero acceleration
zeroAcceleration :: Acceleration2D
zeroAcceleration = acceleration2D 0.0 0.0

-- | Get horizontal acceleration
accelerationX :: Acceleration2D -> Number
accelerationX a = a.ax

-- | Get vertical acceleration
accelerationY :: Acceleration2D -> Number
accelerationY a = a.ay

-- | Calculate acceleration magnitude
accelerationMagnitude :: Acceleration2D -> Number
accelerationMagnitude a = sqrt (a.ax * a.ax + a.ay * a.ay)

-- | Is the motion decelerating? (slowing down)
isDecelerating :: Velocity2D -> Acceleration2D -> Boolean
isDecelerating v a = 
  (v.vx * a.ax < 0.0) || (v.vy * a.ay < 0.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance in pixels (always non-negative)
newtype Distance = Distance Number

derive instance eqDistance :: Eq Distance
derive instance ordDistance :: Ord Distance

instance showDistance :: Show Distance where
  show (Distance d) = show d <> "px"

-- | Create distance (takes absolute value)
distance :: Number -> Distance
distance d = Distance (abs d)

-- | Calculate distance between two points
distanceBetween :: Number -> Number -> Number -> Number -> Distance
distanceBetween x1 y1 x2 y2 =
  let dx = x2 - x1
      dy = y2 - y1
  in Distance (sqrt (dx * dx + dy * dy))

-- | Extract raw distance value
unwrapDistance :: Distance -> Number
unwrapDistance (Distance d) = d

-- | Is distance significant? (> 10px, avoids accidental taps)
isSignificantDistance :: Distance -> Boolean
isSignificantDistance (Distance d) = d > 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cardinal and intermediate directions
data Direction
  = DirectionUp
  | DirectionDown
  | DirectionLeft
  | DirectionRight
  | DirectionUpLeft
  | DirectionUpRight
  | DirectionDownLeft
  | DirectionDownRight
  | DirectionNone

derive instance eqDirection :: Eq Direction
derive instance ordDirection :: Ord Direction

instance showDirection :: Show Direction where
  show DirectionUp = "up"
  show DirectionDown = "down"
  show DirectionLeft = "left"
  show DirectionRight = "right"
  show DirectionUpLeft = "up-left"
  show DirectionUpRight = "up-right"
  show DirectionDownLeft = "down-left"
  show DirectionDownRight = "down-right"
  show DirectionNone = "none"

-- | Determine direction from angle in radians
-- | Angle 0 = right, π/2 = down, π = left, -π/2 = up
directionFromAngle :: Number -> Direction
directionFromAngle angle
  | angle > -pi / 8.0 && angle <= pi / 8.0 = DirectionRight
  | angle > pi / 8.0 && angle <= 3.0 * pi / 8.0 = DirectionDownRight
  | angle > 3.0 * pi / 8.0 && angle <= 5.0 * pi / 8.0 = DirectionDown
  | angle > 5.0 * pi / 8.0 && angle <= 7.0 * pi / 8.0 = DirectionDownLeft
  | angle > 7.0 * pi / 8.0 || angle <= -7.0 * pi / 8.0 = DirectionLeft
  | angle > -7.0 * pi / 8.0 && angle <= -5.0 * pi / 8.0 = DirectionUpLeft
  | angle > -5.0 * pi / 8.0 && angle <= -3.0 * pi / 8.0 = DirectionUp
  | otherwise = DirectionUpRight

-- | Determine direction from delta values
directionFromDelta :: Number -> Number -> Direction
directionFromDelta dx dy
  | abs dx < 1.0 && abs dy < 1.0 = DirectionNone
  | otherwise = directionFromAngle (atan2 dy dx)

-- | Is direction horizontal?
isHorizontal :: Direction -> Boolean
isHorizontal DirectionLeft = true
isHorizontal DirectionRight = true
isHorizontal _ = false

-- | Is direction vertical?
isVertical :: Direction -> Boolean
isVertical DirectionUp = true
isVertical DirectionDown = true
isVertical _ = false

-- | Get opposite direction
oppositeDirection :: Direction -> Direction
oppositeDirection DirectionUp = DirectionDown
oppositeDirection DirectionDown = DirectionUp
oppositeDirection DirectionLeft = DirectionRight
oppositeDirection DirectionRight = DirectionLeft
oppositeDirection DirectionUpLeft = DirectionDownRight
oppositeDirection DirectionUpRight = DirectionDownLeft
oppositeDirection DirectionDownLeft = DirectionUpRight
oppositeDirection DirectionDownRight = DirectionUpLeft
oppositeDirection DirectionNone = DirectionNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // gesture vector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete gesture motion from start to current position
-- |
-- | Combines distance, direction, and velocity into a single
-- | coherent representation of a gesture's motion characteristics.
type GestureVector =
  { startX :: Number       -- ^ Starting X position
  , startY :: Number       -- ^ Starting Y position
  , currentX :: Number     -- ^ Current X position
  , currentY :: Number     -- ^ Current Y position
  , velocity :: Velocity2D -- ^ Current velocity
  , duration :: Number     -- ^ Duration in milliseconds
  }

-- | Create gesture vector
gestureVector 
  :: Number -> Number 
  -> Number -> Number 
  -> Velocity2D 
  -> Number 
  -> GestureVector
gestureVector sx sy cx cy vel dur =
  { startX: sx
  , startY: sy
  , currentX: cx
  , currentY: cy
  , velocity: vel
  , duration: max 0.0 dur
  }

-- | Create gesture vector from two points and time delta
gestureFromPoints 
  :: Number -> Number 
  -> Number -> Number 
  -> Number 
  -> GestureVector
gestureFromPoints sx sy cx cy dt =
  let dx = cx - sx
      dy = cy - sy
      dtSec = dt / 1000.0
      vx = if dtSec > 0.0 then dx / dtSec else 0.0
      vy = if dtSec > 0.0 then dy / dtSec else 0.0
  in gestureVector sx sy cx cy (velocity2D vx vy) dt

-- | Get total distance traveled
vectorDistance :: GestureVector -> Distance
vectorDistance gv = distanceBetween gv.startX gv.startY gv.currentX gv.currentY

-- | Get gesture direction
vectorDirection :: GestureVector -> Direction
vectorDirection gv = directionFromDelta (gv.currentX - gv.startX) (gv.currentY - gv.startY)

-- | Get gesture velocity
vectorVelocity :: GestureVector -> Velocity2D
vectorVelocity gv = gv.velocity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // momentum
-- ═════════════════════════════════════════════════════════════════════════════

-- | Momentum state for inertial scrolling and fling gestures
-- |
-- | Models physics-based motion with friction deceleration.
type Momentum =
  { velocity :: Velocity2D   -- ^ Current velocity
  , friction :: Number       -- ^ Friction coefficient (0-1, higher = more friction)
  , x :: Number              -- ^ Current X position
  , y :: Number              -- ^ Current Y position
  , active :: Boolean        -- ^ Is momentum animation active
  }

-- | Create momentum state
momentum :: Number -> Number -> Velocity2D -> Number -> Momentum
momentum x y vel friction =
  { velocity: vel
  , friction: max 0.0 (min 1.0 friction)
  , x
  , y
  , active: isMoving vel
  }

-- | Apply friction to momentum (call each frame)
-- | Returns updated momentum with reduced velocity
applyFriction :: Number -> Momentum -> Momentum
applyFriction dtMs m =
  let dtSec = dtMs / 1000.0
      decay = 1.0 - m.friction
      newVx = m.velocity.vx * decay
      newVy = m.velocity.vy * decay
      newX = m.x + m.velocity.vx * dtSec
      newY = m.y + m.velocity.vy * dtSec
      newVel = velocity2D newVx newVy
  in m 
    { velocity = newVel
    , x = newX
    , y = newY
    , active = velocityMagnitude newVel > 0.5
    }

-- | Get current velocity
momentumVelocity :: Momentum -> Velocity2D
momentumVelocity m = m.velocity

-- | Get current position
momentumPosition :: Momentum -> { x :: Number, y :: Number }
momentumPosition m = { x: m.x, y: m.y }

-- | Is momentum animation still active?
isMomentumActive :: Momentum -> Boolean
isMomentumActive m = m.active

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // motion state (compound)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete motion state for tracking gesture physics
type MotionState =
  { position :: { x :: Number, y :: Number }
  , velocity :: Velocity2D
  , acceleration :: Acceleration2D
  , direction :: Direction
  , isActive :: Boolean
  , startTime :: Maybe Number
  , lastUpdateTime :: Maybe Number
  }

-- | Create motion state
motionState :: Number -> Number -> MotionState
motionState x y =
  { position: { x, y }
  , velocity: zeroVelocity
  , acceleration: zeroAcceleration
  , direction: DirectionNone
  , isActive: false
  , startTime: Nothing
  , lastUpdateTime: Nothing
  }

-- | Idle motion state at origin
idleMotion :: MotionState
idleMotion = motionState 0.0 0.0

-- | Create active motion state
activeMotion :: Number -> Number -> Number -> MotionState
activeMotion x y timestamp =
  (motionState x y)
    { isActive = true
    , startTime = Just timestamp
    , lastUpdateTime = Just timestamp
    }

-- | Update motion state with new position
updateMotion :: Number -> Number -> Number -> MotionState -> MotionState
updateMotion newX newY timestamp ms = case ms.lastUpdateTime of
  Nothing -> ms
    { position = { x: newX, y: newY }
    , lastUpdateTime = Just timestamp
    }
  Just lastTime ->
    let dt = timestamp - lastTime
        dtSec = dt / 1000.0
        dx = newX - ms.position.x
        dy = newY - ms.position.y
        newVx = if dtSec > 0.0 then dx / dtSec else 0.0
        newVy = if dtSec > 0.0 then dy / dtSec else 0.0
        newVel = velocity2D newVx newVy
        ax = if dtSec > 0.0 then (newVx - ms.velocity.vx) / dtSec else 0.0
        ay = if dtSec > 0.0 then (newVy - ms.velocity.vy) / dtSec else 0.0
    in ms
      { position = { x: newX, y: newY }
      , velocity = newVel
      , acceleration = acceleration2D ax ay
      , direction = directionFromDelta dx dy
      , lastUpdateTime = Just timestamp
      }

-- | Stop motion, preserving final position
stopMotion :: MotionState -> MotionState
stopMotion ms = ms
  { velocity = zeroVelocity
  , acceleration = zeroAcceleration
  , direction = DirectionNone
  , isActive = false
  }
