-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // spatial // gimbal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gimbal — 3-axis rotation control for interactive 3D orientation.
-- |
-- | ## Design Philosophy
-- |
-- | A gimbal represents the rotational state of an object in 3D space,
-- | decomposed into three independent axes: pitch, yaw, and roll.
-- | This is the natural interface for human interaction with 3D rotation.
-- |
-- | ## Use Cases
-- |
-- | - **Bento box widgets**: Cards that tilt and rotate in 3D space
-- | - **Product viewers**: Rotating 3D models with constrained axes
-- | - **Camera controls**: Orbit, pan, tilt operations
-- | - **AR/VR widgets**: Floating UI elements with orientation
-- |
-- | ## Gimbal Lock
-- |
-- | Euler angles (and by extension, gimbals) suffer from gimbal lock when
-- | pitch approaches ±90°. For smooth animation, convert to Quaternion.
-- | The gimbal is for **input and display**, quaternions are for **computation**.
-- |
-- | ## Axis Convention
-- |
-- | Following aerospace/game convention:
-- | - **Pitch** (X-axis): Nose up/down rotation
-- | - **Yaw** (Y-axis): Nose left/right rotation  
-- | - **Roll** (Z-axis): Barrel roll, clockwise/counter-clockwise
-- |
-- | All angles are in degrees, range [-180, 180) with wrapping.

module Hydrogen.Schema.Spatial.Gimbal
  ( -- * Core Type
    Gimbal(Gimbal)
  , gimbal
  , gimbalZero
  
  -- * Accessors
  , gimbalPitch
  , gimbalYaw
  , gimbalRoll
  
  -- * Setters
  , setPitch
  , setYaw
  , setRoll
  
  -- * Operations
  , rotatePitch
  , rotateYaw
  , rotateRoll
  , rotateGimbal
  , invertGimbal
  , lerpGimbal
  
  -- * Constraints
  , clampPitch
  , constrainGimbal
  , GimbalConstraints
  , defaultConstraints
  , noConstraints
  
  -- * Conversion
  , toEuler
  , fromEuler
  , toQuaternion
  , fromQuaternion
  
  -- * Debug
  , showGimbal
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , (<)
  , (>=)
  , (<=)
  , (&&)
  )

import Hydrogen.Schema.Dimension.Rotation.Euler
  ( Euler(Euler)
  , RotationOrder(XYZ)
  )

-- Use Geometry.Quaternion which has fromEuler/toEuler with Degrees
import Hydrogen.Schema.Geometry.Quaternion as Quat
import Hydrogen.Schema.Geometry.Quaternion (Quaternion)
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, unwrapDegrees)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // core type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A gimbal represents 3-axis rotation decomposed into pitch, yaw, and roll.
-- |
-- | All angles are in degrees, normalized to [-180, 180).
-- |
-- | ## Show Instance
-- |
-- | Follows SHOW_DEBUG_CONVENTION: parseable, unambiguous output.
-- |
-- | ```purescript
-- | show (gimbal 45.0 90.0 0.0)
-- | -- "(Gimbal pitch:45.0 yaw:90.0 roll:0.0)"
-- | ```
newtype Gimbal = Gimbal
  { pitch :: Number  -- ^ X-axis rotation (nose up/down), degrees
  , yaw :: Number    -- ^ Y-axis rotation (nose left/right), degrees
  , roll :: Number   -- ^ Z-axis rotation (barrel roll), degrees
  }

derive instance eqGimbal :: Eq Gimbal

instance showGimbalInstance :: Show Gimbal where
  show (Gimbal g) = 
    "(Gimbal pitch:" <> show g.pitch 
    <> " yaw:" <> show g.yaw 
    <> " roll:" <> show g.roll <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a gimbal from pitch, yaw, roll angles (degrees).
-- |
-- | Angles are normalized to [-180, 180).
gimbal :: Number -> Number -> Number -> Gimbal
gimbal pitch yaw roll = Gimbal
  { pitch: normalizeAngle pitch
  , yaw: normalizeAngle yaw
  , roll: normalizeAngle roll
  }

-- | Zero rotation gimbal (identity).
gimbalZero :: Gimbal
gimbalZero = Gimbal { pitch: 0.0, yaw: 0.0, roll: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get pitch angle (X-axis rotation).
gimbalPitch :: Gimbal -> Number
gimbalPitch (Gimbal g) = g.pitch

-- | Get yaw angle (Y-axis rotation).
gimbalYaw :: Gimbal -> Number
gimbalYaw (Gimbal g) = g.yaw

-- | Get roll angle (Z-axis rotation).
gimbalRoll :: Gimbal -> Number
gimbalRoll (Gimbal g) = g.roll

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set pitch angle, preserving yaw and roll.
setPitch :: Number -> Gimbal -> Gimbal
setPitch p (Gimbal g) = Gimbal { pitch: normalizeAngle p, yaw: g.yaw, roll: g.roll }

-- | Set yaw angle, preserving pitch and roll.
setYaw :: Number -> Gimbal -> Gimbal
setYaw y (Gimbal g) = Gimbal { pitch: g.pitch, yaw: normalizeAngle y, roll: g.roll }

-- | Set roll angle, preserving pitch and yaw.
setRoll :: Number -> Gimbal -> Gimbal
setRoll r (Gimbal g) = Gimbal { pitch: g.pitch, yaw: g.yaw, roll: normalizeAngle r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate pitch by delta degrees.
rotatePitch :: Number -> Gimbal -> Gimbal
rotatePitch delta (Gimbal g) = 
  Gimbal { pitch: normalizeAngle (g.pitch + delta), yaw: g.yaw, roll: g.roll }

-- | Rotate yaw by delta degrees.
rotateYaw :: Number -> Gimbal -> Gimbal
rotateYaw delta (Gimbal g) = 
  Gimbal { pitch: g.pitch, yaw: normalizeAngle (g.yaw + delta), roll: g.roll }

-- | Rotate roll by delta degrees.
rotateRoll :: Number -> Gimbal -> Gimbal
rotateRoll delta (Gimbal g) = 
  Gimbal { pitch: g.pitch, yaw: g.yaw, roll: normalizeAngle (g.roll + delta) }

-- | Rotate all axes by delta values.
rotateGimbal :: Number -> Number -> Number -> Gimbal -> Gimbal
rotateGimbal dp dy dr (Gimbal g) = Gimbal
  { pitch: normalizeAngle (g.pitch + dp)
  , yaw: normalizeAngle (g.yaw + dy)
  , roll: normalizeAngle (g.roll + dr)
  }

-- | Invert the gimbal (negate all angles).
invertGimbal :: Gimbal -> Gimbal
invertGimbal (Gimbal g) = Gimbal
  { pitch: normalizeAngle (negate g.pitch)
  , yaw: normalizeAngle (negate g.yaw)
  , roll: normalizeAngle (negate g.roll)
  }

-- | Linear interpolation between two gimbals.
-- |
-- | For smooth animation, consider converting to quaternion and using slerp,
-- | then converting back. This avoids gimbal lock issues during interpolation.
lerpGimbal :: Number -> Gimbal -> Gimbal -> Gimbal
lerpGimbal t (Gimbal a) (Gimbal b) = Gimbal
  { pitch: lerpAngle t a.pitch b.pitch
  , yaw: lerpAngle t a.yaw b.yaw
  , roll: lerpAngle t a.roll b.roll
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Constraints for gimbal axes.
-- |
-- | Each axis has optional min/max bounds. `Nothing` means unconstrained.
type GimbalConstraints =
  { pitchMin :: Number
  , pitchMax :: Number
  , yawMin :: Number
  , yawMax :: Number
  , rollMin :: Number
  , rollMax :: Number
  }

-- | Default constraints: pitch limited to ±85° (avoid gimbal lock), others free.
defaultConstraints :: GimbalConstraints
defaultConstraints =
  { pitchMin: -85.0
  , pitchMax: 85.0
  , yawMin: -180.0
  , yawMax: 180.0
  , rollMin: -180.0
  , rollMax: 180.0
  }

-- | No constraints (full range on all axes).
noConstraints :: GimbalConstraints
noConstraints =
  { pitchMin: -180.0
  , pitchMax: 180.0
  , yawMin: -180.0
  , yawMax: 180.0
  , rollMin: -180.0
  , rollMax: 180.0
  }

-- | Clamp pitch to avoid gimbal lock (typically ±85° or ±89°).
clampPitch :: Number -> Number -> Gimbal -> Gimbal
clampPitch minP maxP (Gimbal g) = Gimbal
  { pitch: clampNumber minP maxP g.pitch
  , yaw: g.yaw
  , roll: g.roll
  }

-- | Apply constraints to a gimbal.
constrainGimbal :: GimbalConstraints -> Gimbal -> Gimbal
constrainGimbal c (Gimbal g) = Gimbal
  { pitch: clampNumber c.pitchMin c.pitchMax g.pitch
  , yaw: clampNumber c.yawMin c.yawMax g.yaw
  , roll: clampNumber c.rollMin c.rollMax g.roll
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert gimbal to Euler angles (XYZ order).
toEuler :: Gimbal -> Euler
toEuler (Gimbal g) = Euler g.pitch g.yaw g.roll XYZ

-- | Create gimbal from Euler angles (ignores rotation order, uses XYZ).
fromEuler :: Euler -> Gimbal
fromEuler (Euler x y z _) = gimbal x y z

-- | Convert gimbal to quaternion for smooth interpolation.
toQuaternion :: Gimbal -> Quaternion
toQuaternion g = Quat.fromEuler 
  (degrees (gimbalPitch g)) 
  (degrees (gimbalYaw g)) 
  (degrees (gimbalRoll g))

-- | Create gimbal from quaternion.
fromQuaternion :: Quaternion -> Gimbal
fromQuaternion q =
  let euler = Quat.toEuler q
  in gimbal (unwrapDegrees euler.x) (unwrapDegrees euler.y) (unwrapDegrees euler.z)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // debug
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debug string representation (same as Show but explicit function).
showGimbal :: Gimbal -> String
showGimbal (Gimbal g) = 
  "(Gimbal pitch:" <> show g.pitch 
  <> " yaw:" <> show g.yaw 
  <> " roll:" <> show g.roll <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalize angle to [-180, 180) range.
normalizeAngle :: Number -> Number
normalizeAngle a =
  let wrapped = a - 360.0 * floor ((a + 180.0) / 360.0)
  in if wrapped >= 180.0 then wrapped - 360.0 else wrapped

-- | Linear interpolation for angles (handles wraparound).
lerpAngle :: Number -> Number -> Number -> Number
lerpAngle t a b =
  let diff = b - a
      -- Shortest path around the circle
      shortDiff = if diff > 180.0 then diff - 360.0
                  else if diff < -180.0 then diff + 360.0
                  else diff
  in normalizeAngle (a + t * shortDiff)

-- | Clamp a value to [minVal, maxVal].
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber minVal maxVal x
  | x < minVal = minVal
  | x > maxVal = maxVal
  | x >= minVal && x <= maxVal = x
  | x < minVal = minVal  -- Fallback for NaN protection
  | x > maxVal = maxVal
  | true = x  -- Total coverage

-- | Floor function for angle normalization.
floor :: Number -> Number
floor x = 
  let truncated = x - (x - (x / 1.0))  -- Integer part
  in if truncated > x then truncated - 1.0 else truncated
