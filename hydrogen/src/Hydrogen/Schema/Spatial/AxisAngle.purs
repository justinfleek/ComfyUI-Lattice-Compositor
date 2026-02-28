-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // spatial // axis angle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AxisAngle - rotation representation as axis vector + angle.
-- |
-- | Alternative to quaternions and Euler angles.
-- | Intuitive representation: "rotate by θ degrees around axis v"
-- |
-- | ## Use Cases
-- | - Animating rotations (slerp)
-- | - Physics (angular velocity)
-- | - User interfaces (rotation handles)

module Hydrogen.Schema.Spatial.AxisAngle
  ( -- * Axis Angle
    AxisAngle
  , axisAngle
  , axisAngleAxis
  , axisAngleAngle
  , sameAxisAngle
  , showAxisAngle
  , isValidAxisAngle
  
  -- * Common Axes
  , rotateAroundX
  , rotateAroundY
  , rotateAroundZ
  
  -- * Operations
  , normalizeAxis
  , invertRotation
  , combineRotations
  , isLargerRotation
  
  -- * Conversions
  , toQuaternion
  , toDegrees
  , toRadians
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , max
  , min
  , negate
  , otherwise
  , (&&)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Number (floor) as Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // axis angle
-- ═════════════════════════════════════════════════════════════════════════════

-- | AxisAngle - rotation around an arbitrary axis.
-- | Axis should be unit length; angle in radians.
type AxisAngle =
  { axisX :: Number
  , axisY :: Number
  , axisZ :: Number
  , angle :: Number   -- Radians
  }

-- | Construct an axis-angle rotation.
-- | Axis is automatically normalized.
axisAngle :: Number -> Number -> Number -> Number -> AxisAngle
axisAngle ax ay az ang =
  let len = sqrt (ax * ax + ay * ay + az * az)
      safeLen = if len < 0.000001 then 1.0 else len
  in { axisX: ax / safeLen
     , axisY: ay / safeLen
     , axisZ: az / safeLen
     , angle: ang
     }

-- | Get rotation axis (unit vector).
axisAngleAxis :: AxisAngle -> { x :: Number, y :: Number, z :: Number }
axisAngleAxis aa = { x: aa.axisX, y: aa.axisY, z: aa.axisZ }

-- | Get rotation angle in radians.
axisAngleAngle :: AxisAngle -> Number
axisAngleAngle aa = aa.angle

-- | Check if two axis-angle rotations are equal (within tolerance).
sameAxisAngle :: AxisAngle -> AxisAngle -> Boolean
sameAxisAngle aa1 aa2 =
  let tolerance = 0.000001
      axisSame = absNum (aa1.axisX - aa2.axisX) < tolerance &&
                 absNum (aa1.axisY - aa2.axisY) < tolerance &&
                 absNum (aa1.axisZ - aa2.axisZ) < tolerance
      angleSame = absNum (aa1.angle - aa2.angle) < tolerance
  in axisSame && angleSame
  where
    absNum :: Number -> Number
    absNum n = if n < 0.0 then negate n else n

-- | Show axis-angle for debug output.
showAxisAngle :: AxisAngle -> String
showAxisAngle aa =
  "(AxisAngle axis=(" <> show aa.axisX <> ", " <> show aa.axisY <> ", " <> show aa.axisZ <>
  ") angle=" <> show aa.angle <> " rad)"

-- | Validate that axis is unit length (within tolerance).
isValidAxisAngle :: AxisAngle -> Boolean
isValidAxisAngle aa =
  let len = sqrt (aa.axisX * aa.axisX + aa.axisY * aa.axisY + aa.axisZ * aa.axisZ)
      tolerance = 0.0001
  in len >= (1.0 - tolerance) && len <= (1.0 + tolerance)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // common axes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create rotation around X axis.
rotateAroundX :: Number -> AxisAngle
rotateAroundX ang = { axisX: 1.0, axisY: 0.0, axisZ: 0.0, angle: ang }

-- | Create rotation around Y axis.
rotateAroundY :: Number -> AxisAngle
rotateAroundY ang = { axisX: 0.0, axisY: 1.0, axisZ: 0.0, angle: ang }

-- | Create rotation around Z axis.
rotateAroundZ :: Number -> AxisAngle
rotateAroundZ ang = { axisX: 0.0, axisY: 0.0, axisZ: 1.0, angle: ang }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalize the axis to unit length.
normalizeAxis :: AxisAngle -> AxisAngle
normalizeAxis aa =
  let len = sqrt (aa.axisX * aa.axisX + aa.axisY * aa.axisY + aa.axisZ * aa.axisZ)
      safeLen = if len < 0.000001 then 1.0 else len
  in { axisX: aa.axisX / safeLen
     , axisY: aa.axisY / safeLen
     , axisZ: aa.axisZ / safeLen
     , angle: aa.angle
     }

-- | Invert rotation (negate angle).
invertRotation :: AxisAngle -> AxisAngle
invertRotation aa = aa { angle = negate aa.angle }

-- | Combine two rotations (approximate via quaternion multiplication).
-- | For exact results, convert to quaternions, multiply, convert back.
combineRotations :: AxisAngle -> AxisAngle -> AxisAngle
combineRotations aa1 aa2 =
  let q1 = toQuaternion aa1
      q2 = toQuaternion aa2
      qr = multiplyQuaternions q1 q2
  in quaternionToAxisAngle qr

-- | Check if first rotation has a larger angle than second.
isLargerRotation :: AxisAngle -> AxisAngle -> Boolean
isLargerRotation aa1 aa2 =
  let absAngle1 = if aa1.angle < 0.0 then negate aa1.angle else aa1.angle
      absAngle2 = if aa2.angle < 0.0 then negate aa2.angle else aa2.angle
  in absAngle1 > absAngle2

-- | Multiply quaternions.
multiplyQuaternions :: { x :: Number, y :: Number, z :: Number, w :: Number }
                    -> { x :: Number, y :: Number, z :: Number, w :: Number }
                    -> { x :: Number, y :: Number, z :: Number, w :: Number }
multiplyQuaternions q1 q2 =
  { x: q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y
  , y: q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x
  , z: q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w
  , w: q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to quaternion.
toQuaternion :: AxisAngle -> { x :: Number, y :: Number, z :: Number, w :: Number }
toQuaternion aa =
  let halfAngle = aa.angle / 2.0
      s = sin halfAngle
      c = cos halfAngle
  in { x: aa.axisX * s
     , y: aa.axisY * s
     , z: aa.axisZ * s
     , w: c
     }

-- | Convert quaternion to axis-angle.
quaternionToAxisAngle :: { x :: Number, y :: Number, z :: Number, w :: Number } -> AxisAngle
quaternionToAxisAngle q =
  let angle = 2.0 * acos (clampUnit q.w)
      s = sqrt (1.0 - q.w * q.w)
      safeS = if s < 0.0001 then 1.0 else s
  in { axisX: q.x / safeS
     , axisY: q.y / safeS
     , axisZ: q.z / safeS
     , angle: angle
     }

-- | Clamp to [-1, 1] for acos.
clampUnit :: Number -> Number
clampUnit x = max (-1.0) (min 1.0 x)

-- | Convert angle from radians to degrees.
toDegrees :: AxisAngle -> AxisAngle
toDegrees aa = aa { angle = aa.angle * 180.0 / pi }

-- | Convert angle from degrees to radians.
toRadians :: AxisAngle -> AxisAngle
toRadians aa = aa { angle = aa.angle * pi / 180.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // math helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pi constant.
pi :: Number
pi = 3.141592653589793

-- | Square root (Newton's method).
sqrt :: Number -> Number
sqrt x
  | x <= 0.0 = 0.0
  | otherwise = sqrtNewton x (x / 2.0) 10

sqrtNewton :: Number -> Number -> Int -> Number
sqrtNewton _ guess 0 = guess
sqrtNewton x guess n = sqrtNewton x ((guess + x / guess) / 2.0) (n - 1)

-- | Sine approximation (Taylor series).
sin :: Number -> Number
sin x = 
  let x' = modFloat x (2.0 * pi)
      x2 = x' * x'
  in x' - (x' * x2 / 6.0) + (x' * x2 * x2 / 120.0) - (x' * x2 * x2 * x2 / 5040.0)

-- | Cosine approximation (Taylor series).
cos :: Number -> Number
cos x =
  let x' = modFloat x (2.0 * pi)
      x2 = x' * x'
  in 1.0 - (x2 / 2.0) + (x2 * x2 / 24.0) - (x2 * x2 * x2 / 720.0)

-- | Arc cosine approximation.
acos :: Number -> Number
acos x = pi / 2.0 - asin x

-- | Arc sine approximation (series).
asin :: Number -> Number
asin x =
  let x2 = x * x
  in x + (x * x2 / 6.0) + (3.0 * x * x2 * x2 / 40.0)

-- | Float modulo.
modFloat :: Number -> Number -> Number
modFloat x y = x - y * Number.floor (x / y)
