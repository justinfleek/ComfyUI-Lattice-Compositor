-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // geometry // quaternion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Quaternion — 4D hypercomplex numbers for 3D rotation.

module Hydrogen.Schema.Geometry.Quaternion
  ( -- * Type
    Quaternion(Quaternion)
  
  -- * Constructors
  , quaternion
  , identity
  , fromAxisAngle
  , fromEuler
  
  -- * Accessors
  , getX
  , getY
  , getZ
  , getW
  
  -- * Length / Norm
  , lengthSq
  , length
  , normalize
  
  -- * Algebraic Operations
  , conjugate
  , invert
  , multiply
  
  -- * Euler Conversion
  , toEuler
  
  -- * Interpolation
  , dot
  , slerp
  
  -- * Vector Rotation
  , rotateVector
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<)
  , (>)
  , (>=)
  , (<>)
  )

import Data.Number (sqrt, sin, cos, asin, acos, atan2, abs, pi)

import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, unwrapDegrees)
import Hydrogen.Schema.Geometry.Vector (Vector3D(Vector3D), vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quaternion for 3D rotation representation.
-- |
-- | Components: x, y, z (imaginary), w (real/scalar)
-- | Convention follows Three.js: (x, y, z, w) order
data Quaternion = Quaternion Number Number Number Number

derive instance eqQuaternion :: Eq Quaternion

instance showQuaternion :: Show Quaternion where
  show (Quaternion x y z w) = 
    "(Quaternion " <> show x <> " " <> show y <> " " <> show z <> " " <> show w <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create quaternion from components
quaternion :: Number -> Number -> Number -> Number -> Quaternion
quaternion = Quaternion

-- | Identity quaternion (no rotation)
identity :: Quaternion
identity = Quaternion 0.0 0.0 0.0 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get X component (imaginary i)
getX :: Quaternion -> Number
getX (Quaternion x _ _ _) = x

-- | Get Y component (imaginary j)
getY :: Quaternion -> Number
getY (Quaternion _ y _ _) = y

-- | Get Z component (imaginary k)
getZ :: Quaternion -> Number
getZ (Quaternion _ _ z _) = z

-- | Get W component (real/scalar)
getW :: Quaternion -> Number
getW (Quaternion _ _ _ w) = w

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // length / norm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Squared length of quaternion
lengthSq :: Quaternion -> Number
lengthSq (Quaternion x y z w) = x*x + y*y + z*z + w*w

-- | Length (magnitude) of quaternion
length :: Quaternion -> Number
length q = sqrt (lengthSq q)

-- | Normalize to unit quaternion
-- | Returns identity if length is zero
normalize :: Quaternion -> Quaternion
normalize q =
  let len = length q
  in if len == 0.0
       then identity
       else let invLen = 1.0 / len
            in Quaternion 
                 (getX q * invLen) 
                 (getY q * invLen) 
                 (getZ q * invLen) 
                 (getW q * invLen)

-- | Conjugate: negate imaginary components
conjugate :: Quaternion -> Quaternion
conjugate (Quaternion x y z w) = Quaternion (negate x) (negate y) (negate z) w

-- | Multiplicative inverse
-- | Returns identity if length is zero
invert :: Quaternion -> Quaternion
invert q =
  let lenSq = lengthSq q
  in if lenSq == 0.0
       then identity
       else let invLenSq = 1.0 / lenSq
            in Quaternion 
                 (negate (getX q) * invLenSq) 
                 (negate (getY q) * invLenSq) 
                 (negate (getZ q) * invLenSq) 
                 (getW q * invLenSq)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // multiplication
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hamilton product: compose two rotations
-- | multiply a b means "apply b, then apply a"
multiply :: Quaternion -> Quaternion -> Quaternion
multiply (Quaternion ax ay az aw) (Quaternion bx by bz bw) =
  Quaternion
    (aw*bx + ax*bw + ay*bz - az*by)
    (aw*by - ax*bz + ay*bw + az*bx)
    (aw*bz + ax*by - ay*bx + az*bw)
    (aw*bw - ax*bx - ay*by - az*bz)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // from angles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create quaternion from axis and angle (radians)
-- | Axis should be normalized; if zero, returns identity
fromAxisAngle :: Number -> Number -> Number -> Number -> Quaternion
fromAxisAngle axisX axisY axisZ angle =
  let halfAngle = angle / 2.0
      s = sin halfAngle
      c = cos halfAngle
  in Quaternion (axisX * s) (axisY * s) (axisZ * s) c

-- | Create quaternion from Euler angles (degrees).
-- |
-- | Rotation order: X (pitch) → Y (yaw) → Z (roll)
-- | This matches the intrinsic Tait-Bryan convention used in Transform3D.
fromEuler :: Degrees -> Degrees -> Degrees -> Quaternion
fromEuler xDeg yDeg zDeg =
  let
    -- Convert to radians and halve
    hx = unwrapDegrees xDeg * pi / 360.0
    hy = unwrapDegrees yDeg * pi / 360.0
    hz = unwrapDegrees zDeg * pi / 360.0
    
    -- Precompute sin/cos of half angles
    cx = cos hx
    sx = sin hx
    cy = cos hy
    sy = sin hy
    cz = cos hz
    sz = sin hz
  in
    -- Compose rotations: qz * qy * qx
    Quaternion
      (sx * cy * cz - cx * sy * sz)
      (cx * sy * cz + sx * cy * sz)
      (cx * cy * sz - sx * sy * cz)
      (cx * cy * cz + sx * sy * sz)

-- | Extract Euler angles from quaternion (degrees).
-- |
-- | Returns { x, y, z } representing pitch, yaw, roll.
-- | Handles gimbal lock at ±90° pitch gracefully.
toEuler :: Quaternion -> { x :: Degrees, y :: Degrees, z :: Degrees }
toEuler (Quaternion qx qy qz qw) =
  let
    -- Precompute common terms
    sinp = 2.0 * (qw * qy - qz * qx)
    
    -- Check for gimbal lock (pitch at ±90°)
    pitch = 
      if abs sinp >= 1.0
        then if sinp > 0.0 then 90.0 else (-90.0)
        else asinSafe sinp * 180.0 / pi
    
    -- Yaw (Y rotation)
    yaw =
      if abs sinp >= 1.0
        -- Gimbal lock: yaw is undefined, set to 0
        then 0.0
        else atan2 (2.0 * (qw * qz + qx * qy)) (1.0 - 2.0 * (qy * qy + qz * qz)) * 180.0 / pi
    
    -- Roll (Z rotation)  
    roll =
      if abs sinp >= 1.0
        -- Gimbal lock: combine with pitch
        then atan2 (2.0 * (qw * qx + qy * qz)) (1.0 - 2.0 * (qx * qx + qy * qy)) * 180.0 / pi
        else atan2 (2.0 * (qw * qx + qy * qz)) (1.0 - 2.0 * (qx * qx + qy * qy)) * 180.0 / pi
  in
    { x: degrees pitch, y: degrees yaw, z: degrees roll }

-- | Safe asin that clamps input to [-1, 1]
asinSafe :: Number -> Number
asinSafe n
  | n < (-1.0) = asin (-1.0)
  | n > 1.0 = asin 1.0
  | true = asin n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dot product of two quaternions
dot :: Quaternion -> Quaternion -> Number
dot (Quaternion ax ay az aw) (Quaternion bx by bz bw) =
  ax*bx + ay*by + az*bz + aw*bw

-- | Spherical linear interpolation
-- | t=0 returns a, t=1 returns b
slerp :: Number -> Quaternion -> Quaternion -> Quaternion
slerp t qa qb =
  let d = dot qa qb
      -- Handle negative dot (opposite hemispheres)
      d' = abs d
      qb' = if d < 0.0 
              then Quaternion (negate (getX qb)) (negate (getY qb)) (negate (getZ qb)) (negate (getW qb))
              else qb
  in if d' > 0.9995
       -- Very close: use linear interpolation
       then normalize (Quaternion
              (getX qa + t * (getX qb' - getX qa))
              (getY qa + t * (getY qb' - getY qa))
              (getZ qa + t * (getZ qb' - getZ qa))
              (getW qa + t * (getW qb' - getW qa)))
       -- Standard slerp
       else let theta = acos d'
                sinTheta = sin theta
                wa = sin ((1.0 - t) * theta) / sinTheta
                wb = sin (t * theta) / sinTheta
             in Quaternion
                 (wa * getX qa + wb * getX qb')
                 (wa * getY qa + wb * getY qb')
                 (wa * getZ qa + wb * getZ qb')
                 (wa * getW qa + wb * getW qb')

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // vector rotation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate a 3D vector by a quaternion.
-- |
-- | Uses the formula: v' = q * v * q⁻¹
-- | where v is treated as a quaternion with w=0.
-- | Quaternion should be normalized for correct rotation.
rotateVector :: Quaternion -> Vector3D -> Vector3D
rotateVector q (Vector3D v) =
  let
    -- Normalize quaternion to ensure proper rotation
    (Quaternion qx qy qz qw) = normalize q
    
    -- Vector as quaternion (w = 0)
    vx = v.x
    vy = v.y
    vz = v.z
    
    -- Compute q * v (Hamilton product where v.w = 0)
    -- t = q * v
    tx = qw * vx + qy * vz - qz * vy
    ty = qw * vy + qz * vx - qx * vz
    tz = qw * vz + qx * vy - qy * vx
    tw = negate (qx * vx) - qy * vy - qz * vz
    
    -- Compute t * q⁻¹ (conjugate since q is unit)
    -- For unit quaternion: q⁻¹ = conjugate(q) = (-qx, -qy, -qz, qw)
    rx = tw * (negate qx) + tx * qw + ty * (negate qz) - tz * (negate qy)
    ry = tw * (negate qy) - tx * (negate qz) + ty * qw + tz * (negate qx)
    rz = tw * (negate qz) + tx * (negate qy) - ty * (negate qx) + tz * qw
  in
    vec3 rx ry rz
