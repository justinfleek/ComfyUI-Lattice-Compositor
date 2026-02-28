-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // dimension // rotation // quaternion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Unit quaternions for 3D rotation representation.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Quaternion.lean`:
-- | - mul_assoc: Quaternion multiplication is associative
-- | - mul_identity_left/right: identity × q = q × identity = q
-- | - conjugate_mul: (ab)* = b*a*
-- | - lengthSq_mul: ‖ab‖² = ‖a‖² × ‖b‖²
-- | - mul_isUnit: Unit quaternions closed under multiplication
-- | - normalize_isUnit: Normalized quaternions are unit
-- |
-- | ## Why Quaternions
-- | - No gimbal lock (unlike Euler angles)
-- | - Smooth interpolation via SLERP
-- | - Compact representation (4 floats vs 9 for rotation matrix)
-- | - Numerically stable composition
-- |
-- | ## Mathematical Background
-- | Quaternions extend complex numbers: q = w + xi + yj + zk
-- | where i² = j² = k² = ijk = -1
-- |
-- | Unit quaternions (‖q‖ = 1) form a double cover of SO(3):
-- | both q and -q represent the same rotation.
-- |
-- | Rotation of vector v by quaternion q: v' = qvq⁻¹

module Hydrogen.Schema.Dimension.Rotation.Quaternion
  ( -- * Type
    Quaternion(Quaternion)
  
  -- * Constructors
  , quaternion
  , quaternionIdentity
  , quaternionZero
  , fromAxisAngle
  , fromRotationX
  , fromRotationY
  , fromRotationZ
  
  -- * Basic Operations
  , addQuaternion
  , subtractQuaternion
  , scaleQuaternion
  , negateQuaternion
  , conjugateQuaternion
  
  -- * Quaternion Multiplication
  , mulQuaternion
  
  -- * Length and Normalization
  , lengthSqQuaternion
  , lengthQuaternion
  , normalizeQuaternion
  , isUnitQuaternion
  
  -- * Inverse
  , inverseQuaternion
  
  -- * Interpolation
  , lerpQuaternion
  , slerpQuaternion
  
  -- * Dot Product
  , dotQuaternion
  
  -- * Conversion
  , toMat4Quaternion
  , rotateVec3
  
  -- * Accessors
  , getW
  , getX
  , getY
  , getZ
  ) where

import Prelude
  ( class Eq
  , class Show
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<)
  , (>)
  , (<>)
  , (&&)
  , max
  , min
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3, lengthVec3)
import Hydrogen.Schema.Dimension.Matrix.Mat4 (Mat4(Mat4))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quaternion with real components (w, x, y, z)
-- | Convention: w is the scalar part, (x, y, z) is the vector part
-- |
-- | For rotation by angle θ around unit axis (ax, ay, az):
-- |   q = cos(θ/2) + sin(θ/2)(ax·i + ay·j + az·k)
data Quaternion = Quaternion Number Number Number Number
  -- w x y z

derive instance eqQuaternion :: Eq Quaternion

instance showQuaternion :: Show Quaternion where
  show (Quaternion w x y z) =
    "Quaternion(" <> show w <> ", " <> show x <> ", " <> show y <> ", " <> show z <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a quaternion from components
quaternion :: Number -> Number -> Number -> Number -> Quaternion
quaternion = Quaternion

-- | Identity quaternion (represents no rotation)
-- | Proof reference: Quaternion.lean identity, mul_identity_left, mul_identity_right
quaternionIdentity :: Quaternion
quaternionIdentity = Quaternion 1.0 0.0 0.0 0.0

-- | Zero quaternion (NOT a valid rotation, but useful algebraically)
-- | Proof reference: Quaternion.lean zero
quaternionZero :: Quaternion
quaternionZero = Quaternion 0.0 0.0 0.0 0.0

-- | Create quaternion from axis-angle representation
-- | Proof reference: Quaternion.lean fromAxisAngle
fromAxisAngle :: Vec3 Number -> Number -> Quaternion
fromAxisAngle axis angle =
  let
    halfAngle = angle / 2.0
    s = Math.sin halfAngle
    c = Math.cos halfAngle
    len = lengthVec3 axis
  in
    if len == 0.0 then quaternionIdentity
    else
      let
        Vec3 ax ay az = axis
        invLen = 1.0 / len
      in Quaternion c (s * ax * invLen) (s * ay * invLen) (s * az * invLen)

-- | Create quaternion for rotation around X axis
-- | Proof reference: Quaternion.lean fromRotationX, fromRotationX_isUnit
fromRotationX :: Number -> Quaternion
fromRotationX angle =
  let halfAngle = angle / 2.0
  in Quaternion (Math.cos halfAngle) (Math.sin halfAngle) 0.0 0.0

-- | Create quaternion for rotation around Y axis
-- | Proof reference: Quaternion.lean fromRotationY, fromRotationY_isUnit
fromRotationY :: Number -> Quaternion
fromRotationY angle =
  let halfAngle = angle / 2.0
  in Quaternion (Math.cos halfAngle) 0.0 (Math.sin halfAngle) 0.0

-- | Create quaternion for rotation around Z axis
-- | Proof reference: Quaternion.lean fromRotationZ, fromRotationZ_isUnit
fromRotationZ :: Number -> Quaternion
fromRotationZ angle =
  let halfAngle = angle / 2.0
  in Quaternion (Math.cos halfAngle) 0.0 0.0 (Math.sin halfAngle)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // basic operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quaternion addition
addQuaternion :: Quaternion -> Quaternion -> Quaternion
addQuaternion (Quaternion w1 x1 y1 z1) (Quaternion w2 x2 y2 z2) =
  Quaternion (w1 + w2) (x1 + x2) (y1 + y2) (z1 + z2)

-- | Quaternion subtraction
subtractQuaternion :: Quaternion -> Quaternion -> Quaternion
subtractQuaternion (Quaternion w1 x1 y1 z1) (Quaternion w2 x2 y2 z2) =
  Quaternion (w1 - w2) (x1 - x2) (y1 - y2) (z1 - z2)

-- | Scalar multiplication
scaleQuaternion :: Number -> Quaternion -> Quaternion
scaleQuaternion s (Quaternion w x y z) =
  Quaternion (s * w) (s * x) (s * y) (s * z)

-- | Negation
negateQuaternion :: Quaternion -> Quaternion
negateQuaternion (Quaternion w x y z) =
  Quaternion (negate w) (negate x) (negate y) (negate z)

-- | Conjugate: q* = w - xi - yj - zk
-- | Proof reference: Quaternion.lean conjugate, conjugate_involutive, conjugate_mul
conjugateQuaternion :: Quaternion -> Quaternion
conjugateQuaternion (Quaternion w x y z) =
  Quaternion w (negate x) (negate y) (negate z)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // quaternion multiplication
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quaternion multiplication (Hamilton product)
-- | This is the KEY operation. Non-commutative!
-- | Proof reference: Quaternion.lean mul, mul_assoc, mul_not_comm
mulQuaternion :: Quaternion -> Quaternion -> Quaternion
mulQuaternion (Quaternion w1 x1 y1 z1) (Quaternion w2 x2 y2 z2) = Quaternion
  (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2)
  (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2)
  (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2)
  (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // length and normalization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Squared length (norm squared): ‖q‖² = w² + x² + y² + z²
-- | Proof reference: Quaternion.lean lengthSq, lengthSq_nonneg, lengthSq_mul
lengthSqQuaternion :: Quaternion -> Number
lengthSqQuaternion (Quaternion w x y z) =
  w * w + x * x + y * y + z * z

-- | Length (norm): ‖q‖ = √(w² + x² + y² + z²)
-- | Proof reference: Quaternion.lean length, length_nonneg, length_mul
lengthQuaternion :: Quaternion -> Number
lengthQuaternion q = Math.sqrt (lengthSqQuaternion q)

-- | Normalize a quaternion to unit length
-- | Returns identity if input is zero
-- | Proof reference: Quaternion.lean normalize, normalize_isUnit
normalizeQuaternion :: Quaternion -> Quaternion
normalizeQuaternion q =
  let len = lengthQuaternion q
  in if len == 0.0 then quaternionIdentity
     else scaleQuaternion (1.0 / len) q

-- | Check if quaternion is unit (length ≈ 1)
-- | Proof reference: Quaternion.lean IsUnit
isUnitQuaternion :: Quaternion -> Boolean
isUnitQuaternion q =
  let lenSq = lengthSqQuaternion q
  in lenSq > 0.999 && lenSq < 1.001

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // inverse
-- ═════════════════════════════════════════════════════════════════════════════

-- | Inverse of a quaternion
-- | For unit quaternions: q⁻¹ = q* (conjugate)
-- | For general quaternions: q⁻¹ = q* / ‖q‖²
-- | Returns identity if input is zero
-- | Proof reference: Quaternion.lean inverse, mul_inverse_unit, inverse_mul_unit
inverseQuaternion :: Quaternion -> Quaternion
inverseQuaternion q =
  let lenSq = lengthSqQuaternion q
  in if lenSq == 0.0 then quaternionIdentity
     else scaleQuaternion (1.0 / lenSq) (conjugateQuaternion q)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dot product of quaternions (as 4D vectors)
-- | Proof reference: Quaternion.lean dot
dotQuaternion :: Quaternion -> Quaternion -> Number
dotQuaternion (Quaternion w1 x1 y1 z1) (Quaternion w2 x2 y2 z2) =
  w1 * w2 + x1 * x2 + y1 * y2 + z1 * z2

-- | Linear interpolation of quaternions (NOT normalized)
-- | Proof reference: Quaternion.lean lerp, lerp_zero, lerp_one
lerpQuaternion :: Quaternion -> Quaternion -> Number -> Quaternion
lerpQuaternion a b t =
  addQuaternion (scaleQuaternion (1.0 - t) a) (scaleQuaternion t b)

-- | Spherical linear interpolation (SLERP)
-- | The proper way to interpolate rotations
-- | Proof reference: Quaternion.lean slerp
slerpQuaternion :: Quaternion -> Quaternion -> Number -> Quaternion
slerpQuaternion a b t =
  let
    d = dotQuaternion a b
    -- Handle negative dot product (choose shorter arc)
    b' = if d < 0.0 then negateQuaternion b else b
    d' = if d < 0.0 then negate d else d
    -- Clamp for numerical stability
    d'' = max (negate 1.0) (min 1.0 d')
    theta = Math.acos d''
    sinTheta = Math.sin theta
  in
    -- If nearly parallel, use lerp
    if sinTheta < 0.001 then normalizeQuaternion (lerpQuaternion a b' t)
    else
      let
        s0 = Math.sin ((1.0 - t) * theta) / sinTheta
        s1 = Math.sin (t * theta) / sinTheta
      in addQuaternion (scaleQuaternion s0 a) (scaleQuaternion s1 b')

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert unit quaternion to rotation matrix
-- | Proof reference: Quaternion.lean toMat4, toMat4_identity, det_toMat4_unit
toMat4Quaternion :: Quaternion -> Mat4
toMat4Quaternion (Quaternion w x y z) =
  let
    x2 = x + x
    y2 = y + y
    z2 = z + z
    xx = x * x2
    xy = x * y2
    xz = x * z2
    yy = y * y2
    yz = y * z2
    zz = z * z2
    wx = w * x2
    wy = w * y2
    wz = w * z2
  in Mat4
    (1.0 - (yy + zz)) (xy + wz)         (xz - wy)         0.0
    (xy - wz)         (1.0 - (xx + zz)) (yz + wx)         0.0
    (xz + wy)         (yz - wx)         (1.0 - (xx + yy)) 0.0
    0.0               0.0               0.0               1.0

-- | Rotate a Vec3 by this quaternion
-- | Formula: v' = q × v × q⁻¹ (treating v as pure quaternion with w=0)
rotateVec3 :: Quaternion -> Vec3 Number -> Vec3 Number
rotateVec3 q (Vec3 vx vy vz) =
  let
    -- Convert Vec3 to pure quaternion (w=0)
    vq = Quaternion 0.0 vx vy vz
    -- q × v × q⁻¹
    result = mulQuaternion (mulQuaternion q vq) (conjugateQuaternion q)
    Quaternion _ rx ry rz = result
  in vec3 rx ry rz

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get W component (scalar part)
getW :: Quaternion -> Number
getW (Quaternion w _ _ _) = w

-- | Get X component
getX :: Quaternion -> Number
getX (Quaternion _ x _ _) = x

-- | Get Y component
getY :: Quaternion -> Number
getY (Quaternion _ _ y _) = y

-- | Get Z component
getZ :: Quaternion -> Number
getZ (Quaternion _ _ _ z) = z
