-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // dimension // rotation // euler
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Euler angles with rotation order for 3D rotations.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Euler.lean`:
-- | - toQuaternion_zeroWithOrder: Zero Euler → identity quaternion (all orders)
-- | - toMat3_zeroWithOrder: Zero Euler → identity Mat3 (all orders)
-- | - toMat4_zeroWithOrder: Zero Euler → identity Mat4 (all orders)
-- | - neg_neg: Double negation is identity
-- | - neg_preserves_order: Negation preserves rotation order
-- | - toVec3_fromVec3: Vec3 round-trip is identity
-- |
-- | ## Three.js Parity
-- | - All six rotation orders: XYZ, YZX, ZXY, XZY, YXZ, ZYX
-- | - Intrinsic Tait-Bryan angles (local coordinate rotations)
-- | - Conversion to/from quaternions and matrices
-- |
-- | ## Why Euler Angles
-- | Euler angles are intuitive for humans (pitch, yaw, roll) but suffer from
-- | gimbal lock. For interpolation and composition, convert to Quaternion.
-- |
-- | ## Mathematical Background
-- | Euler angles represent rotation as three successive rotations about
-- | coordinate axes. The rotation order matters: XYZ ≠ ZYX.
-- |
-- | For intrinsic rotations (Three.js convention), rotations are applied
-- | with respect to the local (rotating) coordinate system. In matrix form:
-- | M_XYZ = Rz(z) × Ry(y) × Rx(x)

module Hydrogen.Schema.Dimension.Rotation.Euler
  ( -- * Types
    RotationOrder(..)
  , Euler(Euler)
  
  -- * Rotation Order
  , defaultOrder
  
  -- * Constructors
  , euler
  , eulerZero
  , eulerZeroWithOrder
  , eulerFromAngles
  , eulerFromAnglesWithOrder
  , eulerFromVec3
  , eulerFromVec3WithOrder
  
  -- * Basic Operations
  , toVec3Euler
  , setOrderEuler
  , negEuler
  
  -- * Conversions
  , toMat3Euler
  , toMat4Euler
  , toQuaternionEuler
  
  -- * Accessors
  , getX
  , getY
  , getZ
  , getOrder
  ) where

import Prelude
  ( class Eq
  , class Show
  , negate
  , show
  , (<>)
  )

import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3)
import Hydrogen.Schema.Dimension.Matrix.Mat3 
  ( Mat3
  , makeRotationX3
  , makeRotationY3
  , makeRotationZ3
  , mulMat3
  )
import Hydrogen.Schema.Dimension.Matrix.Mat4 
  ( Mat4
  , makeRotationX4
  , makeRotationY4
  , makeRotationZ4
  , mulMat4
  )
import Hydrogen.Schema.Dimension.Rotation.Quaternion
  ( Quaternion
  , fromRotationX
  , fromRotationY
  , fromRotationZ
  , mulQuaternion
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // rotation order
-- ═════════════════════════════════════════════════════════════════════════════

-- | The six possible rotation orders for Euler angles.
-- | Each order specifies which axis to rotate around first, second, third.
-- | Three.js uses intrinsic rotations (local coordinate system).
-- |
-- | Proof reference: Euler.lean RotationOrder
data RotationOrder
  = XYZ  -- ^ Default: rotate X, then Y, then Z
  | YZX
  | ZXY
  | XZY
  | YXZ
  | ZYX

derive instance eqRotationOrder :: Eq RotationOrder

instance showRotationOrder :: Show RotationOrder where
  show XYZ = "XYZ"
  show YZX = "YZX"
  show ZXY = "ZXY"
  show XZY = "XZY"
  show YXZ = "YXZ"
  show ZYX = "ZYX"

-- | The default rotation order (XYZ)
-- | Proof reference: Euler.lean RotationOrder.default
defaultOrder :: RotationOrder
defaultOrder = XYZ

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Euler angles representing a 3D rotation.
-- |
-- | - x: rotation angle around X axis (pitch) in radians
-- | - y: rotation angle around Y axis (yaw) in radians
-- | - z: rotation angle around Z axis (roll) in radians
-- | - order: the order in which rotations are applied
-- |
-- | Three.js uses intrinsic Tait-Bryan angles: rotations are performed
-- | with respect to the local (rotating) coordinate system.
-- |
-- | Proof reference: Euler.lean Euler
data Euler = Euler Number Number Number RotationOrder

derive instance eqEuler :: Eq Euler

instance showEuler :: Show Euler where
  show (Euler x y z order) =
    "Euler(" <> show x <> ", " <> show y <> ", " <> show z <> ", " <> show order <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create Euler angles from components
euler :: Number -> Number -> Number -> RotationOrder -> Euler
euler = Euler

-- | Zero rotation (identity) with default XYZ order
-- | Proof reference: Euler.lean zero, toMat3_zero_XYZ, toMat4_zero_XYZ, toQuaternion_zero_XYZ
eulerZero :: Euler
eulerZero = Euler 0.0 0.0 0.0 XYZ

-- | Zero rotation with specified order
-- | Proof reference: Euler.lean zeroWithOrder, toMat3_zeroWithOrder, toMat4_zeroWithOrder
eulerZeroWithOrder :: RotationOrder -> Euler
eulerZeroWithOrder order = Euler 0.0 0.0 0.0 order

-- | Create Euler from angles with default XYZ order
-- | Proof reference: Euler.lean fromAngles
eulerFromAngles :: Number -> Number -> Number -> Euler
eulerFromAngles x y z = Euler x y z XYZ

-- | Create Euler from angles with specified order
-- | Proof reference: Euler.lean fromAnglesWithOrder
eulerFromAnglesWithOrder :: Number -> Number -> Number -> RotationOrder -> Euler
eulerFromAnglesWithOrder = Euler

-- | Create Euler from a Vec3 (using x, y, z as angles) with default order
-- | Proof reference: Euler.lean fromVec3
eulerFromVec3 :: Vec3 Number -> Euler
eulerFromVec3 (Vec3 x y z) = Euler x y z XYZ

-- | Create Euler from a Vec3 with specified order
-- | Proof reference: Euler.lean fromVec3WithOrder
eulerFromVec3WithOrder :: Vec3 Number -> RotationOrder -> Euler
eulerFromVec3WithOrder (Vec3 x y z) order = Euler x y z order

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // basic operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Euler angles to Vec3 (loses order information)
-- | Proof reference: Euler.lean toVec3, toVec3_fromVec3
toVec3Euler :: Euler -> Vec3 Number
toVec3Euler (Euler x y z _) = vec3 x y z

-- | Set a new rotation order (reinterprets existing angles)
-- | Note: This does NOT convert the rotation — it reinterprets the same
-- | angle values with a different application order.
-- | Proof reference: Euler.lean setOrder, setOrder_preserves_x/y/z, setOrder_same
setOrderEuler :: RotationOrder -> Euler -> Euler
setOrderEuler order (Euler x y z _) = Euler x y z order

-- | Negation (reverse rotation)
-- | Proof reference: Euler.lean neg, neg_neg, neg_zero, neg_preserves_order
negEuler :: Euler -> Euler
negEuler (Euler x y z order) = Euler (negate x) (negate y) (negate z) order

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // conversion to mat3
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Euler angles to Mat3 rotation matrix.
-- |
-- | For intrinsic rotations with order XYZ:
-- | M = Rz(z) × Ry(y) × Rx(x)
-- |
-- | The rotation matrices are multiplied in REVERSE order because
-- | intrinsic rotations apply from right to left.
-- |
-- | Proof reference: Euler.lean toMat3, toMat3_zeroWithOrder
toMat3Euler :: Euler -> Mat3
toMat3Euler (Euler x y z order) =
  let
    rx = makeRotationX3 x
    ry = makeRotationY3 y
    rz = makeRotationZ3 z
  in case order of
    XYZ -> mulMat3 (mulMat3 rz ry) rx  -- Z(Y(X))
    YZX -> mulMat3 (mulMat3 rx rz) ry  -- X(Z(Y))
    ZXY -> mulMat3 (mulMat3 ry rx) rz  -- Y(X(Z))
    XZY -> mulMat3 (mulMat3 ry rz) rx  -- Y(Z(X))
    YXZ -> mulMat3 (mulMat3 rz rx) ry  -- Z(X(Y))
    ZYX -> mulMat3 (mulMat3 rx ry) rz  -- X(Y(Z))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // conversion to mat4
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Euler angles to Mat4 rotation matrix.
-- | The translation component is zero (pure rotation).
-- |
-- | Proof reference: Euler.lean toMat4, toMat4_zeroWithOrder
toMat4Euler :: Euler -> Mat4
toMat4Euler (Euler x y z order) =
  let
    rx = makeRotationX4 x
    ry = makeRotationY4 y
    rz = makeRotationZ4 z
  in case order of
    XYZ -> mulMat4 (mulMat4 rz ry) rx  -- Z(Y(X))
    YZX -> mulMat4 (mulMat4 rx rz) ry  -- X(Z(Y))
    ZXY -> mulMat4 (mulMat4 ry rx) rz  -- Y(X(Z))
    XZY -> mulMat4 (mulMat4 ry rz) rx  -- Y(Z(X))
    YXZ -> mulMat4 (mulMat4 rz rx) ry  -- Z(X(Y))
    ZYX -> mulMat4 (mulMat4 rx ry) rz  -- X(Y(Z))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // conversion to quaternion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Euler angles to Quaternion.
-- |
-- | Uses the formula for composing axis rotations into a single quaternion.
-- | For XYZ order: q = qz * qy * qx (applying x first, then y, then z)
-- |
-- | Proof reference: Euler.lean toQuaternion, toQuaternion_zeroWithOrder
toQuaternionEuler :: Euler -> Quaternion
toQuaternionEuler (Euler x y z order) =
  let
    qx = fromRotationX x
    qy = fromRotationY y
    qz = fromRotationZ z
  in case order of
    XYZ -> mulQuaternion (mulQuaternion qz qy) qx  -- qz * qy * qx
    YZX -> mulQuaternion (mulQuaternion qx qz) qy  -- qx * qz * qy
    ZXY -> mulQuaternion (mulQuaternion qy qx) qz  -- qy * qx * qz
    XZY -> mulQuaternion (mulQuaternion qy qz) qx  -- qy * qz * qx
    YXZ -> mulQuaternion (mulQuaternion qz qx) qy  -- qz * qx * qy
    ZYX -> mulQuaternion (mulQuaternion qx qy) qz  -- qx * qy * qz

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get X component (rotation around X axis in radians)
getX :: Euler -> Number
getX (Euler x _ _ _) = x

-- | Get Y component (rotation around Y axis in radians)
getY :: Euler -> Number
getY (Euler _ y _ _) = y

-- | Get Z component (rotation around Z axis in radians)
getZ :: Euler -> Number
getZ (Euler _ _ z _) = z

-- | Get rotation order
getOrder :: Euler -> RotationOrder
getOrder (Euler _ _ _ order) = order
