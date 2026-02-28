-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // dimension // vector // vec4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 4D vector type parameterized by component type.
-- | Used for homogeneous coordinates and quaternions.

module Hydrogen.Schema.Dimension.Vector.Vec4
  ( Vec4(Vec4)
  , vec4
  , vec4Zero
  , vec4One
  , vec4Uniform
  , vec4UnitX
  , vec4UnitY
  , vec4UnitZ
  , vec4UnitW
  , addVec4
  , subtractVec4
  , scaleVec4
  , negateVec4
  , dotVec4
  , hadamardVec4
  , lengthSquaredVec4
  , lengthVec4
  , normalizeVec4
  , normalizeVec4Safe
  , distanceVec4
  , distanceSquaredVec4
  , lerpVec4
  , fromVec3Vec4
  , pointVec4
  , directionVec4
  , toVec3Vec4
  , perspectiveDivideVec4
  , getX4
  , getY4
  , getZ4
  , getW4
  , setX4
  , setY4
  , setZ4
  , setW4
  ) where

import Prelude
  ( class Eq
  , class Functor
  , class Ring
  , class Semiring
  , class Show
  , negate
  , one
  , show
  , zero
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<>)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3)

-- | 4D vector parameterized by component type
data Vec4 a = Vec4 a a a a

derive instance eqVec4 :: Eq a => Eq (Vec4 a)

instance showVec4 :: Show a => Show (Vec4 a) where
  show (Vec4 x y z w) = "Vec4(" <> show x <> ", " <> show y <> ", " <> show z <> ", " <> show w <> ")"

instance functorVec4 :: Functor Vec4 where
  map f (Vec4 x y z w) = Vec4 (f x) (f y) (f z) (f w)

-- | Create a 4D vector
vec4 :: forall a. a -> a -> a -> a -> Vec4 a
vec4 = Vec4

-- | Zero vector
vec4Zero :: forall a. Semiring a => Vec4 a
vec4Zero = Vec4 zero zero zero zero

-- | Unit vector (1,1,1,1)
vec4One :: forall a. Semiring a => Vec4 a
vec4One = Vec4 one one one one

-- | Uniform vector (all components equal)
-- | Proof reference: Vec4.lean uniform
vec4Uniform :: forall a. a -> Vec4 a
vec4Uniform s = Vec4 s s s s

-- | Unit vector along X axis
vec4UnitX :: forall a. Semiring a => Vec4 a
vec4UnitX = Vec4 one zero zero zero

-- | Unit vector along Y axis
vec4UnitY :: forall a. Semiring a => Vec4 a
vec4UnitY = Vec4 zero one zero zero

-- | Unit vector along Z axis
vec4UnitZ :: forall a. Semiring a => Vec4 a
vec4UnitZ = Vec4 zero zero one zero

-- | Unit vector along W axis
vec4UnitW :: forall a. Semiring a => Vec4 a
vec4UnitW = Vec4 zero zero zero one

-- | Add two 4D vectors
addVec4 :: forall a. Semiring a => Vec4 a -> Vec4 a -> Vec4 a
addVec4 (Vec4 x1 y1 z1 w1) (Vec4 x2 y2 z2 w2) = Vec4 (x1 + x2) (y1 + y2) (z1 + z2) (w1 + w2)

-- | Subtract two 4D vectors
subtractVec4 :: forall a. Ring a => Vec4 a -> Vec4 a -> Vec4 a
subtractVec4 (Vec4 x1 y1 z1 w1) (Vec4 x2 y2 z2 w2) = Vec4 (x1 - x2) (y1 - y2) (z1 - z2) (w1 - w2)

-- | Scale a 4D vector by a scalar
scaleVec4 :: forall a. Semiring a => a -> Vec4 a -> Vec4 a
scaleVec4 s (Vec4 x y z w) = Vec4 (s * x) (s * y) (s * z) (s * w)

-- | Negate a 4D vector
negateVec4 :: forall a. Ring a => Vec4 a -> Vec4 a
negateVec4 (Vec4 x y z w) = Vec4 (negate x) (negate y) (negate z) (negate w)

-- | Dot product of two 4D vectors
-- | Proof reference: Vec4.lean dot, dot_comm, dot_self_nonneg
dotVec4 :: forall a. Semiring a => Vec4 a -> Vec4 a -> a
dotVec4 (Vec4 x1 y1 z1 w1) (Vec4 x2 y2 z2 w2) = x1 * x2 + y1 * y2 + z1 * z2 + w1 * w2

-- | Component-wise multiplication (Hadamard product)
-- | Proof reference: Vec4.lean hadamard
hadamardVec4 :: forall a. Semiring a => Vec4 a -> Vec4 a -> Vec4 a
hadamardVec4 (Vec4 x1 y1 z1 w1) (Vec4 x2 y2 z2 w2) = Vec4 (x1 * x2) (y1 * y2) (z1 * z2) (w1 * w2)

-- | Squared length of a 4D Number vector
lengthSquaredVec4 :: Vec4 Number -> Number
lengthSquaredVec4 v = dotVec4 v v

-- | Length of a 4D Number vector
lengthVec4 :: Vec4 Number -> Number
lengthVec4 v = Math.sqrt (lengthSquaredVec4 v)

-- | Normalize a 4D Number vector to unit length
-- | Returns zero vector if input is zero
-- | Proof reference: Vec4.lean normalize
normalizeVec4 :: Vec4 Number -> Vec4 Number
normalizeVec4 v =
  let len = lengthVec4 v
  in if len == 0.0 then vec4Zero else scaleVec4 (1.0 / len) v

-- | Safe normalization that returns input unchanged for zero vectors
normalizeVec4Safe :: Vec4 Number -> Vec4 Number
normalizeVec4Safe v =
  let len = lengthVec4 v
  in if len == 0.0 then v else scaleVec4 (1.0 / len) v

-- | Distance between two 4D vectors
distanceVec4 :: Vec4 Number -> Vec4 Number -> Number
distanceVec4 a b = lengthVec4 (subtractVec4 b a)

-- | Squared distance between two 4D vectors (avoids sqrt)
distanceSquaredVec4 :: Vec4 Number -> Vec4 Number -> Number
distanceSquaredVec4 a b = lengthSquaredVec4 (subtractVec4 b a)

-- | Linear interpolation between two 4D vectors
-- | Proof reference: Vec4.lean lerp, lerp_zero, lerp_one, lerp_self
lerpVec4 :: Number -> Vec4 Number -> Vec4 Number -> Vec4 Number
lerpVec4 t (Vec4 x1 y1 z1 w1) (Vec4 x2 y2 z2 w2) = 
  Vec4 (Math.lerp x1 x2 t) (Math.lerp y1 y2 t) (Math.lerp z1 z2 t) (Math.lerp w1 w2 t)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // homogeneous coordinates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create Vec4 from Vec3 with specified w component
-- | Proof reference: Vec4.lean fromVec3, toVec3_fromVec3
fromVec3Vec4 :: Vec3 Number -> Number -> Vec4 Number
fromVec3Vec4 (Vec3 x y z) w = Vec4 x y z w

-- | Create point from Vec3 (w = 1)
-- | Points are affected by translation in matrix multiplication
-- | Proof reference: Vec4.lean point, point_w_one
pointVec4 :: Vec3 Number -> Vec4 Number
pointVec4 v = fromVec3Vec4 v 1.0

-- | Create direction from Vec3 (w = 0)
-- | Directions are NOT affected by translation (only rotation/scale)
-- | Proof reference: Vec4.lean direction, direction_w_zero
directionVec4 :: Vec3 Number -> Vec4 Number
directionVec4 v = fromVec3Vec4 v 0.0

-- | Extract xyz components as Vec3 (ignoring w)
-- | Proof reference: Vec4.lean toVec3
toVec3Vec4 :: Vec4 Number -> Vec3 Number
toVec3Vec4 (Vec4 x y z _) = vec3 x y z

-- | Perspective divide: (x/w, y/w, z/w)
-- | Used for perspective projection (e.g., after multiplying by projection matrix)
-- | Returns zero vector if w is zero
-- | Proof reference: Vec4.lean perspectiveDivide
perspectiveDivideVec4 :: Vec4 Number -> Vec3 Number
perspectiveDivideVec4 (Vec4 x y z w) =
  if w == 0.0 then vec3 0.0 0.0 0.0
  else vec3 (x / w) (y / w) (z / w)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get X component
getX4 :: forall a. Vec4 a -> a
getX4 (Vec4 x _ _ _) = x

-- | Get Y component
getY4 :: forall a. Vec4 a -> a
getY4 (Vec4 _ y _ _) = y

-- | Get Z component
getZ4 :: forall a. Vec4 a -> a
getZ4 (Vec4 _ _ z _) = z

-- | Get W component
getW4 :: forall a. Vec4 a -> a
getW4 (Vec4 _ _ _ w) = w

-- | Set X component
setX4 :: forall a. a -> Vec4 a -> Vec4 a
setX4 x' (Vec4 _ y z w) = Vec4 x' y z w

-- | Set Y component
setY4 :: forall a. a -> Vec4 a -> Vec4 a
setY4 y' (Vec4 x _ z w) = Vec4 x y' z w

-- | Set Z component
setZ4 :: forall a. a -> Vec4 a -> Vec4 a
setZ4 z' (Vec4 x y _ w) = Vec4 x y z' w

-- | Set W component
setW4 :: forall a. a -> Vec4 a -> Vec4 a
setW4 w' (Vec4 x y z _) = Vec4 x y z w'
