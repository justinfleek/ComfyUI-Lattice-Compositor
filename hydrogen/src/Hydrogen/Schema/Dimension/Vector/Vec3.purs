-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // dimension // vector // vec3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D vector type parameterized by component type.

-- | ═══════════════════════════════════════════════════════════════════════════
-- | Status: ✓ PROVEN (Hydrogen.Math.Vec3 in Lean4)
-- |
-- | Invariants proven in Lean4:
-- |   • cross_perp_left: dot a (cross a b) = 0
-- |   • cross_perp_right: dot b (cross a b) = 0
-- |   • normalize_length: length (normalize v) = 1 (for v ≠ zero)
-- |   • project_reject_orthogonal: dot (project a b) (reject a b) = 0
-- |   • project_reject_sum: add (project a b) (reject a b) = a
-- |   • add_comm, add_assoc, scale_distrib_vec
-- | ═══════════════════════════════════════════════════════════════════════════

module Hydrogen.Schema.Dimension.Vector.Vec3
  ( Vec3(Vec3)
  , vec3
  , vec3Zero
  , vec3One
  , vec3UnitX
  , vec3UnitY
  , vec3UnitZ
  , addVec3
  , subtractVec3
  , scaleVec3
  , negateVec3
  , dotVec3
  , crossVec3
  , hadamardVec3
  , lengthSquaredVec3
  , lengthVec3
  , normalizeVec3
  , normalizeVec3Safe
  , distanceVec3
  , distanceSquaredVec3
  , lerpVec3
  , reflectVec3
  , projectVec3
  , rejectVec3
  , getX3
  , getY3
  , getZ3
  , setX3
  , setY3
  , setZ3
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

-- | 3D vector parameterized by component type
data Vec3 a = Vec3 a a a

derive instance eqVec3 :: Eq a => Eq (Vec3 a)

instance showVec3 :: Show a => Show (Vec3 a) where
  show (Vec3 x y z) = "Vec3(" <> show x <> ", " <> show y <> ", " <> show z <> ")"

instance functorVec3 :: Functor Vec3 where
  map f (Vec3 x y z) = Vec3 (f x) (f y) (f z)

-- | Create a 3D vector
vec3 :: forall a. a -> a -> a -> Vec3 a
vec3 = Vec3

-- | Zero vector
vec3Zero :: forall a. Semiring a => Vec3 a
vec3Zero = Vec3 zero zero zero

-- | Unit vector (1,1,1)
vec3One :: forall a. Semiring a => Vec3 a
vec3One = Vec3 one one one

-- | Unit vector along X axis
vec3UnitX :: forall a. Semiring a => Vec3 a
vec3UnitX = Vec3 one zero zero

-- | Unit vector along Y axis
vec3UnitY :: forall a. Semiring a => Vec3 a
vec3UnitY = Vec3 zero one zero

-- | Unit vector along Z axis
vec3UnitZ :: forall a. Semiring a => Vec3 a
vec3UnitZ = Vec3 zero zero one

-- | Add two 3D vectors
addVec3 :: forall a. Semiring a => Vec3 a -> Vec3 a -> Vec3 a
addVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = Vec3 (x1 + x2) (y1 + y2) (z1 + z2)

-- | Subtract two 3D vectors
subtractVec3 :: forall a. Ring a => Vec3 a -> Vec3 a -> Vec3 a
subtractVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = Vec3 (x1 - x2) (y1 - y2) (z1 - z2)

-- | Scale a 3D vector by a scalar
scaleVec3 :: forall a. Semiring a => a -> Vec3 a -> Vec3 a
scaleVec3 s (Vec3 x y z) = Vec3 (s * x) (s * y) (s * z)

-- | Negate a 3D vector
negateVec3 :: forall a. Ring a => Vec3 a -> Vec3 a
negateVec3 (Vec3 x y z) = Vec3 (negate x) (negate y) (negate z)

-- | Dot product of two 3D vectors
dotVec3 :: forall a. Semiring a => Vec3 a -> Vec3 a -> a
dotVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = x1 * x2 + y1 * y2 + z1 * z2

-- | Cross product of two 3D vectors
-- | PROVEN: cross_perp_left, cross_perp_right, cross_anticomm, cross_self
crossVec3 :: forall a. Ring a => Vec3 a -> Vec3 a -> Vec3 a
crossVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = Vec3
  (y1 * z2 - z1 * y2)
  (z1 * x2 - x1 * z2)
  (x1 * y2 - y1 * x2)

-- | Hadamard (component-wise) product
hadamardVec3 :: forall a. Semiring a => Vec3 a -> Vec3 a -> Vec3 a
hadamardVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = Vec3 (x1 * x2) (y1 * y2) (z1 * z2)

-- | Squared length of a 3D Number vector
lengthSquaredVec3 :: Vec3 Number -> Number
lengthSquaredVec3 v = dotVec3 v v

-- | Length of a 3D Number vector
lengthVec3 :: Vec3 Number -> Number
lengthVec3 v = Math.sqrt (lengthSquaredVec3 v)

-- | Normalize a 3D Number vector to unit length
-- | PROVEN: normalize_length (result has length 1 for non-zero input)
-- | WARNING: Caller must ensure v ≠ zero
normalizeVec3 :: Vec3 Number -> Vec3 Number
normalizeVec3 v =
  let len = lengthVec3 v
  in scaleVec3 (1.0 / len) v

-- | Safe normalize (returns input unchanged for zero vector)
normalizeVec3Safe :: Vec3 Number -> Vec3 Number
normalizeVec3Safe v =
  let len = lengthVec3 v
  in if len == 0.0 then v else scaleVec3 (1.0 / len) v

-- | Distance between two 3D points
distanceVec3 :: Vec3 Number -> Vec3 Number -> Number
distanceVec3 a b = lengthVec3 (subtractVec3 b a)

-- | Squared distance (avoids sqrt, useful for comparisons)
distanceSquaredVec3 :: Vec3 Number -> Vec3 Number -> Number
distanceSquaredVec3 a b = lengthSquaredVec3 (subtractVec3 b a)

-- | Linear interpolation between two 3D vectors
lerpVec3 :: Number -> Vec3 Number -> Vec3 Number -> Vec3 Number
lerpVec3 t (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) = 
  Vec3 (Math.lerp x1 x2 t) (Math.lerp y1 y2 t) (Math.lerp z1 z2 t)

-- | Reflect a vector around a normal
reflectVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
reflectVec3 incident normal =
  let d = 2.0 * dotVec3 incident normal
  in subtractVec3 incident (scaleVec3 d normal)

-- | Project vector a onto vector b
-- | PROVEN: project_reject_orthogonal (dot (project a b) (reject a b) = 0)
-- | WARNING: Caller must ensure b ≠ zero
projectVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
projectVec3 a b = 
  let scalar = dotVec3 a b / dotVec3 b b
  in scaleVec3 scalar b

-- | Reject: component of a perpendicular to b
-- | PROVEN: project_reject_sum (add (project a b) (reject a b) = a)
-- | WARNING: Caller must ensure b ≠ zero
rejectVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
rejectVec3 a b = subtractVec3 a (projectVec3 a b)

-- | Get X component
getX3 :: forall a. Vec3 a -> a
getX3 (Vec3 x _ _) = x

-- | Get Y component
getY3 :: forall a. Vec3 a -> a
getY3 (Vec3 _ y _) = y

-- | Get Z component
getZ3 :: forall a. Vec3 a -> a
getZ3 (Vec3 _ _ z) = z

-- | Set X component
setX3 :: forall a. a -> Vec3 a -> Vec3 a
setX3 x' (Vec3 _ y z) = Vec3 x' y z

-- | Set Y component
setY3 :: forall a. a -> Vec3 a -> Vec3 a
setY3 y' (Vec3 x _ z) = Vec3 x y' z

-- | Set Z component
setZ3 :: forall a. a -> Vec3 a -> Vec3 a
setZ3 z' (Vec3 x y _) = Vec3 x y z'
