-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // vector
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vector types - typed coordinates in N-dimensional space.
-- |
-- | Re-exports all vector submodules and provides conversion functions.

module Hydrogen.Schema.Dimension.Vector
  ( -- * 2D Vectors
    module Hydrogen.Schema.Dimension.Vector.Vec2
  -- * 3D Vectors
  , module Hydrogen.Schema.Dimension.Vector.Vec3
  -- * 4D Vectors
  , module Hydrogen.Schema.Dimension.Vector.Vec4
  -- * N-Dimensional Vectors
  , module Hydrogen.Schema.Dimension.Vector.VecN
  
  -- * Conversions
  , vec2ToVec3
  , vec3ToVec2
  , vec3ToVec4
  , vec4ToVec3
  , vec2ToVecN
  , vec3ToVecN
  , vec4ToVecN
  ) where

import Prelude (class Semiring, zero, one, (==), (/))

import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2(Vec2), vec2, vec2Zero, vec2One, vec2UnitX, vec2UnitY, addVec2, subtractVec2, scaleVec2, negateVec2, dotVec2, lengthSquaredVec2, lengthVec2, normalizeVec2, distanceVec2, lerpVec2, perpendicularVec2, angleVec2, getX2, getY2, setX2, setY2)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3, vec3Zero, vec3One, vec3UnitX, vec3UnitY, vec3UnitZ, addVec3, subtractVec3, scaleVec3, negateVec3, dotVec3, crossVec3, lengthSquaredVec3, lengthVec3, normalizeVec3, distanceVec3, lerpVec3, reflectVec3, getX3, getY3, getZ3, setX3, setY3, setZ3)
import Hydrogen.Schema.Dimension.Vector.Vec4 (Vec4(Vec4), vec4, vec4Zero, vec4One, addVec4, subtractVec4, scaleVec4, negateVec4, dotVec4, lengthSquaredVec4, lengthVec4, normalizeVec4, lerpVec4, getX4, getY4, getZ4, getW4, setX4, setY4, setZ4, setW4)
import Hydrogen.Schema.Dimension.Vector.VecN (VecN(VecN), vecN, vecNZero, vecNFromArray, vecNToArray, dimVecN, addVecN, subtractVecN, scaleVecN, negateVecN, dotVecN, lengthSquaredVecN, lengthVecN, normalizeVecN, distanceVecN, lerpVecN, getComponentN, setComponentN)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extend 2D to 3D with z=zero
vec2ToVec3 :: forall a. Semiring a => Vec2 a -> Vec3 a
vec2ToVec3 (Vec2 x y) = Vec3 x y zero

-- | Project 3D to 2D (drop z)
vec3ToVec2 :: forall a. Vec3 a -> Vec2 a
vec3ToVec2 (Vec3 x y _) = Vec2 x y

-- | Extend 3D to 4D with w=one (point in homogeneous coordinates)
vec3ToVec4 :: forall a. Semiring a => Vec3 a -> Vec4 a
vec3ToVec4 (Vec3 x y z) = Vec4 x y z one

-- | Project 4D to 3D (perspective divide if w != 1)
vec4ToVec3 :: Vec4 Number -> Vec3 Number
vec4ToVec3 (Vec4 x y z w) =
  if w == 0.0 then Vec3 x y z
  else Vec3 (x / w) (y / w) (z / w)

-- | Convert Vec2 to VecN
vec2ToVecN :: forall a. Vec2 a -> VecN a
vec2ToVecN (Vec2 x y) = VecN [x, y]

-- | Convert Vec3 to VecN
vec3ToVecN :: forall a. Vec3 a -> VecN a
vec3ToVecN (Vec3 x y z) = VecN [x, y, z]

-- | Convert Vec4 to VecN
vec4ToVecN :: forall a. Vec4 a -> VecN a
vec4ToVecN (Vec4 x y z w) = VecN [x, y, z, w]
