-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // motion // camera3d // vectors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera3D Vectors: 2D and 3D vector types for camera system.
-- |
-- | Used for positions, orientations, bezier handles, and offsets.

module Hydrogen.Schema.Motion.Camera3D.Vectors
  ( -- * Vec2
    Vec2(..)
  , mkVec2
  , vec2Zero
  
    -- * Vec3
  , Vec3(..)
  , mkVec3
  , vec3Zero
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // vec2
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D vector with finite float components.
-- |
-- | Used for bezier handles, 2D offsets, UV coordinates.
newtype Vec2 = Vec2
  { x :: Number
  , y :: Number
  }

derive instance eqVec2 :: Eq Vec2

instance showVec2 :: Show Vec2 where
  show (Vec2 v) = "(Vec2 " <> show v.x <> " " <> show v.y <> ")"

-- | Create a 2D vector.
mkVec2 :: Number -> Number -> Vec2
mkVec2 x y = Vec2 { x, y }

-- | Zero vector.
vec2Zero :: Vec2
vec2Zero = Vec2 { x: 0.0, y: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // vec3
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D vector with finite float components.
-- |
-- | Used for position, rotation, scale in 3D space.
newtype Vec3 = Vec3
  { x :: Number
  , y :: Number
  , z :: Number
  }

derive instance eqVec3 :: Eq Vec3

instance showVec3 :: Show Vec3 where
  show (Vec3 v) = "(Vec3 " <> show v.x <> " " <> show v.y <> " " <> show v.z <> ")"

-- | Create a 3D vector.
mkVec3 :: Number -> Number -> Number -> Vec3
mkVec3 x y z = Vec3 { x, y, z }

-- | Zero vector.
vec3Zero :: Vec3
vec3Zero = Vec3 { x: 0.0, y: 0.0, z: 0.0 }
