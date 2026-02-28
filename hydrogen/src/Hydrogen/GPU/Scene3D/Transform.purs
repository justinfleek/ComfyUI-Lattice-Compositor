-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // scene3d // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transform3D — Transform and clipping plane definitions.
-- |
-- | ## Transform
-- | Combines position, rotation (quaternion), and scale for hierarchical
-- | positioning via PushTransform/PopTransform commands.
-- |
-- | ## ClipPlane
-- | Defines a clipping plane for sectioning geometry.

module Hydrogen.GPU.Scene3D.Transform
  ( Transform3DParams
  , transform3DParams
  , identityTransform3D
  , ClipPlane3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.Scene3D.Position (Position3D, Direction3D, zeroPosition3D)
import Hydrogen.Schema.Dimension.Physical.SI (Meter)
import Hydrogen.Schema.Dimension.Rotation.Quaternion (Quaternion, quaternionIdentity)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform parameters for hierarchical positioning.
type Transform3DParams =
  { position :: Position3D
  , rotation :: Quaternion
  , scale :: Vec3 Number
  }

-- | Create transform parameters.
transform3DParams :: Position3D -> Quaternion -> Vec3 Number -> Transform3DParams
transform3DParams position rotation scale = { position, rotation, scale }

-- | Identity transform (no change).
identityTransform3D :: Transform3DParams
identityTransform3D =
  { position: zeroPosition3D
  , rotation: quaternionIdentity
  , scale: vec3 1.0 1.0 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // clip plane
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clipping plane for sectioning geometry.
type ClipPlane3D =
  { normal :: Direction3D
  , constant :: Meter         -- Distance from origin along normal
  }
