-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // gpu // scene3d // camera
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera3D — Perspective and orthographic camera definitions.
-- |
-- | ## Proof Reference
-- | Projection matrices: `proofs/Hydrogen/Math/Mat4Projection.lean`
-- | - makePerspective: near_lt_far precondition
-- | - makeOrthographic: bounds preconditions

module Hydrogen.GPU.Scene3D.Camera
  ( Camera3D
      ( PerspectiveCamera3D
      , OrthographicCamera3D
      )
  , PerspectiveCameraParams
  , perspectiveCamera
  , OrthographicCameraParams
  , orthographicCamera
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude (class Eq)

import Hydrogen.GPU.Scene3D.Position (Position3D, Direction3D)
import Hydrogen.Schema.Dimension.Physical.SI (Meter)
import Hydrogen.Schema.Geometry.Angle (Degrees)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // camera
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera for viewing the 3D scene.
-- |
-- | ## Proof Reference
-- | Projection matrices: `proofs/Hydrogen/Math/Mat4Projection.lean`
-- | - makePerspective: near_lt_far precondition
-- | - makeOrthographic: bounds preconditions
data Camera3D
  = PerspectiveCamera3D PerspectiveCameraParams
  | OrthographicCamera3D OrthographicCameraParams

derive instance eqCamera3D :: Eq Camera3D

-- | Perspective camera parameters.
-- |
-- | ## Fields
-- | - position: Camera location in world space
-- | - target: Point the camera looks at
-- | - up: Up direction (usually Y-up)
-- | - fov: Vertical field of view in degrees (bounded 1-179)
-- | - near: Near clipping plane distance (must be > 0)
-- | - far: Far clipping plane distance (must be > near)
-- | - aspect: Width / height ratio
type PerspectiveCameraParams =
  { position :: Position3D
  , target :: Position3D
  , up :: Direction3D
  , fov :: Degrees              -- Bounded 1-179
  , near :: Meter               -- Must be > 0
  , far :: Meter                -- Must be > near
  , aspect :: Number            -- Width / height
  }

-- | Create a perspective camera.
perspectiveCamera :: PerspectiveCameraParams -> Camera3D
perspectiveCamera = PerspectiveCamera3D

-- | Orthographic camera parameters (no perspective distortion).
type OrthographicCameraParams =
  { position :: Position3D
  , target :: Position3D
  , up :: Direction3D
  , left :: Meter
  , right :: Meter
  , top :: Meter
  , bottom :: Meter
  , near :: Meter
  , far :: Meter
  , zoom :: Number
  }

-- | Create an orthographic camera.
orthographicCamera :: OrthographicCameraParams -> Camera3D
orthographicCamera = OrthographicCamera3D
