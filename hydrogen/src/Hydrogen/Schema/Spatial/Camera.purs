-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // spatial // camera
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera Compounds — 3D Camera definitions.
-- |
-- | Defines the optical properties of cameras (Perspective, Orthographic).
-- | Position and orientation are handled by `Transform3D` in the Scene graph.

module Hydrogen.Schema.Spatial.Camera
  ( Camera(..)
  , perspective
  , orthographic
  , physical
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Hydrogen.Schema.Spatial.FOV (FOV)
import Hydrogen.Schema.Spatial.NearClip (NearClip)
import Hydrogen.Schema.Spatial.FarClip (FarClip)
import Hydrogen.Schema.Spatial.FocalLength (FocalLength)
import Hydrogen.Schema.Spatial.SensorWidth (SensorWidth)
import Hydrogen.Schema.Spatial.Exposure (Exposure)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // camera
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera type definition
data Camera
  = PerspectiveCamera
      { fov :: FOV
      , near :: NearClip
      , far :: FarClip
      }
  | OrthographicCamera
      { size :: Number -- Vertical size/zoom
      , near :: NearClip
      , far :: FarClip
      }
  | PhysicalCamera
      { focalLength :: FocalLength
      , sensorWidth :: SensorWidth
      , exposure :: Exposure
      , near :: NearClip
      , far :: FarClip
      , focusDistance :: Maybe Number
      , aperture :: Maybe Number
      }

derive instance eqCamera :: Eq Camera
derive instance ordCamera :: Ord Camera
derive instance genericCamera :: Generic Camera _

instance showCamera :: Show Camera where
  show (PerspectiveCamera c) = "(PerspectiveCamera " <> show c <> ")"
  show (OrthographicCamera c) = "(OrthographicCamera " <> show c <> ")"
  show (PhysicalCamera c) = "(PhysicalCamera " <> show c <> ")"

-- | Create simple perspective camera
perspective :: FOV -> NearClip -> FarClip -> Camera
perspective fov near far = PerspectiveCamera { fov, near, far }

-- | Create orthographic camera
orthographic :: Number -> NearClip -> FarClip -> Camera
orthographic size near far = OrthographicCamera { size, near, far }

-- | Create physical camera
physical :: FocalLength -> SensorWidth -> Exposure -> NearClip -> FarClip -> Camera
physical focalLength sensorWidth exposure near far =
  PhysicalCamera
    { focalLength
    , sensorWidth
    , exposure
    , near
    , far
    , focusDistance: Nothing
    , aperture: Nothing
    }
