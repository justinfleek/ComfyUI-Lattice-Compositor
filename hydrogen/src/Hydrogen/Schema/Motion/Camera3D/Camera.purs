-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // motion // camera3d // camera
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera3D Camera: Complete 3D camera definition.
-- |
-- | Supports one-node and two-node cameras with full lens simulation.

module Hydrogen.Schema.Motion.Camera3D.Camera
  ( -- * Camera ID
    CameraId(..)
  , mkCameraId
  
    -- * Camera3D
  , Camera3D(..)
  , mkCamera3D
  , defaultCamera3D
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (clampNumber, clampNumberMin)

import Hydrogen.Schema.Motion.Camera3D.Enums
  ( CameraType(CTTwoNode)
  , AutoOrientMode(AOMOff)
  , MeasureFilmSize(MFSHorizontal)
  )
import Hydrogen.Schema.Motion.Camera3D.Vectors (Vec3, mkVec3, vec3Zero)
import Hydrogen.Schema.Motion.Camera3D.DepthOfField
  ( DepthOfFieldSettings
  , IrisProperties
  , HighlightProperties
  , defaultDepthOfFieldSettings
  , defaultIrisProperties
  , defaultHighlightProperties
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // camera // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a camera.
-- |
-- | Uses NonEmptyString semantics — must have at least one character.
newtype CameraId = CameraId String

derive instance eqCameraId :: Eq CameraId
derive instance ordCameraId :: Ord CameraId

instance showCameraId :: Show CameraId where
  show (CameraId id) = "(CameraId " <> id <> ")"

-- | Create a camera ID from a non-empty string.
-- | Returns Nothing if the string is empty.
mkCameraId :: String -> Maybe CameraId
mkCameraId "" = Nothing
mkCameraId s = Just (CameraId s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // camera // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D camera definition.
-- |
-- | Supports both one-node and two-node cameras with full lens simulation.
newtype Camera3D = Camera3D
  { id              :: CameraId
  , name            :: String            -- ^ Display name
  , cameraType      :: CameraType
  -- Transform
  , position        :: Vec3              -- ^ World position
  , pointOfInterest :: Vec3              -- ^ POI for two-node cameras
  , orientation     :: Vec3              -- ^ Combined XYZ rotation
  , xRotation       :: Number            -- ^ Individual X rotation
  , yRotation       :: Number            -- ^ Individual Y rotation
  , zRotation       :: Number            -- ^ Individual Z rotation
  -- Lens settings
  , zoom            :: Number            -- ^ Zoom in pixels (positive)
  , focalLength     :: Number            -- ^ Focal length in mm (positive)
  , angleOfView     :: Number            -- ^ Angle of view in degrees (positive)
  , filmSize        :: Number            -- ^ Film size in mm (default 36)
  , measureFilmSize :: MeasureFilmSize
  -- Depth of field
  , depthOfField    :: DepthOfFieldSettings
  -- Iris
  , iris            :: IrisProperties
  -- Highlight
  , highlight       :: HighlightProperties
  -- Auto-orient
  , autoOrient      :: AutoOrientMode
  -- Clipping
  , nearClip        :: Number            -- ^ Near clip plane (positive)
  , farClip         :: Number            -- ^ Far clip plane (positive)
  }

derive instance eqCamera3D :: Eq Camera3D

instance showCamera3D :: Show Camera3D where
  show (Camera3D c) =
    "(Camera3D " <> c.name
    <> " " <> show c.focalLength <> "mm"
    <> " " <> show c.cameraType <> ")"

-- | Create a 3D camera with validation.
mkCamera3D
  :: { id              :: CameraId
     , name            :: String
     , cameraType      :: CameraType
     , position        :: Vec3
     , pointOfInterest :: Vec3
     , orientation     :: Vec3
     , xRotation       :: Number
     , yRotation       :: Number
     , zRotation       :: Number
     , zoom            :: Number
     , focalLength     :: Number
     , angleOfView     :: Number
     , filmSize        :: Number
     , measureFilmSize :: MeasureFilmSize
     , depthOfField    :: DepthOfFieldSettings
     , iris            :: IrisProperties
     , highlight       :: HighlightProperties
     , autoOrient      :: AutoOrientMode
     , nearClip        :: Number
     , farClip         :: Number
     }
  -> Camera3D
mkCamera3D cfg = Camera3D
  { id: cfg.id
  , name: cfg.name
  , cameraType: cfg.cameraType
  , position: cfg.position
  , pointOfInterest: cfg.pointOfInterest
  , orientation: cfg.orientation
  , xRotation: cfg.xRotation
  , yRotation: cfg.yRotation
  , zRotation: cfg.zRotation
  , zoom: clampNumberMin 0.1 cfg.zoom
  , focalLength: clampNumberMin 0.1 cfg.focalLength
  , angleOfView: clampNumber 0.1 179.9 cfg.angleOfView
  , filmSize: clampNumberMin 0.1 cfg.filmSize
  , measureFilmSize: cfg.measureFilmSize
  , depthOfField: cfg.depthOfField
  , iris: cfg.iris
  , highlight: cfg.highlight
  , autoOrient: cfg.autoOrient
  , nearClip: clampNumberMin 0.001 cfg.nearClip
  , farClip: clampNumberMin 1.0 cfg.farClip
  }

-- | Default 3D camera (50mm, standard position).
defaultCamera3D :: CameraId -> Camera3D
defaultCamera3D cameraId = Camera3D
  { id: cameraId
  , name: "Camera 1"
  , cameraType: CTTwoNode
  , position: mkVec3 0.0 0.0 (negate 1500.0)
  , pointOfInterest: vec3Zero
  , orientation: vec3Zero
  , xRotation: 0.0
  , yRotation: 0.0
  , zRotation: 0.0
  , zoom: 800.0
  , focalLength: 50.0
  , angleOfView: 39.6
  , filmSize: 36.0
  , measureFilmSize: MFSHorizontal
  , depthOfField: defaultDepthOfFieldSettings
  , iris: defaultIrisProperties
  , highlight: defaultHighlightProperties
  , autoOrient: AOMOff
  , nearClip: 0.001
  , farClip: 10000.0
  }
