-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // motion // camera3d // keyframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera3D Keyframe: Animation keyframes for 3D camera properties.
-- |
-- | Supports position, orientation, lens, and focus animation with
-- | spatial and temporal interpolation controls.

module Hydrogen.Schema.Motion.Camera3D.Keyframe
  ( CameraKeyframe(..)
  , mkCameraKeyframe
  , cameraKeyframeAtFrame
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Temporal (Frames)

import Hydrogen.Schema.Motion.Camera3D.Enums
  ( SpatialInterpolation
  , TemporalInterpolation
  )
import Hydrogen.Schema.Motion.Camera3D.Vectors (Vec2, Vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // camera // keyframe
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyframe data for camera animation.
-- |
-- | Only non-Nothing values are keyframed; others inherit from previous keyframe.
newtype CameraKeyframe = CameraKeyframe
  { frame                 :: Frames
  -- Transform (optional)
  , position              :: Maybe Vec3
  , pointOfInterest       :: Maybe Vec3
  , orientation           :: Maybe Vec3
  , xRotation             :: Maybe Number
  , yRotation             :: Maybe Number
  , zRotation             :: Maybe Number
  -- Lens
  , zoom                  :: Maybe Number
  , focalLength           :: Maybe Number
  , focusDistance         :: Maybe Number
  , aperture              :: Maybe Number
  -- Bezier handles
  , inHandle              :: Maybe Vec2
  , outHandle             :: Maybe Vec2
  -- Interpolation
  , spatialInterpolation  :: Maybe SpatialInterpolation
  , temporalInterpolation :: Maybe TemporalInterpolation
  -- Separate dimensions
  , separateDimensions    :: Boolean
  }

derive instance eqCameraKeyframe :: Eq CameraKeyframe

instance showCameraKeyframe :: Show CameraKeyframe where
  show (CameraKeyframe kf) =
    "(CameraKeyframe@" <> show kf.frame <> ")"

-- | Create a camera keyframe.
mkCameraKeyframe
  :: { frame                 :: Frames
     , position              :: Maybe Vec3
     , pointOfInterest       :: Maybe Vec3
     , orientation           :: Maybe Vec3
     , xRotation             :: Maybe Number
     , yRotation             :: Maybe Number
     , zRotation             :: Maybe Number
     , zoom                  :: Maybe Number
     , focalLength           :: Maybe Number
     , focusDistance         :: Maybe Number
     , aperture              :: Maybe Number
     , inHandle              :: Maybe Vec2
     , outHandle             :: Maybe Vec2
     , spatialInterpolation  :: Maybe SpatialInterpolation
     , temporalInterpolation :: Maybe TemporalInterpolation
     , separateDimensions    :: Boolean
     }
  -> CameraKeyframe
mkCameraKeyframe cfg = CameraKeyframe cfg

-- | Create an empty keyframe at a specific frame.
cameraKeyframeAtFrame :: Frames -> CameraKeyframe
cameraKeyframeAtFrame f = CameraKeyframe
  { frame: f
  , position: Nothing
  , pointOfInterest: Nothing
  , orientation: Nothing
  , xRotation: Nothing
  , yRotation: Nothing
  , zRotation: Nothing
  , zoom: Nothing
  , focalLength: Nothing
  , focusDistance: Nothing
  , aperture: Nothing
  , inHandle: Nothing
  , outHandle: Nothing
  , spatialInterpolation: Nothing
  , temporalInterpolation: Nothing
  , separateDimensions: false
  }
