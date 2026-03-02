-- | Lattice.Schemas.Imports.CameraTrackingSchema - Camera tracking import format enums and types
-- |
-- | Camera tracking import format enums and types from external tools.
-- |
-- | Source: ui/src/schemas/imports/cameraTracking-schema.ts

module Lattice.Schemas.Imports.CameraTrackingSchema
  ( -- Camera Model
    CameraModel(..)
  , cameraModelFromString
  , cameraModelToString
    -- Constants
  , maxDimension
  , maxFrames
  , maxFPS
  , maxTrackIDs
  , maxCameraPoses
  , maxTrackPoints3D
  , maxTrackPoints2D
  , maxBlenderTracks
  , maxBlenderPoints
  , maxDistortion
  , maxTangentialDistortion
  , quaternionTolerance
    -- Structures
  , Vector2
  , Vector3
  , Quaternion
  , RGBColor
  , Distortion
  , CameraIntrinsics
  , CameraPose
  , GroundPlane
  , TrackingMetadata
    -- Validation
  , isValidVector2
  , isValidVector3
  , isValidQuaternion
  , isValidRGBColor
  , isValidDistortion
  , isValidCameraIntrinsics
  , isValidCameraPose
  , isValidTrackingMetadata
  ) where

import Prelude
import Data.Maybe (Maybe(..), maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Number (isFinite)
import Math (sqrt, abs)

--------------------------------------------------------------------------------
-- Camera Model
--------------------------------------------------------------------------------

-- | Camera model types for lens distortion
data CameraModel
  = ModelPinhole
  | ModelRadial
  | ModelBrown
  | ModelFisheye

derive instance Eq CameraModel
derive instance Generic CameraModel _

instance Show CameraModel where
  show = genericShow

cameraModelFromString :: String -> Maybe CameraModel
cameraModelFromString = case _ of
  "pinhole" -> Just ModelPinhole
  "radial" -> Just ModelRadial
  "brown" -> Just ModelBrown
  "fisheye" -> Just ModelFisheye
  _ -> Nothing

cameraModelToString :: CameraModel -> String
cameraModelToString = case _ of
  ModelPinhole -> "pinhole"
  ModelRadial -> "radial"
  ModelBrown -> "brown"
  ModelFisheye -> "fisheye"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxDimension :: Int
maxDimension = 16384

maxFrames :: Int
maxFrames = 100000

maxFPS :: Number
maxFPS = 120.0

maxTrackIDs :: Int
maxTrackIDs = 1000

maxCameraPoses :: Int
maxCameraPoses = 100000

maxTrackPoints3D :: Int
maxTrackPoints3D = 100000

maxTrackPoints2D :: Int
maxTrackPoints2D = 1000000

maxBlenderTracks :: Int
maxBlenderTracks = 10000

maxBlenderPoints :: Int
maxBlenderPoints = 10000000

maxDistortion :: Number
maxDistortion = 10.0

maxTangentialDistortion :: Number
maxTangentialDistortion = 1.0

quaternionTolerance :: Number
quaternionTolerance = 0.1

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | 2D vector
type Vector2 =
  { x :: Number
  , y :: Number
  }

-- | 3D vector
type Vector3 =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Quaternion rotation
type Quaternion =
  { w :: Number
  , x :: Number
  , y :: Number
  , z :: Number
  }

-- | RGB color (0-255)
type RGBColor =
  { r :: Int
  , g :: Int
  , b :: Int
  }

-- | Lens distortion coefficients
type Distortion =
  { k1 :: Maybe Number
  , k2 :: Maybe Number
  , k3 :: Maybe Number
  , p1 :: Maybe Number
  , p2 :: Maybe Number
  }

-- | Camera intrinsics
type CameraIntrinsics =
  { focalLength :: Number
  , principalPoint :: Vector2
  , width :: Int
  , height :: Int
  , distortion :: Maybe Distortion
  , model :: Maybe CameraModel
  }

-- | Camera pose at a frame
type CameraPose =
  { frame :: Int
  , position :: Vector3
  , rotation :: Quaternion
  , eulerAngles :: Maybe Vector3
  , fov :: Maybe Number
  }

-- | Ground plane definition
type GroundPlane =
  { normal :: Vector3
  , origin :: Vector3
  , up :: Vector3
  , scale :: Maybe Number
  }

-- | Tracking metadata
type TrackingMetadata =
  { sourceWidth :: Int
  , sourceHeight :: Int
  , frameRate :: Number
  , frameCount :: Int
  , averageError :: Maybe Number
  , solveMethod :: Maybe String
  , solveDate :: Maybe String
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if 2D vector has finite values
isValidVector2 :: Vector2 -> Boolean
isValidVector2 v = isFinite v.x && isFinite v.y

-- | Check if 3D vector has finite values
isValidVector3 :: Vector3 -> Boolean
isValidVector3 v = isFinite v.x && isFinite v.y && isFinite v.z

-- | Check if quaternion is approximately normalized
isValidQuaternion :: Quaternion -> Boolean
isValidQuaternion q =
  let len = sqrt (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z)
  in abs (len - 1.0) < quaternionTolerance

-- | Check if RGB color is valid
isValidRGBColor :: RGBColor -> Boolean
isValidRGBColor c =
  c.r >= 0 && c.r <= 255 &&
  c.g >= 0 && c.g <= 255 &&
  c.b >= 0 && c.b <= 255

-- | Check if distortion coefficients are valid
isValidDistortion :: Distortion -> Boolean
isValidDistortion d =
  maybe true (\k -> abs k <= maxDistortion) d.k1 &&
  maybe true (\k -> abs k <= maxDistortion) d.k2 &&
  maybe true (\k -> abs k <= maxDistortion) d.k3 &&
  maybe true (\p -> abs p <= maxTangentialDistortion) d.p1 &&
  maybe true (\p -> abs p <= maxTangentialDistortion) d.p2

-- | Check if camera intrinsics are valid
isValidCameraIntrinsics :: CameraIntrinsics -> Boolean
isValidCameraIntrinsics ci =
  ci.focalLength > 0.0 && ci.focalLength <= 10000.0 &&
  ci.width > 0 && ci.width <= maxDimension &&
  ci.height > 0 && ci.height <= maxDimension &&
  isValidVector2 ci.principalPoint

-- | Check if camera pose is valid
isValidCameraPose :: CameraPose -> Boolean
isValidCameraPose cp =
  cp.frame <= maxFrames &&
  isValidVector3 cp.position &&
  isValidQuaternion cp.rotation

-- | Check if tracking metadata is valid
isValidTrackingMetadata :: TrackingMetadata -> Boolean
isValidTrackingMetadata m =
  m.sourceWidth > 0 && m.sourceWidth <= maxDimension &&
  m.sourceHeight > 0 && m.sourceHeight <= maxDimension &&
  m.frameRate > 0.0 && m.frameRate <= maxFPS &&
  m.frameCount > 0 && m.frameCount <= maxFrames
