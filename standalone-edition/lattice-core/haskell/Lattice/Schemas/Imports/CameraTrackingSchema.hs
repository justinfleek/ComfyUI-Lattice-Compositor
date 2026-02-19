{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Imports.CameraTrackingSchema
Description : Camera tracking import format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Camera tracking import format enums and types from external tools.

Source: ui/src/schemas/imports/cameraTracking-schema.ts
-}

module Lattice.Schemas.Imports.CameraTrackingSchema
  ( -- * Camera Model
    CameraModel(..)
  , cameraModelFromText
  , cameraModelToText
    -- * Constants
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
    -- * Structures
  , Vector2(..)
  , Vector3(..)
  , Quaternion(..)
  , RGBColor(..)
  , Distortion(..)
  , CameraIntrinsics(..)
  , CameraPose(..)
  , GroundPlane(..)
  , TrackingMetadata(..)
    -- * Validation
  , isValidVector2
  , isValidVector3
  , isValidQuaternion
  , isValidRGBColor
  , isValidDistortion
  , isValidCameraIntrinsics
  , isValidCameraPose
  , isValidTrackingMetadata
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Model
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera model types for lens distortion
data CameraModel
  = ModelPinhole
  | ModelRadial
  | ModelBrown
  | ModelFisheye
  deriving stock (Eq, Show, Generic, Enum, Bounded)

cameraModelFromText :: Text -> Maybe CameraModel
cameraModelFromText "pinhole" = Just ModelPinhole
cameraModelFromText "radial" = Just ModelRadial
cameraModelFromText "brown" = Just ModelBrown
cameraModelFromText "fisheye" = Just ModelFisheye
cameraModelFromText _ = Nothing

cameraModelToText :: CameraModel -> Text
cameraModelToText ModelPinhole = "pinhole"
cameraModelToText ModelRadial = "radial"
cameraModelToText ModelBrown = "brown"
cameraModelToText ModelFisheye = "fisheye"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxDimension :: Int
maxDimension = 16384

maxFrames :: Int
maxFrames = 100000

maxFPS :: Double
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

maxDistortion :: Double
maxDistortion = 10.0

maxTangentialDistortion :: Double
maxTangentialDistortion = 1.0

quaternionTolerance :: Double
quaternionTolerance = 0.1

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D vector
data Vector2 = Vector2
  { v2X :: !Double
  , v2Y :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | 3D vector
data Vector3 = Vector3
  { v3X :: !Double
  , v3Y :: !Double
  , v3Z :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Quaternion rotation
data Quaternion = Quaternion
  { quatW :: !Double
  , quatX :: !Double
  , quatY :: !Double
  , quatZ :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | RGB color (0-255)
data RGBColor = RGBColor
  { rgbR :: !Int
  , rgbG :: !Int
  , rgbB :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Lens distortion coefficients
data Distortion = Distortion
  { distK1 :: !(Maybe Double)
  , distK2 :: !(Maybe Double)
  , distK3 :: !(Maybe Double)
  , distP1 :: !(Maybe Double)
  , distP2 :: !(Maybe Double)
  }
  deriving stock (Eq, Show, Generic)

-- | Camera intrinsics
data CameraIntrinsics = CameraIntrinsics
  { ciFocalLength :: !Double
  , ciPrincipalPoint :: !Vector2
  , ciWidth :: !Int
  , ciHeight :: !Int
  , ciDistortion :: !(Maybe Distortion)
  , ciModel :: !(Maybe CameraModel)
  }
  deriving stock (Eq, Show, Generic)

-- | Camera pose at a frame
data CameraPose = CameraPose
  { cpFrame :: !Int
  , cpPosition :: !Vector3
  , cpRotation :: !Quaternion
  , cpEulerAngles :: !(Maybe Vector3)
  , cpFov :: !(Maybe Double)
  }
  deriving stock (Eq, Show, Generic)

-- | Ground plane definition
data GroundPlane = GroundPlane
  { gpNormal :: !Vector3
  , gpOrigin :: !Vector3
  , gpUp :: !Vector3
  , gpScale :: !(Maybe Double)
  }
  deriving stock (Eq, Show, Generic)

-- | Tracking metadata
data TrackingMetadata = TrackingMetadata
  { tmSourceWidth :: !Int
  , tmSourceHeight :: !Int
  , tmFrameRate :: !Double
  , tmFrameCount :: !Int
  , tmAverageError :: !(Maybe Double)
  , tmSolveMethod :: !(Maybe Text)
  , tmSolveDate :: !(Maybe Text)
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if 2D vector has finite values
isValidVector2 :: Vector2 -> Bool
isValidVector2 v =
  not (isNaN (v2X v) || isInfinite (v2X v)) &&
  not (isNaN (v2Y v) || isInfinite (v2Y v))

-- | Check if 3D vector has finite values
isValidVector3 :: Vector3 -> Bool
isValidVector3 v =
  not (isNaN (v3X v) || isInfinite (v3X v)) &&
  not (isNaN (v3Y v) || isInfinite (v3Y v)) &&
  not (isNaN (v3Z v) || isInfinite (v3Z v))

-- | Check if quaternion is approximately normalized
isValidQuaternion :: Quaternion -> Bool
isValidQuaternion q =
  let len = sqrt (quatW q ^ (2 :: Int) + quatX q ^ (2 :: Int) + quatY q ^ (2 :: Int) + quatZ q ^ (2 :: Int))
  in abs (len - 1) < quaternionTolerance

-- | Check if RGB color is valid
isValidRGBColor :: RGBColor -> Bool
isValidRGBColor c =
  rgbR c >= 0 && rgbR c <= 255 &&
  rgbG c >= 0 && rgbG c <= 255 &&
  rgbB c >= 0 && rgbB c <= 255

-- | Check if distortion coefficients are valid
isValidDistortion :: Distortion -> Bool
isValidDistortion d =
  maybe True (\k -> abs k <= maxDistortion) (distK1 d) &&
  maybe True (\k -> abs k <= maxDistortion) (distK2 d) &&
  maybe True (\k -> abs k <= maxDistortion) (distK3 d) &&
  maybe True (\p -> abs p <= maxTangentialDistortion) (distP1 d) &&
  maybe True (\p -> abs p <= maxTangentialDistortion) (distP2 d)

-- | Check if camera intrinsics are valid
isValidCameraIntrinsics :: CameraIntrinsics -> Bool
isValidCameraIntrinsics ci =
  ciFocalLength ci > 0 && ciFocalLength ci <= 10000 &&
  ciWidth ci > 0 && ciWidth ci <= maxDimension &&
  ciHeight ci > 0 && ciHeight ci <= maxDimension &&
  isValidVector2 (ciPrincipalPoint ci)

-- | Check if camera pose is valid
isValidCameraPose :: CameraPose -> Bool
isValidCameraPose cp =
  cpFrame cp <= maxFrames &&
  isValidVector3 (cpPosition cp) &&
  isValidQuaternion (cpRotation cp)

-- | Check if tracking metadata is valid
isValidTrackingMetadata :: TrackingMetadata -> Bool
isValidTrackingMetadata m =
  tmSourceWidth m > 0 && tmSourceWidth m <= maxDimension &&
  tmSourceHeight m > 0 && tmSourceHeight m <= maxDimension &&
  tmFrameRate m > 0 && tmFrameRate m <= maxFPS &&
  tmFrameCount m > 0 && tmFrameCount m <= maxFrames
