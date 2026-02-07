-- | Lattice.Schemas.Exports.LightXSchema - Light-X export format enums and types
-- |
-- | Light-X export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/lightx-schema.ts

module Lattice.Schemas.Exports.LightXSchema
  ( -- Light-X Motion Style
    LightXMotionStyle(..)
  , lightXMotionStyleFromString
  , lightXMotionStyleToString
    -- Light-X Relight Source
  , LightXRelightSource(..)
  , lightXRelightSourceFromString
  , lightXRelightSourceToString
    -- Constants
  , maxFrames
  , maxFPS
  , maxFOV
  , maxClip
  , maxDimension
    -- Structures
  , CameraTrajectoryMetadata
  , CameraTrajectoryExport
  , LightXRelightingConfig
  , LightXExport
    -- Validation
  , isValidCameraMetadata
  , isValidCameraExport
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array (length, all)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Light-X Motion Style
--------------------------------------------------------------------------------

-- | Light-X motion style options
data LightXMotionStyle
  = MotionGradual
  | MotionBullet
  | MotionDirect
  | MotionDollyZoom

derive instance Eq LightXMotionStyle
derive instance Generic LightXMotionStyle _

instance Show LightXMotionStyle where
  show = genericShow

lightXMotionStyleFromString :: String -> Maybe LightXMotionStyle
lightXMotionStyleFromString = case _ of
  "gradual" -> Just MotionGradual
  "bullet" -> Just MotionBullet
  "direct" -> Just MotionDirect
  "dolly-zoom" -> Just MotionDollyZoom
  _ -> Nothing

lightXMotionStyleToString :: LightXMotionStyle -> String
lightXMotionStyleToString = case _ of
  MotionGradual -> "gradual"
  MotionBullet -> "bullet"
  MotionDirect -> "direct"
  MotionDollyZoom -> "dolly-zoom"

--------------------------------------------------------------------------------
-- Light-X Relight Source
--------------------------------------------------------------------------------

-- | Light-X relighting source options
data LightXRelightSource
  = RelightText
  | RelightReference
  | RelightHDR
  | RelightBackground

derive instance Eq LightXRelightSource
derive instance Generic LightXRelightSource _

instance Show LightXRelightSource where
  show = genericShow

lightXRelightSourceFromString :: String -> Maybe LightXRelightSource
lightXRelightSourceFromString = case _ of
  "text" -> Just RelightText
  "reference" -> Just RelightReference
  "hdr" -> Just RelightHDR
  "background" -> Just RelightBackground
  _ -> Nothing

lightXRelightSourceToString :: LightXRelightSource -> String
lightXRelightSourceToString = case _ of
  RelightText -> "text"
  RelightReference -> "reference"
  RelightHDR -> "hdr"
  RelightBackground -> "background"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxFrames :: Int
maxFrames = 100000

maxFPS :: Number
maxFPS = 120.0

maxFOV :: Number
maxFOV = 180.0

maxClip :: Number
maxClip = 100000.0

maxDimension :: Int
maxDimension = 16384

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Camera trajectory metadata
type CameraTrajectoryMetadata =
  { frameCount :: Int
  , fps :: Number
  , fov :: Number
  , nearClip :: Number
  , farClip :: Number
  , width :: Int
  , height :: Int
  }

-- | Camera trajectory export with 4x4 matrices
type CameraTrajectoryExport =
  { matrices :: Array (Array (Array Number))  -- ^ Array of 4x4 matrices
  , metadata :: CameraTrajectoryMetadata
  }

-- | Light-X relighting configuration
type LightXRelightingConfig =
  { source :: LightXRelightSource
  , textPrompt :: Maybe String
  , referenceImage :: Maybe String  -- ^ Base64
  , hdrMap :: Maybe String          -- ^ Base64 or path
  , backgroundColor :: Maybe String -- ^ Hex color
  }

-- | Light-X export format
type LightXExport =
  { cameraTrajectory :: CameraTrajectoryExport
  , motionStyle :: LightXMotionStyle
  , relighting :: LightXRelightingConfig
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if camera trajectory metadata is valid
isValidCameraMetadata :: CameraTrajectoryMetadata -> Boolean
isValidCameraMetadata m =
  m.frameCount > 0 && m.frameCount <= maxFrames &&
  m.fps > 0.0 && m.fps <= maxFPS &&
  m.fov > 0.0 && m.fov <= maxFOV &&
  m.nearClip > 0.0 && m.nearClip <= maxClip &&
  m.farClip > m.nearClip && m.farClip <= maxClip &&
  m.width > 0 && m.width <= maxDimension &&
  m.height > 0 && m.height <= maxDimension

-- | Check if camera trajectory export is valid
isValidCameraExport :: CameraTrajectoryExport -> Boolean
isValidCameraExport e =
  isValidCameraMetadata e.metadata &&
  length e.matrices == e.metadata.frameCount &&
  all (\mat -> length mat == 4 && all (\row -> length row == 4) mat) e.matrices
