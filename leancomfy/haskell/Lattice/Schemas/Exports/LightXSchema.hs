{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.LightXSchema
Description : Light-X export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Light-X export format enums and types.

Source: ui/src/schemas/exports/lightx-schema.ts
-}

module Lattice.Schemas.Exports.LightXSchema
  ( -- * Light-X Motion Style
    LightXMotionStyle(..)
  , lightXMotionStyleFromText
  , lightXMotionStyleToText
    -- * Light-X Relight Source
  , LightXRelightSource(..)
  , lightXRelightSourceFromText
  , lightXRelightSourceToText
    -- * Constants
  , maxFrames
  , maxFPS
  , maxFOV
  , maxClip
  , maxDimension
    -- * Structures
  , CameraTrajectoryMetadata(..)
  , CameraTrajectoryExport(..)
  , LightXRelightingConfig(..)
  , LightXExport(..)
    -- * Validation
  , isValidCameraMetadata
  , isValidCameraExport
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Light-X Motion Style
--------------------------------------------------------------------------------

-- | Light-X motion style options
data LightXMotionStyle
  = MotionGradual
  | MotionBullet
  | MotionDirect
  | MotionDollyZoom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

lightXMotionStyleFromText :: Text -> Maybe LightXMotionStyle
lightXMotionStyleFromText "gradual" = Just MotionGradual
lightXMotionStyleFromText "bullet" = Just MotionBullet
lightXMotionStyleFromText "direct" = Just MotionDirect
lightXMotionStyleFromText "dolly-zoom" = Just MotionDollyZoom
lightXMotionStyleFromText _ = Nothing

lightXMotionStyleToText :: LightXMotionStyle -> Text
lightXMotionStyleToText MotionGradual = "gradual"
lightXMotionStyleToText MotionBullet = "bullet"
lightXMotionStyleToText MotionDirect = "direct"
lightXMotionStyleToText MotionDollyZoom = "dolly-zoom"

--------------------------------------------------------------------------------
-- Light-X Relight Source
--------------------------------------------------------------------------------

-- | Light-X relighting source options
data LightXRelightSource
  = RelightText
  | RelightReference
  | RelightHDR
  | RelightBackground
  deriving stock (Eq, Show, Generic, Enum, Bounded)

lightXRelightSourceFromText :: Text -> Maybe LightXRelightSource
lightXRelightSourceFromText "text" = Just RelightText
lightXRelightSourceFromText "reference" = Just RelightReference
lightXRelightSourceFromText "hdr" = Just RelightHDR
lightXRelightSourceFromText "background" = Just RelightBackground
lightXRelightSourceFromText _ = Nothing

lightXRelightSourceToText :: LightXRelightSource -> Text
lightXRelightSourceToText RelightText = "text"
lightXRelightSourceToText RelightReference = "reference"
lightXRelightSourceToText RelightHDR = "hdr"
lightXRelightSourceToText RelightBackground = "background"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxFrames :: Int
maxFrames = 100000

maxFPS :: Double
maxFPS = 120.0

maxFOV :: Double
maxFOV = 180.0

maxClip :: Double
maxClip = 100000.0

maxDimension :: Int
maxDimension = 16384

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Camera trajectory metadata
data CameraTrajectoryMetadata = CameraTrajectoryMetadata
  { ctmFrameCount :: !Int
  , ctmFps :: !Double
  , ctmFov :: !Double
  , ctmNearClip :: !Double
  , ctmFarClip :: !Double
  , ctmWidth :: !Int
  , ctmHeight :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Camera trajectory export with 4x4 matrices
data CameraTrajectoryExport = CameraTrajectoryExport
  { cteMatrices :: !(Vector (Vector (Vector Double)))  -- ^ Array of 4x4 matrices
  , cteMetadata :: !CameraTrajectoryMetadata
  }
  deriving stock (Eq, Show, Generic)

-- | Light-X relighting configuration
data LightXRelightingConfig = LightXRelightingConfig
  { lrcSource :: !LightXRelightSource
  , lrcTextPrompt :: !(Maybe Text)
  , lrcReferenceImage :: !(Maybe Text)  -- ^ Base64
  , lrcHdrMap :: !(Maybe Text)          -- ^ Base64 or path
  , lrcBackgroundColor :: !(Maybe Text) -- ^ Hex color
  }
  deriving stock (Eq, Show, Generic)

-- | Light-X export format
data LightXExport = LightXExport
  { lxeCameraTrajectory :: !CameraTrajectoryExport
  , lxeMotionStyle :: !LightXMotionStyle
  , lxeRelighting :: !LightXRelightingConfig
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if camera trajectory metadata is valid
isValidCameraMetadata :: CameraTrajectoryMetadata -> Bool
isValidCameraMetadata m =
  ctmFrameCount m > 0 && ctmFrameCount m <= maxFrames &&
  ctmFps m > 0 && ctmFps m <= maxFPS &&
  ctmFov m > 0 && ctmFov m <= maxFOV &&
  ctmNearClip m > 0 && ctmNearClip m <= maxClip &&
  ctmFarClip m > ctmNearClip m && ctmFarClip m <= maxClip &&
  ctmWidth m > 0 && ctmWidth m <= maxDimension &&
  ctmHeight m > 0 && ctmHeight m <= maxDimension

-- | Check if camera trajectory export is valid
isValidCameraExport :: CameraTrajectoryExport -> Bool
isValidCameraExport e =
  isValidCameraMetadata (cteMetadata e) &&
  V.length (cteMatrices e) == ctmFrameCount (cteMetadata e) &&
  V.all (\mat -> V.length mat == 4 && V.all (\row -> V.length row == 4) mat) (cteMatrices e)
