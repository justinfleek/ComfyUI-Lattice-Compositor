{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.ControlNetSchema
Description : ControlNet export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

ControlNet export format enums and types.

Source: ui/src/schemas/exports/controlnet-schema.ts
-}

module Lattice.Schemas.Exports.ControlNetSchema
  ( -- * ControlNet Type
    ControlNetType(..)
  , controlNetTypeFromText
  , controlNetTypeToText
    -- * Pose Output Format
  , PoseOutputFormat(..)
  , poseOutputFormatFromText
  , poseOutputFormatToText
    -- * Structures
  , ControlNetExportConfig(..)
  , PoseExportConfig(..)
    -- * Constants
  , maxThreshold
  , maxPoseKeypoints
  , maxFaceKeypoints
  , maxHandKeypoints
  , maxPeoplePerFrame
  , maxBoneWidth
  , maxKeypointRadius
  , maxOpenPoseVersion
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- ControlNet Type
-- ────────────────────────────────────────────────────────────────────────────

-- | ControlNet type options
data ControlNetType
  = CNDepth     -- Depth map
  | CNCanny     -- Canny edge detection
  | CNLineart   -- Line art extraction
  | CNSoftedge  -- Soft edge detection (HED/PIDI)
  | CNNormal    -- Normal map
  | CNScribble  -- Scribble/sketch input
  | CNSeg       -- Semantic segmentation
  | CNPose      -- OpenPose skeleton
  deriving stock (Eq, Show, Generic, Enum, Bounded)

controlNetTypeFromText :: Text -> Maybe ControlNetType
controlNetTypeFromText "depth" = Just CNDepth
controlNetTypeFromText "canny" = Just CNCanny
controlNetTypeFromText "lineart" = Just CNLineart
controlNetTypeFromText "softedge" = Just CNSoftedge
controlNetTypeFromText "normal" = Just CNNormal
controlNetTypeFromText "scribble" = Just CNScribble
controlNetTypeFromText "seg" = Just CNSeg
controlNetTypeFromText "pose" = Just CNPose
controlNetTypeFromText _ = Nothing

controlNetTypeToText :: ControlNetType -> Text
controlNetTypeToText CNDepth = "depth"
controlNetTypeToText CNCanny = "canny"
controlNetTypeToText CNLineart = "lineart"
controlNetTypeToText CNSoftedge = "softedge"
controlNetTypeToText CNNormal = "normal"
controlNetTypeToText CNScribble = "scribble"
controlNetTypeToText CNSeg = "seg"
controlNetTypeToText CNPose = "pose"

-- ────────────────────────────────────────────────────────────────────────────
-- Pose Output Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Pose output format options
data PoseOutputFormat
  = PoseImages
  | PoseJSON
  | PoseBoth
  deriving stock (Eq, Show, Generic, Enum, Bounded)

poseOutputFormatFromText :: Text -> Maybe PoseOutputFormat
poseOutputFormatFromText "images" = Just PoseImages
poseOutputFormatFromText "json" = Just PoseJSON
poseOutputFormatFromText "both" = Just PoseBoth
poseOutputFormatFromText _ = Nothing

poseOutputFormatToText :: PoseOutputFormat -> Text
poseOutputFormatToText PoseImages = "images"
poseOutputFormatToText PoseJSON = "json"
poseOutputFormatToText PoseBoth = "both"

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | ControlNet export configuration
data ControlNetExportConfig = ControlNetExportConfig
  { cnecType :: !ControlNetType
  , cnecResolution :: !Int
  , cnecThresholdLow :: !(Maybe Double)
  , cnecThresholdHigh :: !(Maybe Double)
  , cnecDetectResolution :: !(Maybe Int)
  }
  deriving stock (Eq, Show, Generic)

-- | Pose export configuration
data PoseExportConfig = PoseExportConfig
  { pecWidth :: !Int
  , pecHeight :: !Int
  , pecStartFrame :: !Int
  , pecEndFrame :: !Int
  , pecBoneWidth :: !Double
  , pecKeypointRadius :: !Double
  , pecShowKeypoints :: !Bool
  , pecShowBones :: !Bool
  , pecUseOpenPoseColors :: !Bool
  , pecOutputFormat :: !PoseOutputFormat
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxThreshold :: Double
maxThreshold = 255.0

maxPoseKeypoints :: Int
maxPoseKeypoints = 1000

maxFaceKeypoints :: Int
maxFaceKeypoints = 1000

maxHandKeypoints :: Int
maxHandKeypoints = 500

maxPeoplePerFrame :: Int
maxPeoplePerFrame = 1000

maxBoneWidth :: Double
maxBoneWidth = 100.0

maxKeypointRadius :: Double
maxKeypointRadius = 100.0

maxOpenPoseVersion :: Int
maxOpenPoseVersion = 100
