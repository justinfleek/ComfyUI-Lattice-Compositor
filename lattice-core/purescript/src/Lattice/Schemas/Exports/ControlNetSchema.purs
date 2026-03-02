-- | Lattice.Schemas.Exports.ControlNetSchema - ControlNet export format enums and types
-- |
-- | ControlNet export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/controlnet-schema.ts

module Lattice.Schemas.Exports.ControlNetSchema
  ( -- ControlNet Type
    ControlNetType(..)
  , controlNetTypeFromString
  , controlNetTypeToString
    -- Pose Output Format
  , PoseOutputFormat(..)
  , poseOutputFormatFromString
  , poseOutputFormatToString
    -- Structures
  , ControlNetExportConfig
  , PoseExportConfig
    -- Constants
  , maxThreshold
  , maxPoseKeypoints
  , maxFaceKeypoints
  , maxHandKeypoints
  , maxPeoplePerFrame
  , maxBoneWidth
  , maxKeypointRadius
  , maxOpenPoseVersion
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

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

derive instance Eq ControlNetType
derive instance Generic ControlNetType _

instance Show ControlNetType where
  show = genericShow

controlNetTypeFromString :: String -> Maybe ControlNetType
controlNetTypeFromString = case _ of
  "depth" -> Just CNDepth
  "canny" -> Just CNCanny
  "lineart" -> Just CNLineart
  "softedge" -> Just CNSoftedge
  "normal" -> Just CNNormal
  "scribble" -> Just CNScribble
  "seg" -> Just CNSeg
  "pose" -> Just CNPose
  _ -> Nothing

controlNetTypeToString :: ControlNetType -> String
controlNetTypeToString = case _ of
  CNDepth -> "depth"
  CNCanny -> "canny"
  CNLineart -> "lineart"
  CNSoftedge -> "softedge"
  CNNormal -> "normal"
  CNScribble -> "scribble"
  CNSeg -> "seg"
  CNPose -> "pose"

-- ────────────────────────────────────────────────────────────────────────────
-- Pose Output Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Pose output format options
data PoseOutputFormat
  = PoseImages
  | PoseJSON
  | PoseBoth

derive instance Eq PoseOutputFormat
derive instance Generic PoseOutputFormat _

instance Show PoseOutputFormat where
  show = genericShow

poseOutputFormatFromString :: String -> Maybe PoseOutputFormat
poseOutputFormatFromString = case _ of
  "images" -> Just PoseImages
  "json" -> Just PoseJSON
  "both" -> Just PoseBoth
  _ -> Nothing

poseOutputFormatToString :: PoseOutputFormat -> String
poseOutputFormatToString = case _ of
  PoseImages -> "images"
  PoseJSON -> "json"
  PoseBoth -> "both"

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | ControlNet export configuration
type ControlNetExportConfig =
  { controlNetType :: ControlNetType
  , resolution :: Int
  , thresholdLow :: Maybe Number
  , thresholdHigh :: Maybe Number
  , detectResolution :: Maybe Int
  }

-- | Pose export configuration
type PoseExportConfig =
  { width :: Int
  , height :: Int
  , startFrame :: Int
  , endFrame :: Int
  , boneWidth :: Number
  , keypointRadius :: Number
  , showKeypoints :: Boolean
  , showBones :: Boolean
  , useOpenPoseColors :: Boolean
  , outputFormat :: PoseOutputFormat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxThreshold :: Number
maxThreshold = 255.0

maxPoseKeypoints :: Int
maxPoseKeypoints = 1000

maxFaceKeypoints :: Int
maxFaceKeypoints = 1000

maxHandKeypoints :: Int
maxHandKeypoints = 500

maxPeoplePerFrame :: Int
maxPeoplePerFrame = 1000

maxBoneWidth :: Number
maxBoneWidth = 100.0

maxKeypointRadius :: Number
maxKeypointRadius = 100.0

maxOpenPoseVersion :: Int
maxOpenPoseVersion = 100
