-- |
-- Module      : Lattice.State.LayerDefaults
-- Description : Pure state management functions for layer defaults
-- 
-- Migrated from ui/src/stores/actions/layer/layerDefaults.ts
-- Pure functions extracted - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.LayerDefaults
  ( -- Keypoint creation
    createDefaultTPoseKeypoints
  -- Types
  , Keypoint(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  )
import GHC.Generics (Generic)

-- ============================================================================
-- KEYPOINT
-- ============================================================================

-- | Keypoint with x, y coordinates and confidence
data Keypoint = Keypoint
  { keypointX :: Double
  , keypointY :: Double
  , keypointConfidence :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Keypoint where
  toJSON (Keypoint x y confidence) =
    object
      [ "x" .= x
      , "y" .= y
      , "confidence" .= confidence
      ]

instance FromJSON Keypoint where
  parseJSON = withObject "Keypoint" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    confidence <- o .: "confidence"
    return (Keypoint x y confidence)

-- ============================================================================
-- DEFAULT DATA CREATION FUNCTIONS
-- ============================================================================

-- | Create default T-pose keypoints for COCO 18-point format (normalized 0-1)
-- Pure function: returns constant array of 18 keypoints
createDefaultTPoseKeypoints :: [Keypoint]
createDefaultTPoseKeypoints =
  [ Keypoint 0.5 0.1 1.0 -- 0: nose
  , Keypoint 0.5 0.2 1.0 -- 1: neck
  , Keypoint 0.35 0.2 1.0 -- 2: right_shoulder
  , Keypoint 0.2 0.2 1.0 -- 3: right_elbow
  , Keypoint 0.1 0.2 1.0 -- 4: right_wrist
  , Keypoint 0.65 0.2 1.0 -- 5: left_shoulder
  , Keypoint 0.8 0.2 1.0 -- 6: left_elbow
  , Keypoint 0.9 0.2 1.0 -- 7: left_wrist
  , Keypoint 0.4 0.45 1.0 -- 8: right_hip
  , Keypoint 0.4 0.65 1.0 -- 9: right_knee
  , Keypoint 0.4 0.85 1.0 -- 10: right_ankle
  , Keypoint 0.6 0.45 1.0 -- 11: left_hip
  , Keypoint 0.6 0.65 1.0 -- 12: left_knee
  , Keypoint 0.6 0.85 1.0 -- 13: left_ankle
  , Keypoint 0.45 0.08 1.0 -- 14: right_eye
  , Keypoint 0.55 0.08 1.0 -- 15: left_eye
  , Keypoint 0.4 0.1 1.0 -- 16: right_ear
  , Keypoint 0.6 0.1 1.0 -- 17: left_ear
  ]
