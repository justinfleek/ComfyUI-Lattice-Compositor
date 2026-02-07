-- |
-- Module      : Lattice.State.Effect
-- Description : Pure state management functions for effect store
-- 
-- Migrated from ui/src/stores/effectStore/index.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Effect
  ( -- Query functions
    hasStylesInClipboard
  , getStylesFromClipboard
  , getStylePresetNames
  -- Types
  , StylePresetName(..)
  ) where

import Data.Aeson (Value)
import Data.Maybe (Maybe)
import Data.Text (Text)
import qualified Data.Text as T

-- ============================================================================
-- STYLE PRESET NAMES
-- ============================================================================

-- | Style preset name enumeration
data StylePresetName
  = StylePresetSoftShadow
  | StylePresetHardShadow
  | StylePresetNeonGlow
  | StylePresetSimpleStroke
  | StylePresetEmbossed
  | StylePresetInnerBevel
  | StylePresetPillowEmboss
  deriving (Eq, Show)

-- | Convert StylePresetName to Text
stylePresetNameToText :: StylePresetName -> Text
stylePresetNameToText StylePresetSoftShadow = "soft-shadow"
stylePresetNameToText StylePresetHardShadow = "hard-shadow"
stylePresetNameToText StylePresetNeonGlow = "neon-glow"
stylePresetNameToText StylePresetSimpleStroke = "simple-stroke"
stylePresetNameToText StylePresetEmbossed = "embossed"
stylePresetNameToText StylePresetInnerBevel = "inner-bevel"
stylePresetNameToText StylePresetPillowEmboss = "pillow-emboss"

-- ============================================================================
-- QUERY FUNCTIONS
-- ============================================================================

-- | Check if styles clipboard has content
-- Pure function: takes clipboard styles, returns Bool
hasStylesInClipboard :: Maybe Value -> Bool
hasStylesInClipboard mClipboard =
  case mClipboard of
    Nothing -> False
    Just _ -> True

-- | Get styles from clipboard
-- Pure function: takes clipboard styles, returns them
getStylesFromClipboard :: Maybe Value -> Maybe Value
getStylesFromClipboard mClipboard = mClipboard

-- | Get list of available style preset names
-- Pure function: returns list of preset names
getStylePresetNames :: [Text]
getStylePresetNames =
  [ stylePresetNameToText StylePresetSoftShadow
  , stylePresetNameToText StylePresetHardShadow
  , stylePresetNameToText StylePresetNeonGlow
  , stylePresetNameToText StylePresetSimpleStroke
  , stylePresetNameToText StylePresetEmbossed
  , stylePresetNameToText StylePresetInnerBevel
  , stylePresetNameToText StylePresetPillowEmboss
  ]
