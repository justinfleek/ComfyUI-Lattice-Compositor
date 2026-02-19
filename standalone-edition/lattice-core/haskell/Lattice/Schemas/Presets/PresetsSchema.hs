{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Presets.PresetsSchema
Description : Preset system types
Copyright   : (c) Lattice, 2026
License     : MIT

Preset system enums for particles, effects, animations, etc.

Source: ui/src/schemas/presets/presets-schema.ts
-}

module Lattice.Schemas.Presets.PresetsSchema
  ( -- * Preset Category
    PresetCategory(..)
  , presetCategoryFromText
  , presetCategoryToText
    -- * Camera Shake Type
  , CameraShakeType(..)
  , cameraShakeTypeFromText
  , cameraShakeTypeToText
    -- * Text Align
  , TextAlign(..)
  , textAlignFromText
  , textAlignToText
    -- * Constants
  , maxPresetVersion
  , maxPresetsCount
  , maxParticles
  , maxGravity
  , maxEmissionRate
  , maxLifespan
  , maxShakeFrequency
  , maxShakeFrames
  , maxFontSize
  , maxColorsCount
  , maxKeyframes
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Preset Category
-- ────────────────────────────────────────────────────────────────────────────

-- | Preset category options
data PresetCategory
  = PresetParticle
  | PresetEffect
  | PresetAnimation
  | PresetCameraShake
  | PresetCameraTrajectory
  | PresetPathEffect
  | PresetTextStyle
  | PresetColorPalette
  deriving stock (Eq, Show, Generic, Enum, Bounded)

presetCategoryFromText :: Text -> Maybe PresetCategory
presetCategoryFromText "particle" = Just PresetParticle
presetCategoryFromText "effect" = Just PresetEffect
presetCategoryFromText "animation" = Just PresetAnimation
presetCategoryFromText "camera-shake" = Just PresetCameraShake
presetCategoryFromText "camera-trajectory" = Just PresetCameraTrajectory
presetCategoryFromText "path-effect" = Just PresetPathEffect
presetCategoryFromText "text-style" = Just PresetTextStyle
presetCategoryFromText "color-palette" = Just PresetColorPalette
presetCategoryFromText _ = Nothing

presetCategoryToText :: PresetCategory -> Text
presetCategoryToText PresetParticle = "particle"
presetCategoryToText PresetEffect = "effect"
presetCategoryToText PresetAnimation = "animation"
presetCategoryToText PresetCameraShake = "camera-shake"
presetCategoryToText PresetCameraTrajectory = "camera-trajectory"
presetCategoryToText PresetPathEffect = "path-effect"
presetCategoryToText PresetTextStyle = "text-style"
presetCategoryToText PresetColorPalette = "color-palette"

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Shake Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera shake type options
data CameraShakeType
  = ShakeHandheld
  | ShakeImpact
  | ShakeEarthquake
  | ShakeSubtle
  | ShakeCustom
  deriving stock (Eq, Show, Generic, Enum, Bounded)

cameraShakeTypeFromText :: Text -> Maybe CameraShakeType
cameraShakeTypeFromText "handheld" = Just ShakeHandheld
cameraShakeTypeFromText "impact" = Just ShakeImpact
cameraShakeTypeFromText "earthquake" = Just ShakeEarthquake
cameraShakeTypeFromText "subtle" = Just ShakeSubtle
cameraShakeTypeFromText "custom" = Just ShakeCustom
cameraShakeTypeFromText _ = Nothing

cameraShakeTypeToText :: CameraShakeType -> Text
cameraShakeTypeToText ShakeHandheld = "handheld"
cameraShakeTypeToText ShakeImpact = "impact"
cameraShakeTypeToText ShakeEarthquake = "earthquake"
cameraShakeTypeToText ShakeSubtle = "subtle"
cameraShakeTypeToText ShakeCustom = "custom"

-- ────────────────────────────────────────────────────────────────────────────
-- Text Align
-- ────────────────────────────────────────────────────────────────────────────

-- | Text alignment options
data TextAlign
  = AlignLeft
  | AlignCenter
  | AlignRight
  | AlignJustify
  deriving stock (Eq, Show, Generic, Enum, Bounded)

textAlignFromText :: Text -> Maybe TextAlign
textAlignFromText "left" = Just AlignLeft
textAlignFromText "center" = Just AlignCenter
textAlignFromText "right" = Just AlignRight
textAlignFromText "justify" = Just AlignJustify
textAlignFromText _ = Nothing

textAlignToText :: TextAlign -> Text
textAlignToText AlignLeft = "left"
textAlignToText AlignCenter = "center"
textAlignToText AlignRight = "right"
textAlignToText AlignJustify = "justify"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxPresetVersion :: Int
maxPresetVersion = 1000

maxPresetsCount :: Int
maxPresetsCount = 10000

maxParticles :: Int
maxParticles = 10000000

maxGravity :: Double
maxGravity = 1000.0

maxEmissionRate :: Int
maxEmissionRate = 100000

maxLifespan :: Double
maxLifespan = 3600.0  -- 1 hour

maxShakeFrequency :: Double
maxShakeFrequency = 100.0

maxShakeFrames :: Int
maxShakeFrames = 100000

maxFontSize :: Double
maxFontSize = 1000.0

maxColorsCount :: Int
maxColorsCount = 1000

maxKeyframes :: Int
maxKeyframes = 100000
