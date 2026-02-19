-- | Lattice.Schemas.Presets.PresetsSchema - Preset system types
-- |
-- | Preset system enums for particles, effects, animations, etc.
-- |
-- | Source: ui/src/schemas/presets/presets-schema.ts

module Lattice.Schemas.Presets.PresetsSchema
  ( -- Preset Category
    PresetCategory(..)
  , presetCategoryFromString
  , presetCategoryToString
    -- Camera Shake Type
  , CameraShakeType(..)
  , cameraShakeTypeFromString
  , cameraShakeTypeToString
    -- Text Align
  , TextAlign(..)
  , textAlignFromString
  , textAlignToString
    -- Constants
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

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

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

derive instance Eq PresetCategory
derive instance Generic PresetCategory _

instance Show PresetCategory where
  show = genericShow

presetCategoryFromString :: String -> Maybe PresetCategory
presetCategoryFromString = case _ of
  "particle" -> Just PresetParticle
  "effect" -> Just PresetEffect
  "animation" -> Just PresetAnimation
  "camera-shake" -> Just PresetCameraShake
  "camera-trajectory" -> Just PresetCameraTrajectory
  "path-effect" -> Just PresetPathEffect
  "text-style" -> Just PresetTextStyle
  "color-palette" -> Just PresetColorPalette
  _ -> Nothing

presetCategoryToString :: PresetCategory -> String
presetCategoryToString = case _ of
  PresetParticle -> "particle"
  PresetEffect -> "effect"
  PresetAnimation -> "animation"
  PresetCameraShake -> "camera-shake"
  PresetCameraTrajectory -> "camera-trajectory"
  PresetPathEffect -> "path-effect"
  PresetTextStyle -> "text-style"
  PresetColorPalette -> "color-palette"

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

derive instance Eq CameraShakeType
derive instance Generic CameraShakeType _

instance Show CameraShakeType where
  show = genericShow

cameraShakeTypeFromString :: String -> Maybe CameraShakeType
cameraShakeTypeFromString = case _ of
  "handheld" -> Just ShakeHandheld
  "impact" -> Just ShakeImpact
  "earthquake" -> Just ShakeEarthquake
  "subtle" -> Just ShakeSubtle
  "custom" -> Just ShakeCustom
  _ -> Nothing

cameraShakeTypeToString :: CameraShakeType -> String
cameraShakeTypeToString = case _ of
  ShakeHandheld -> "handheld"
  ShakeImpact -> "impact"
  ShakeEarthquake -> "earthquake"
  ShakeSubtle -> "subtle"
  ShakeCustom -> "custom"

-- ────────────────────────────────────────────────────────────────────────────
-- Text Align
-- ────────────────────────────────────────────────────────────────────────────

-- | Text alignment options
data TextAlign
  = AlignLeft
  | AlignCenter
  | AlignRight
  | AlignJustify

derive instance Eq TextAlign
derive instance Generic TextAlign _

instance Show TextAlign where
  show = genericShow

textAlignFromString :: String -> Maybe TextAlign
textAlignFromString = case _ of
  "left" -> Just AlignLeft
  "center" -> Just AlignCenter
  "right" -> Just AlignRight
  "justify" -> Just AlignJustify
  _ -> Nothing

textAlignToString :: TextAlign -> String
textAlignToString = case _ of
  AlignLeft -> "left"
  AlignCenter -> "center"
  AlignRight -> "right"
  AlignJustify -> "justify"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxPresetVersion :: Int
maxPresetVersion = 1000

maxPresetsCount :: Int
maxPresetsCount = 10000

maxParticles :: Int
maxParticles = 10000000

maxGravity :: Number
maxGravity = 1000.0

maxEmissionRate :: Int
maxEmissionRate = 100000

maxLifespan :: Number
maxLifespan = 3600.0  -- 1 hour

maxShakeFrequency :: Number
maxShakeFrequency = 100.0

maxShakeFrames :: Int
maxShakeFrames = 100000

maxFontSize :: Number
maxFontSize = 1000.0

maxColorsCount :: Int
maxColorsCount = 1000

maxKeyframes :: Int
maxKeyframes = 100000
