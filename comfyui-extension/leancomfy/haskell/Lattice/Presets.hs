{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Presets
Description : Preset System Types
Copyright   : (c) Lattice, 2026
License     : MIT

Defines types for saving and loading presets for particles, effects,
animations, and other configurable elements.

Source: ui/src/types/presets.ts (830 lines - mostly built-in data)
-}

module Lattice.Presets
  ( -- * Category
    PresetCategory(..)
    -- * Metadata
  , PresetMetadata(..)
    -- * Particle Preset
  , ParticlePresetConfig(..)
  , ParticlePreset(..)
    -- * Effect Preset
  , EffectParamValue(..)
  , PresetEffect(..)
  , EffectPreset(..)
    -- * Path Effect Preset
  , PathEffectInstance(..)
  , PathEffectPreset(..)
    -- * Camera Presets
  , CameraShakeConfig(..)
  , CameraShakePreset(..)
  , TrajectoryConfig(..)
  , CameraTrajectoryPreset(..)
    -- * Text Style Preset
  , TextAlign(..)
  , TextStyleConfig(..)
  , TextStylePreset(..)
    -- * Color Palette
  , ColorPalettePreset(..)
    -- * Animation Preset
  , PresetKeyframe(..)
  , PresetPropertyAnimation(..)
  , AnimationPreset(..)
    -- * Union and Collection
  , Preset(..)
  , PresetCollection(..)
  , presetMetadata
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Category
--------------------------------------------------------------------------------

data PresetCategory
  = PCParticle
  | PCEffect
  | PCAnimation
  | PCCameraShake
  | PCCameraTrajectory
  | PCPathEffect
  | PCTextStyle
  | PCColorPalette
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Metadata
--------------------------------------------------------------------------------

data PresetMetadata = PresetMetadata
  { pmId          :: !NonEmptyString
  , pmName        :: !NonEmptyString
  , pmCategory    :: !PresetCategory
  , pmDescription :: !(Maybe Text)
  , pmTags        :: !(Vector Text)
  , pmAuthor      :: !(Maybe Text)
  , pmCreatedAt   :: !Int  -- Unix timestamp
  , pmUpdatedAt   :: !Int  -- Unix timestamp
  , pmThumbnail   :: !(Maybe Text)  -- Base64 data URL
  , pmIsBuiltIn   :: !Bool
  , pmVersion     :: !(Maybe Int)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Particle Preset
--------------------------------------------------------------------------------

data ParticlePresetConfig = ParticlePresetConfig
  { ppcMaxParticles      :: !(Maybe Int)
  , ppcGravity           :: !(Maybe FiniteFloat)
  , ppcTurbulenceStrength :: !(Maybe FiniteFloat)
  , ppcEmissionRate      :: !(Maybe PositiveFloat)
  , ppcLifespan          :: !(Maybe PositiveFloat)
  , ppcStartSize         :: !(Maybe PositiveFloat)
  , ppcEndSize           :: !(Maybe NonNegativeFloat)
  , ppcStartColor        :: !(Maybe HexColor)
  , ppcEndColor          :: !(Maybe HexColor)
  , ppcVelocitySpread    :: !(Maybe FiniteFloat)
  } deriving stock (Eq, Show, Generic)

data ParticlePreset = ParticlePreset
  { ppMetadata :: !PresetMetadata
  , ppConfig   :: !ParticlePresetConfig
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Effect Preset
--------------------------------------------------------------------------------

data EffectParamValue
  = EPVNumber !Double
  | EPVString !Text
  | EPVBool !Bool
  | EPVColor !HexColor
  | EPVArray !(Vector EffectParamValue)
  deriving stock (Eq, Show, Generic)

data PresetEffect = PresetEffect
  { peEffectType :: !NonEmptyString
  , peParams     :: !(Vector (Text, EffectParamValue))
  } deriving stock (Eq, Show, Generic)

data EffectPreset = EffectPreset
  { epMetadata :: !PresetMetadata
  , epEffects  :: !(Vector PresetEffect)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Path Effect Preset
--------------------------------------------------------------------------------

data PathEffectInstance = PathEffectInstance
  { peiId         :: !NonEmptyString
  , peiEffectType :: !NonEmptyString
  , peiEnabled    :: !Bool
  , peiOrder      :: !Int
  , peiParams     :: !(Vector (Text, EffectParamValue))
  } deriving stock (Eq, Show, Generic)

data PathEffectPreset = PathEffectPreset
  { pepMetadata :: !PresetMetadata
  , pepEffects  :: !(Vector PathEffectInstance)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Camera Shake Preset
--------------------------------------------------------------------------------

data CameraShakeConfig = CameraShakeConfig
  { cscIntensity :: !(Maybe FiniteFloat)
  , cscFrequency :: !(Maybe PositiveFloat)
  , cscDecay     :: !(Maybe NonNegativeFloat)
  , cscOctaves   :: !(Maybe Int)
  , cscSeed      :: !(Maybe Int)
  } deriving stock (Eq, Show, Generic)

data CameraShakePreset = CameraShakePreset
  { cspMetadata :: !PresetMetadata
  , cspConfig   :: !CameraShakeConfig
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Camera Trajectory Preset
--------------------------------------------------------------------------------

data TrajectoryConfig = TrajectoryConfig
  { tcDuration :: !(Maybe PositiveFloat)
  , tcEasing   :: !(Maybe NonEmptyString)
  , tcLoopMode :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data CameraTrajectoryPreset = CameraTrajectoryPreset
  { ctpMetadata :: !PresetMetadata
  , ctpConfig   :: !TrajectoryConfig
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Text Style Preset
--------------------------------------------------------------------------------

data TextAlign = TALeft | TACenter | TARight
  deriving stock (Eq, Show, Generic)

data TextStyleConfig = TextStyleConfig
  { tscFontFamily    :: !(Maybe NonEmptyString)
  , tscFontSize      :: !(Maybe PositiveFloat)
  , tscFontWeight    :: !(Maybe Int)
  , tscFill          :: !(Maybe HexColor)
  , tscStroke        :: !(Maybe HexColor)
  , tscStrokeWidth   :: !(Maybe NonNegativeFloat)
  , tscLetterSpacing :: !(Maybe FiniteFloat)
  , tscLineHeight    :: !(Maybe PositiveFloat)
  , tscTextAlign     :: !(Maybe TextAlign)
  } deriving stock (Eq, Show, Generic)

data TextStylePreset = TextStylePreset
  { tspMetadata :: !PresetMetadata
  , tspStyle    :: !TextStyleConfig
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Color Palette Preset
--------------------------------------------------------------------------------

data ColorPalettePreset = ColorPalettePreset
  { cppMetadata :: !PresetMetadata
  , cppColors   :: !(Vector HexColor)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Animation Preset
--------------------------------------------------------------------------------

data PresetKeyframe = PresetKeyframe
  { pkFrame  :: !FrameNumber
  , pkValue  :: !EffectParamValue
  , pkEasing :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data PresetPropertyAnimation = PresetPropertyAnimation
  { ppaProperty  :: !NonEmptyString
  , ppaKeyframes :: !(Vector PresetKeyframe)
  } deriving stock (Eq, Show, Generic)

data AnimationPreset = AnimationPreset
  { apMetadata  :: !PresetMetadata
  , apKeyframes :: !(Vector PresetPropertyAnimation)
  , apDuration  :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Union and Collection
--------------------------------------------------------------------------------

data Preset
  = PParticle !ParticlePreset
  | PEffect !EffectPreset
  | PPathEffect !PathEffectPreset
  | PCameraShake !CameraShakePreset
  | PCameraTrajectory !CameraTrajectoryPreset
  | PTextStyle !TextStylePreset
  | PColorPalette !ColorPalettePreset
  | PAnimation !AnimationPreset
  deriving stock (Eq, Show, Generic)

-- | Get metadata from any preset
presetMetadata :: Preset -> PresetMetadata
presetMetadata (PParticle p)          = ppMetadata p
presetMetadata (PEffect e)            = epMetadata e
presetMetadata (PPathEffect pe)       = pepMetadata pe
presetMetadata (PCameraShake cs)      = cspMetadata cs
presetMetadata (PCameraTrajectory ct) = ctpMetadata ct
presetMetadata (PTextStyle ts)        = tspMetadata ts
presetMetadata (PColorPalette cp)     = cppMetadata cp
presetMetadata (PAnimation a)         = apMetadata a

data PresetCollection = PresetCollection
  { pcVersion    :: !Int
  , pcPresets    :: !(Vector Preset)
  , pcExportedAt :: !Int  -- Unix timestamp
  } deriving stock (Eq, Show, Generic)
