-- | Lattice.Presets - Preset System Types
-- |
-- | Source: ui/src/types/presets.ts (830 lines - mostly built-in data)
-- |
-- | Defines types for saving and loading presets for particles, effects,
-- | animations, and other configurable elements.

module Lattice.Presets
  ( PresetCategory(..)
  , PresetMetadata
  , ParticlePresetConfig
  , ParticlePreset
  , EffectParamValue(..)
  , PresetEffect
  , EffectPreset
  , PathEffectInstance
  , PathEffectPreset
  , CameraShakeConfig
  , CameraShakePreset
  , TrajectoryConfig
  , CameraTrajectoryPreset
  , TextAlign(..)
  , TextStyleConfig
  , TextStylePreset
  , ColorPalettePreset
  , PresetKeyframe
  , PresetPropertyAnimation
  , AnimationPreset
  , Preset(..)
  , PresetCollection
  , presetMetadata
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

-- ────────────────────────────────────────────────────────────────────────────
-- Category
-- ────────────────────────────────────────────────────────────────────────────

data PresetCategory
  = PCParticle
  | PCEffect
  | PCAnimation
  | PCCameraShake
  | PCCameraTrajectory
  | PCPathEffect
  | PCTextStyle
  | PCColorPalette

derive instance Eq PresetCategory
derive instance Generic PresetCategory _
instance Show PresetCategory where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Metadata
-- ────────────────────────────────────────────────────────────────────────────

type PresetMetadata =
  { id          :: NonEmptyString
  , name        :: NonEmptyString
  , category    :: PresetCategory
  , description :: Maybe String
  , tags        :: Array String
  , author      :: Maybe String
  , createdAt   :: Int  -- Unix timestamp
  , updatedAt   :: Int  -- Unix timestamp
  , thumbnail   :: Maybe String  -- Base64 data URL
  , isBuiltIn   :: Boolean
  , version     :: Maybe Int
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Particle Preset
-- ────────────────────────────────────────────────────────────────────────────

type ParticlePresetConfig =
  { maxParticles      :: Maybe Int
  , gravity           :: Maybe FiniteFloat
  , turbulenceStrength :: Maybe FiniteFloat
  , emissionRate      :: Maybe PositiveFloat
  , lifespan          :: Maybe PositiveFloat
  , startSize         :: Maybe PositiveFloat
  , endSize           :: Maybe NonNegativeFloat
  , startColor        :: Maybe HexColor
  , endColor          :: Maybe HexColor
  , velocitySpread    :: Maybe FiniteFloat
  }

type ParticlePreset =
  { metadata :: PresetMetadata
  , config   :: ParticlePresetConfig
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Effect Preset
-- ────────────────────────────────────────────────────────────────────────────

data EffectParamValue
  = EPVNumber Number
  | EPVString String
  | EPVBool Boolean
  | EPVColor HexColor
  | EPVArray (Array EffectParamValue)

derive instance Eq EffectParamValue
derive instance Generic EffectParamValue _
instance Show EffectParamValue where
  show (EPVNumber n) = "(EPVNumber " <> show n <> ")"
  show (EPVString s) = "(EPVString " <> show s <> ")"
  show (EPVBool b) = "(EPVBool " <> show b <> ")"
  show (EPVColor c) = "(EPVColor " <> show c <> ")"
  show (EPVArray arr) = "(EPVArray " <> show arr <> ")"

type PresetEffect =
  { effectType :: NonEmptyString
  , params     :: Array { key :: String, value :: EffectParamValue }
  }

type EffectPreset =
  { metadata :: PresetMetadata
  , effects  :: Array PresetEffect
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Path Effect Preset
-- ────────────────────────────────────────────────────────────────────────────

type PathEffectInstance =
  { id         :: NonEmptyString
  , effectType :: NonEmptyString
  , enabled    :: Boolean
  , order      :: Int
  , params     :: Array { key :: String, value :: EffectParamValue }
  }

type PathEffectPreset =
  { metadata :: PresetMetadata
  , effects  :: Array PathEffectInstance
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Shake Preset
-- ────────────────────────────────────────────────────────────────────────────

type CameraShakeConfig =
  { intensity :: Maybe FiniteFloat
  , frequency :: Maybe PositiveFloat
  , decay     :: Maybe NonNegativeFloat
  , octaves   :: Maybe Int
  , seed      :: Maybe Int
  }

type CameraShakePreset =
  { metadata :: PresetMetadata
  , config   :: CameraShakeConfig
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Trajectory Preset
-- ────────────────────────────────────────────────────────────────────────────

type TrajectoryConfig =
  { duration :: Maybe PositiveFloat
  , easing   :: Maybe NonEmptyString
  , loopMode :: Maybe NonEmptyString
  }

type CameraTrajectoryPreset =
  { metadata :: PresetMetadata
  , config   :: TrajectoryConfig
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Text Style Preset
-- ────────────────────────────────────────────────────────────────────────────

data TextAlign = TALeft | TACenter | TARight

derive instance Eq TextAlign
derive instance Generic TextAlign _
instance Show TextAlign where show = genericShow

type TextStyleConfig =
  { fontFamily    :: Maybe NonEmptyString
  , fontSize      :: Maybe PositiveFloat
  , fontWeight    :: Maybe Int
  , fill          :: Maybe HexColor
  , stroke        :: Maybe HexColor
  , strokeWidth   :: Maybe NonNegativeFloat
  , letterSpacing :: Maybe FiniteFloat
  , lineHeight    :: Maybe PositiveFloat
  , textAlign     :: Maybe TextAlign
  }

type TextStylePreset =
  { metadata :: PresetMetadata
  , style    :: TextStyleConfig
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Color Palette Preset
-- ────────────────────────────────────────────────────────────────────────────

type ColorPalettePreset =
  { metadata :: PresetMetadata
  , colors   :: Array HexColor
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Animation Preset
-- ────────────────────────────────────────────────────────────────────────────

type PresetKeyframe =
  { frame  :: FrameNumber
  , value  :: EffectParamValue
  , easing :: Maybe NonEmptyString
  }

type PresetPropertyAnimation =
  { property  :: NonEmptyString
  , keyframes :: Array PresetKeyframe
  }

type AnimationPreset =
  { metadata  :: PresetMetadata
  , keyframes :: Array PresetPropertyAnimation
  , duration  :: FrameNumber
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Union and Collection
-- ────────────────────────────────────────────────────────────────────────────

data Preset
  = PParticle ParticlePreset
  | PEffect EffectPreset
  | PPathEffect PathEffectPreset
  | PCameraShake CameraShakePreset
  | PCameraTrajectory CameraTrajectoryPreset
  | PTextStyle TextStylePreset
  | PColorPalette ColorPalettePreset
  | PAnimation AnimationPreset

derive instance Generic Preset _
instance Show Preset where show = genericShow

-- | Get metadata from any preset
presetMetadata :: Preset -> PresetMetadata
presetMetadata (PParticle p)          = p.metadata
presetMetadata (PEffect e)            = e.metadata
presetMetadata (PPathEffect pe)       = pe.metadata
presetMetadata (PCameraShake cs)      = cs.metadata
presetMetadata (PCameraTrajectory ct) = ct.metadata
presetMetadata (PTextStyle ts)        = ts.metadata
presetMetadata (PColorPalette cp)     = cp.metadata
presetMetadata (PAnimation a)         = a.metadata

type PresetCollection =
  { version    :: Int
  , presets    :: Array Preset
  , exportedAt :: Int  -- Unix timestamp
  }
