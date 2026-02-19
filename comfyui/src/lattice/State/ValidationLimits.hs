-- |
-- Module      : Lattice.State.ValidationLimits
-- Description : Pure validation limits functions
-- 
-- Migrated from ui/src/stores/validationLimitsStore.ts
-- Pure validation and constant functions extracted - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.ValidationLimits
  ( -- Pure constants
    getDefaultLimits
  -- Pure validation
  , validateLimit
  , clampLimit
  -- Types
  , ValidationLimits(..)
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

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Validation Limits
data ValidationLimits = ValidationLimits
  { validationLimitsMaxDimension :: Double
  , validationLimitsMaxDimensionAbsolute :: Double
  , validationLimitsMaxFrameCount :: Double
  , validationLimitsMaxFrameCountAbsolute :: Double
  , validationLimitsMaxArrayLength :: Double
  , validationLimitsMaxArrayLengthAbsolute :: Double
  , validationLimitsMaxParticles :: Double
  , validationLimitsMaxParticlesAbsolute :: Double
  , validationLimitsMaxLayers :: Double
  , validationLimitsMaxLayersAbsolute :: Double
  , validationLimitsMaxKeyframesPerProperty :: Double
  , validationLimitsMaxKeyframesPerPropertyAbsolute :: Double
  , validationLimitsMaxStringLength :: Double
  , validationLimitsMaxStringLengthAbsolute :: Double
  , validationLimitsMaxFPS :: Double
  , validationLimitsMaxFPSAbsolute :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON ValidationLimits where
  toJSON (ValidationLimits maxDim maxDimAbs maxFrames maxFramesAbs maxArray maxArrayAbs maxParts maxPartsAbs maxLayers maxLayersAbs maxKeyframes maxKeyframesAbs maxString maxStringAbs maxFps maxFpsAbs) =
    object
      [ "maxDimension" .= maxDim
      , "maxDimensionAbsolute" .= maxDimAbs
      , "maxFrameCount" .= maxFrames
      , "maxFrameCountAbsolute" .= maxFramesAbs
      , "maxArrayLength" .= maxArray
      , "maxArrayLengthAbsolute" .= maxArrayAbs
      , "maxParticles" .= maxParts
      , "maxParticlesAbsolute" .= maxPartsAbs
      , "maxLayers" .= maxLayers
      , "maxLayersAbsolute" .= maxLayersAbs
      , "maxKeyframesPerProperty" .= maxKeyframes
      , "maxKeyframesPerPropertyAbsolute" .= maxKeyframesAbs
      , "maxStringLength" .= maxString
      , "maxStringLengthAbsolute" .= maxStringAbs
      , "maxFPS" .= maxFps
      , "maxFPSAbsolute" .= maxFpsAbs
      ]

instance FromJSON ValidationLimits where
  parseJSON = withObject "ValidationLimits" $ \o ->
    ValidationLimits
      <$> o .: "maxDimension"
      <*> o .: "maxDimensionAbsolute"
      <*> o .: "maxFrameCount"
      <*> o .: "maxFrameCountAbsolute"
      <*> o .: "maxArrayLength"
      <*> o .: "maxArrayLengthAbsolute"
      <*> o .: "maxParticles"
      <*> o .: "maxParticlesAbsolute"
      <*> o .: "maxLayers"
      <*> o .: "maxLayersAbsolute"
      <*> o .: "maxKeyframesPerProperty"
      <*> o .: "maxKeyframesPerPropertyAbsolute"
      <*> o .: "maxStringLength"
      <*> o .: "maxStringLengthAbsolute"
      <*> o .: "maxFPS"
      <*> o .: "maxFPSAbsolute"

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // pure // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Get default validation limits
-- Pure function: returns default limits constant
getDefaultLimits ::
  ValidationLimits
getDefaultLimits =
  ValidationLimits
    { validationLimitsMaxDimension = 8192.0
    , validationLimitsMaxDimensionAbsolute = 16384.0
    , validationLimitsMaxFrameCount = 10000.0
    , validationLimitsMaxFrameCountAbsolute = 50000.0
    , validationLimitsMaxArrayLength = 100000.0
    , validationLimitsMaxArrayLengthAbsolute = 1000000.0
    , validationLimitsMaxParticles = 1000000.0
    , validationLimitsMaxParticlesAbsolute = 10000000.0
    , validationLimitsMaxLayers = 1000.0
    , validationLimitsMaxLayersAbsolute = 5000.0
    , validationLimitsMaxKeyframesPerProperty = 10000.0
    , validationLimitsMaxKeyframesPerPropertyAbsolute = 50000.0
    , validationLimitsMaxStringLength = 100000.0
    , validationLimitsMaxStringLengthAbsolute = 1000000.0
    , validationLimitsMaxFPS = 120.0
    , validationLimitsMaxFPSAbsolute = 240.0
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // pure // validation
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate a limit value against absolute maximum
-- Pure function: takes limit value and absolute maximum, returns boolean
validateLimit ::
  Double ->
  Double ->
  Bool
validateLimit limitValue absoluteMax =
  limitValue >= 0.0 && limitValue <= absoluteMax

-- | Clamp a limit value to valid range [0, absoluteMax]
-- Pure function: takes limit value and absolute maximum, returns clamped value
clampLimit ::
  Double ->
  Double ->
  Double
clampLimit limitValue absoluteMax =
  if limitValue < 0.0
    then 0.0
    else if limitValue > absoluteMax
      then absoluteMax
      else limitValue
