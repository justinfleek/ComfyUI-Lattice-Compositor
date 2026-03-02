-- | Lattice.Schemas.Settings.ValidationLimitsSchema - Validation limits schema
-- |
-- | Validates validation limits stored in localStorage.
-- |
-- | Source: leancomfy/lean/Lattice/Schemas/Settings/ValidationLimitsSchema.lean

module Lattice.Schemas.Settings.ValidationLimitsSchema
  ( -- Constants
    maxDimensionAbsolute
  , maxFrameCountAbsolute
  , maxArrayLengthAbsolute
  , maxParticlesAbsolute
  , maxLayersAbsolute
  , maxKeyframesAbsolute
  , maxStringLengthAbsolute
  , maxFpsAbsolute
    -- Validation Limits
  , ValidationLimits
  , defaultValidationLimits
    -- Validation
  , validateValidationLimits
  , safeValidateValidationLimits
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError, validatePositiveInt )

--------------------------------------------------------------------------------
-- Absolute Maximums (Security Critical)
--------------------------------------------------------------------------------

maxDimensionAbsolute :: Int
maxDimensionAbsolute = 16384

maxFrameCountAbsolute :: Int
maxFrameCountAbsolute = 100000

maxArrayLengthAbsolute :: Int
maxArrayLengthAbsolute = 1000000

maxParticlesAbsolute :: Int
maxParticlesAbsolute = 10000000

maxLayersAbsolute :: Int
maxLayersAbsolute = 10000

maxKeyframesAbsolute :: Int
maxKeyframesAbsolute = 100000

maxStringLengthAbsolute :: Int
maxStringLengthAbsolute = 1000000

maxFpsAbsolute :: Int
maxFpsAbsolute = 120

--------------------------------------------------------------------------------
-- Validation Limits
--------------------------------------------------------------------------------

-- | Validation limits with configurable and absolute values
type ValidationLimits =
  { maxDimension :: Int
  , maxDimensionAbsolute :: Int
  , maxFrameCount :: Int
  , maxFrameCountAbsolute :: Int
  , maxArrayLength :: Int
  , maxArrayLengthAbsolute :: Int
  , maxParticles :: Int
  , maxParticlesAbsolute :: Int
  , maxLayers :: Int
  , maxLayersAbsolute :: Int
  , maxKeyframesPerProperty :: Int
  , maxKeyframesPerPropertyAbsolute :: Int
  , maxStringLength :: Int
  , maxStringLengthAbsolute :: Int
  , maxFPS :: Int
  , maxFPSAbsolute :: Int
  }

-- | Default validation limits
defaultValidationLimits :: ValidationLimits
defaultValidationLimits =
  { maxDimension: 8192
  , maxDimensionAbsolute: maxDimensionAbsolute
  , maxFrameCount: 10000
  , maxFrameCountAbsolute: maxFrameCountAbsolute
  , maxArrayLength: 100000
  , maxArrayLengthAbsolute: maxArrayLengthAbsolute
  , maxParticles: 1000000
  , maxParticlesAbsolute: maxParticlesAbsolute
  , maxLayers: 1000
  , maxLayersAbsolute: maxLayersAbsolute
  , maxKeyframesPerProperty: 10000
  , maxKeyframesPerPropertyAbsolute: maxKeyframesAbsolute
  , maxStringLength: 100000
  , maxStringLengthAbsolute: maxStringLengthAbsolute
  , maxFPS: 120
  , maxFPSAbsolute: maxFpsAbsolute
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate that configurable limits don't exceed absolute limits
validateLimitsConstraint :: ValidationLimits -> Either ValidationError Unit
validateLimitsConstraint vl
  | vl.maxDimension > vl.maxDimensionAbsolute =
      Left $ mkError "maxDimension" "must be <= maxDimensionAbsolute"
  | vl.maxFrameCount > vl.maxFrameCountAbsolute =
      Left $ mkError "maxFrameCount" "must be <= maxFrameCountAbsolute"
  | vl.maxArrayLength > vl.maxArrayLengthAbsolute =
      Left $ mkError "maxArrayLength" "must be <= maxArrayLengthAbsolute"
  | vl.maxParticles > vl.maxParticlesAbsolute =
      Left $ mkError "maxParticles" "must be <= maxParticlesAbsolute"
  | vl.maxLayers > vl.maxLayersAbsolute =
      Left $ mkError "maxLayers" "must be <= maxLayersAbsolute"
  | vl.maxKeyframesPerProperty > vl.maxKeyframesPerPropertyAbsolute =
      Left $ mkError "maxKeyframesPerProperty" "must be <= maxKeyframesPerPropertyAbsolute"
  | vl.maxStringLength > vl.maxStringLengthAbsolute =
      Left $ mkError "maxStringLength" "must be <= maxStringLengthAbsolute"
  | vl.maxFPS > vl.maxFPSAbsolute =
      Left $ mkError "maxFPS" "must be <= maxFPSAbsolute"
  | otherwise = Right unit

-- | Validate individual field values
validateFieldValues :: ValidationLimits -> Either ValidationError Unit
validateFieldValues vl = do
  _ <- validatePositiveInt "maxDimension" maxDimensionAbsolute vl.maxDimension
  _ <- validatePositiveInt "maxDimensionAbsolute" maxDimensionAbsolute vl.maxDimensionAbsolute
  _ <- validatePositiveInt "maxFrameCount" maxFrameCountAbsolute vl.maxFrameCount
  _ <- validatePositiveInt "maxFrameCountAbsolute" maxFrameCountAbsolute vl.maxFrameCountAbsolute
  _ <- validatePositiveInt "maxArrayLength" maxArrayLengthAbsolute vl.maxArrayLength
  _ <- validatePositiveInt "maxArrayLengthAbsolute" maxArrayLengthAbsolute vl.maxArrayLengthAbsolute
  _ <- validatePositiveInt "maxParticles" maxParticlesAbsolute vl.maxParticles
  _ <- validatePositiveInt "maxParticlesAbsolute" maxParticlesAbsolute vl.maxParticlesAbsolute
  _ <- validatePositiveInt "maxLayers" maxLayersAbsolute vl.maxLayers
  _ <- validatePositiveInt "maxLayersAbsolute" maxLayersAbsolute vl.maxLayersAbsolute
  _ <- validatePositiveInt "maxKeyframesPerProperty" maxKeyframesAbsolute vl.maxKeyframesPerProperty
  _ <- validatePositiveInt "maxKeyframesPerPropertyAbsolute" maxKeyframesAbsolute vl.maxKeyframesPerPropertyAbsolute
  _ <- validatePositiveInt "maxStringLength" maxStringLengthAbsolute vl.maxStringLength
  _ <- validatePositiveInt "maxStringLengthAbsolute" maxStringLengthAbsolute vl.maxStringLengthAbsolute
  _ <- validatePositiveInt "maxFPS" maxFpsAbsolute vl.maxFPS
  _ <- validatePositiveInt "maxFPSAbsolute" maxFpsAbsolute vl.maxFPSAbsolute
  pure unit

-- | Full validation of ValidationLimits
validateValidationLimits :: ValidationLimits -> Either ValidationError ValidationLimits
validateValidationLimits vl = do
  validateFieldValues vl
  validateLimitsConstraint vl
  pure vl

-- | Safe validation (returns Maybe)
safeValidateValidationLimits :: ValidationLimits -> Maybe ValidationLimits
safeValidateValidationLimits vl =
  case validateValidationLimits vl of
    Right l -> Just l
    Left _ -> Nothing
