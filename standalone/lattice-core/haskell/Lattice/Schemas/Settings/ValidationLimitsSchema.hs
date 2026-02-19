{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Settings.ValidationLimitsSchema
Description : Validation limits schema
Copyright   : (c) Lattice, 2026
License     : MIT

Validates validation limits stored in localStorage.

Source: lattice-core/lean/Lattice/Schemas/Settings/ValidationLimitsSchema.lean
-}

module Lattice.Schemas.Settings.ValidationLimitsSchema
  ( -- * Constants
    maxDimensionAbsolute
  , maxFrameCountAbsolute
  , maxArrayLengthAbsolute
  , maxParticlesAbsolute
  , maxLayersAbsolute
  , maxKeyframesAbsolute
  , maxStringLengthAbsolute
  , maxFpsAbsolute
    -- * Validation Limits
  , ValidationLimits(..)
  , defaultValidationLimits
    -- * Validation
  , validateValidationLimits
  , safeValidateValidationLimits
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T

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
data ValidationLimits = ValidationLimits
  { vlMaxDimension :: !Int
  , vlMaxDimensionAbsolute :: !Int
  , vlMaxFrameCount :: !Int
  , vlMaxFrameCountAbsolute :: !Int
  , vlMaxArrayLength :: !Int
  , vlMaxArrayLengthAbsolute :: !Int
  , vlMaxParticles :: !Int
  , vlMaxParticlesAbsolute :: !Int
  , vlMaxLayers :: !Int
  , vlMaxLayersAbsolute :: !Int
  , vlMaxKeyframesPerProperty :: !Int
  , vlMaxKeyframesPerPropertyAbsolute :: !Int
  , vlMaxStringLength :: !Int
  , vlMaxStringLengthAbsolute :: !Int
  , vlMaxFPS :: !Int
  , vlMaxFPSAbsolute :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Default validation limits
defaultValidationLimits :: ValidationLimits
defaultValidationLimits = ValidationLimits
  { vlMaxDimension = 8192
  , vlMaxDimensionAbsolute = maxDimensionAbsolute
  , vlMaxFrameCount = 10000
  , vlMaxFrameCountAbsolute = maxFrameCountAbsolute
  , vlMaxArrayLength = 100000
  , vlMaxArrayLengthAbsolute = maxArrayLengthAbsolute
  , vlMaxParticles = 1000000
  , vlMaxParticlesAbsolute = maxParticlesAbsolute
  , vlMaxLayers = 1000
  , vlMaxLayersAbsolute = maxLayersAbsolute
  , vlMaxKeyframesPerProperty = 10000
  , vlMaxKeyframesPerPropertyAbsolute = maxKeyframesAbsolute
  , vlMaxStringLength = 100000
  , vlMaxStringLengthAbsolute = maxStringLengthAbsolute
  , vlMaxFPS = 120
  , vlMaxFPSAbsolute = maxFpsAbsolute
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate that configurable limits don't exceed absolute limits
validateLimitsConstraint :: ValidationLimits -> Either ValidationError ()
validateLimitsConstraint vl
  | vlMaxDimension vl > vlMaxDimensionAbsolute vl =
      Left $ mkError "maxDimension" "must be <= maxDimensionAbsolute"
  | vlMaxFrameCount vl > vlMaxFrameCountAbsolute vl =
      Left $ mkError "maxFrameCount" "must be <= maxFrameCountAbsolute"
  | vlMaxArrayLength vl > vlMaxArrayLengthAbsolute vl =
      Left $ mkError "maxArrayLength" "must be <= maxArrayLengthAbsolute"
  | vlMaxParticles vl > vlMaxParticlesAbsolute vl =
      Left $ mkError "maxParticles" "must be <= maxParticlesAbsolute"
  | vlMaxLayers vl > vlMaxLayersAbsolute vl =
      Left $ mkError "maxLayers" "must be <= maxLayersAbsolute"
  | vlMaxKeyframesPerProperty vl > vlMaxKeyframesPerPropertyAbsolute vl =
      Left $ mkError "maxKeyframesPerProperty" "must be <= maxKeyframesPerPropertyAbsolute"
  | vlMaxStringLength vl > vlMaxStringLengthAbsolute vl =
      Left $ mkError "maxStringLength" "must be <= maxStringLengthAbsolute"
  | vlMaxFPS vl > vlMaxFPSAbsolute vl =
      Left $ mkError "maxFPS" "must be <= maxFPSAbsolute"
  | otherwise = Right ()

-- | Validate individual field values
validateFieldValues :: ValidationLimits -> Either ValidationError ()
validateFieldValues vl = do
  _ <- validatePositiveInt "maxDimension" maxDimensionAbsolute (vlMaxDimension vl)
  _ <- validatePositiveInt "maxDimensionAbsolute" maxDimensionAbsolute (vlMaxDimensionAbsolute vl)
  _ <- validatePositiveInt "maxFrameCount" maxFrameCountAbsolute (vlMaxFrameCount vl)
  _ <- validatePositiveInt "maxFrameCountAbsolute" maxFrameCountAbsolute (vlMaxFrameCountAbsolute vl)
  _ <- validatePositiveInt "maxArrayLength" maxArrayLengthAbsolute (vlMaxArrayLength vl)
  _ <- validatePositiveInt "maxArrayLengthAbsolute" maxArrayLengthAbsolute (vlMaxArrayLengthAbsolute vl)
  _ <- validatePositiveInt "maxParticles" maxParticlesAbsolute (vlMaxParticles vl)
  _ <- validatePositiveInt "maxParticlesAbsolute" maxParticlesAbsolute (vlMaxParticlesAbsolute vl)
  _ <- validatePositiveInt "maxLayers" maxLayersAbsolute (vlMaxLayers vl)
  _ <- validatePositiveInt "maxLayersAbsolute" maxLayersAbsolute (vlMaxLayersAbsolute vl)
  _ <- validatePositiveInt "maxKeyframesPerProperty" maxKeyframesAbsolute (vlMaxKeyframesPerProperty vl)
  _ <- validatePositiveInt "maxKeyframesPerPropertyAbsolute" maxKeyframesAbsolute (vlMaxKeyframesPerPropertyAbsolute vl)
  _ <- validatePositiveInt "maxStringLength" maxStringLengthAbsolute (vlMaxStringLength vl)
  _ <- validatePositiveInt "maxStringLengthAbsolute" maxStringLengthAbsolute (vlMaxStringLengthAbsolute vl)
  _ <- validatePositiveInt "maxFPS" maxFpsAbsolute (vlMaxFPS vl)
  _ <- validatePositiveInt "maxFPSAbsolute" maxFpsAbsolute (vlMaxFPSAbsolute vl)
  Right ()

-- | Full validation of ValidationLimits
validateValidationLimits :: ValidationLimits -> Either ValidationError ValidationLimits
validateValidationLimits vl = do
  validateFieldValues vl
  validateLimitsConstraint vl
  Right vl

-- | Safe validation (returns Maybe)
safeValidateValidationLimits :: ValidationLimits -> Maybe ValidationLimits
safeValidateValidationLimits vl =
  case validateValidationLimits vl of
    Right l -> Just l
    Left _ -> Nothing
