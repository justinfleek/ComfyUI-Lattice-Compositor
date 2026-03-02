{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.NormalSchema
Description : Normal map export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Normal map export format enums and types.

Source: ui/src/schemas/exports/normal-schema.ts
-}

module Lattice.Schemas.Exports.NormalSchema
  ( -- * Normal Generation Method
    NormalGenerationMethod(..)
  , normalGenerationMethodFromText
  , normalGenerationMethodToText
    -- * Normal Depth Model
  , NormalDepthModel(..)
  , normalDepthModelFromText
  , normalDepthModelToText
    -- * Generation Status
  , GenerationStatus(..)
  , generationStatusFromText
  , generationStatusToText
    -- * Constants
  , maxDimension
    -- * Structures
  , NormalGenerationOptions(..)
  , NormalGenerationMetadata(..)
  , NormalGenerationResult(..)
    -- * Validation
  , isValidMetadata
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Normal Generation Method
-- ────────────────────────────────────────────────────────────────────────────

-- | Normal generation method options
data NormalGenerationMethod
  = MethodAlgebraic
  | MethodNormalcrafter
  deriving stock (Eq, Show, Generic, Enum, Bounded)

normalGenerationMethodFromText :: Text -> Maybe NormalGenerationMethod
normalGenerationMethodFromText "algebraic" = Just MethodAlgebraic
normalGenerationMethodFromText "normalcrafter" = Just MethodNormalcrafter
normalGenerationMethodFromText _ = Nothing

normalGenerationMethodToText :: NormalGenerationMethod -> Text
normalGenerationMethodToText MethodAlgebraic = "algebraic"
normalGenerationMethodToText MethodNormalcrafter = "normalcrafter"

-- ────────────────────────────────────────────────────────────────────────────
-- Normal Depth Model
-- ────────────────────────────────────────────────────────────────────────────

-- | Normal depth model options
data NormalDepthModel
  = DA3_LARGE_1_1
  | DA3_GIANT_1_1
  | DA3NESTED_GIANT_LARGE_1_1
  deriving stock (Eq, Show, Generic, Enum, Bounded)

normalDepthModelFromText :: Text -> Maybe NormalDepthModel
normalDepthModelFromText "DA3-LARGE-1.1" = Just DA3_LARGE_1_1
normalDepthModelFromText "DA3-GIANT-1.1" = Just DA3_GIANT_1_1
normalDepthModelFromText "DA3NESTED-GIANT-LARGE-1.1" = Just DA3NESTED_GIANT_LARGE_1_1
normalDepthModelFromText _ = Nothing

normalDepthModelToText :: NormalDepthModel -> Text
normalDepthModelToText DA3_LARGE_1_1 = "DA3-LARGE-1.1"
normalDepthModelToText DA3_GIANT_1_1 = "DA3-GIANT-1.1"
normalDepthModelToText DA3NESTED_GIANT_LARGE_1_1 = "DA3NESTED-GIANT-LARGE-1.1"

-- ────────────────────────────────────────────────────────────────────────────
-- Generation Status
-- ────────────────────────────────────────────────────────────────────────────

-- | Generation status options
data GenerationStatus
  = StatusSuccess
  | StatusError
  deriving stock (Eq, Show, Generic, Enum, Bounded)

generationStatusFromText :: Text -> Maybe GenerationStatus
generationStatusFromText "success" = Just StatusSuccess
generationStatusFromText "error" = Just StatusError
generationStatusFromText _ = Nothing

generationStatusToText :: GenerationStatus -> Text
generationStatusToText StatusSuccess = "success"
generationStatusToText StatusError = "error"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxDimension :: Int
maxDimension = 16384

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Normal generation options
data NormalGenerationOptions = NormalGenerationOptions
  { ngoMethod :: !(Maybe NormalGenerationMethod)
  , ngoDepthModel :: !(Maybe NormalDepthModel)
  }
  deriving stock (Eq, Show, Generic)

-- | Normal generation metadata
data NormalGenerationMetadata = NormalGenerationMetadata
  { ngmMethod :: !Text
  , ngmWidth :: !Int
  , ngmHeight :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Normal generation result
data NormalGenerationResult = NormalGenerationResult
  { ngrStatus :: !GenerationStatus
  , ngrNormal :: !Text        -- ^ Base64 encoded PNG (RGB normal map)
  , ngrDepth :: !(Maybe Text) -- ^ Base64 depth map used (if generated)
  , ngrFallback :: !(Maybe Bool)
  , ngrMessage :: !(Maybe Text)
  , ngrMetadata :: !(Maybe NormalGenerationMetadata)
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if metadata is valid
isValidMetadata :: NormalGenerationMetadata -> Bool
isValidMetadata m =
  ngmWidth m > 0 && ngmWidth m <= maxDimension &&
  ngmHeight m > 0 && ngmHeight m <= maxDimension
