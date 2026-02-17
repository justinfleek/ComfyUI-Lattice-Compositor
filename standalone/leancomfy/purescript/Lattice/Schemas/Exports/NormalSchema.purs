-- | Lattice.Schemas.Exports.NormalSchema - Normal map export format enums and types
-- |
-- | Normal map export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/normal-schema.ts

module Lattice.Schemas.Exports.NormalSchema
  ( -- Normal Generation Method
    NormalGenerationMethod(..)
  , normalGenerationMethodFromString
  , normalGenerationMethodToString
    -- Normal Depth Model
  , NormalDepthModel(..)
  , normalDepthModelFromString
  , normalDepthModelToString
    -- Generation Status
  , GenerationStatus(..)
  , generationStatusFromString
  , generationStatusToString
    -- Constants
  , maxDimension
    -- Structures
  , NormalGenerationOptions
  , NormalGenerationMetadata
  , NormalGenerationResult
    -- Validation
  , isValidMetadata
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Normal Generation Method
--------------------------------------------------------------------------------

-- | Normal generation method options
data NormalGenerationMethod
  = MethodAlgebraic
  | MethodNormalcrafter

derive instance Eq NormalGenerationMethod
derive instance Generic NormalGenerationMethod _

instance Show NormalGenerationMethod where
  show = genericShow

normalGenerationMethodFromString :: String -> Maybe NormalGenerationMethod
normalGenerationMethodFromString = case _ of
  "algebraic" -> Just MethodAlgebraic
  "normalcrafter" -> Just MethodNormalcrafter
  _ -> Nothing

normalGenerationMethodToString :: NormalGenerationMethod -> String
normalGenerationMethodToString = case _ of
  MethodAlgebraic -> "algebraic"
  MethodNormalcrafter -> "normalcrafter"

--------------------------------------------------------------------------------
-- Normal Depth Model
--------------------------------------------------------------------------------

-- | Normal depth model options
data NormalDepthModel
  = DA3_LARGE_1_1
  | DA3_GIANT_1_1
  | DA3NESTED_GIANT_LARGE_1_1

derive instance Eq NormalDepthModel
derive instance Generic NormalDepthModel _

instance Show NormalDepthModel where
  show = genericShow

normalDepthModelFromString :: String -> Maybe NormalDepthModel
normalDepthModelFromString = case _ of
  "DA3-LARGE-1.1" -> Just DA3_LARGE_1_1
  "DA3-GIANT-1.1" -> Just DA3_GIANT_1_1
  "DA3NESTED-GIANT-LARGE-1.1" -> Just DA3NESTED_GIANT_LARGE_1_1
  _ -> Nothing

normalDepthModelToString :: NormalDepthModel -> String
normalDepthModelToString = case _ of
  DA3_LARGE_1_1 -> "DA3-LARGE-1.1"
  DA3_GIANT_1_1 -> "DA3-GIANT-1.1"
  DA3NESTED_GIANT_LARGE_1_1 -> "DA3NESTED-GIANT-LARGE-1.1"

--------------------------------------------------------------------------------
-- Generation Status
--------------------------------------------------------------------------------

-- | Generation status options
data GenerationStatus
  = StatusSuccess
  | StatusError

derive instance Eq GenerationStatus
derive instance Generic GenerationStatus _

instance Show GenerationStatus where
  show = genericShow

generationStatusFromString :: String -> Maybe GenerationStatus
generationStatusFromString = case _ of
  "success" -> Just StatusSuccess
  "error" -> Just StatusError
  _ -> Nothing

generationStatusToString :: GenerationStatus -> String
generationStatusToString = case _ of
  StatusSuccess -> "success"
  StatusError -> "error"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxDimension :: Int
maxDimension = 16384

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Normal generation options
type NormalGenerationOptions =
  { method :: Maybe NormalGenerationMethod
  , depthModel :: Maybe NormalDepthModel
  }

-- | Normal generation metadata
type NormalGenerationMetadata =
  { method :: String
  , width :: Int
  , height :: Int
  }

-- | Normal generation result
type NormalGenerationResult =
  { status :: GenerationStatus
  , normal :: String        -- ^ Base64 encoded PNG (RGB normal map)
  , depth :: Maybe String   -- ^ Base64 depth map used (if generated)
  , fallback :: Maybe Boolean
  , message :: Maybe String
  , metadata :: Maybe NormalGenerationMetadata
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if metadata is valid
isValidMetadata :: NormalGenerationMetadata -> Boolean
isValidMetadata m =
  m.width > 0 && m.width <= maxDimension &&
  m.height > 0 && m.height <= maxDimension
