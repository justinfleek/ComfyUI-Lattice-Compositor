-- | Lattice.Services.Export.BackendDepth - Backend depth/normal service
-- |
-- | Pure request types for calling depth estimation endpoints.
-- | All actual AI processing is done server-side via Bridge.
-- |
-- | Source: ui/src/services/export/backendDepthService.ts

module Lattice.Services.Export.BackendDepth
  ( -- * Types
    DepthModel(..)
  , NormalMethod(..)
  , DepthGenerationOptions
  , DepthGenerationResult
  , NormalGenerationOptions
  , NormalGenerationResult
  , DepthMetadata
  , NormalMetadata
  , AvailabilityResult
    -- * Request Types
  , DepthServiceRequest(..)
    -- * Request Builders
  , mkGenerateDepthRequest
  , mkGenerateNormalRequest
  , mkGenerateDepthAndNormalRequest
  , mkCheckAvailabilityRequest
    -- * Utilities
  , depthModelToString
  , normalMethodToString
  , base64ToDataUrl
    -- * Default Options
  , defaultDepthOptions
  , defaultNormalOptions
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth estimation model options
data DepthModel
  = DA3Large         -- DA3-LARGE-1.1
  | DA3Giant         -- DA3-GIANT-1.1
  | DA3NestedGiant   -- DA3NESTED-GIANT-LARGE-1.1

derive instance Generic DepthModel _
instance Show DepthModel where show = genericShow
instance Eq DepthModel where eq = genericEq
instance EncodeJson DepthModel where
  encodeJson = genericEncodeJson

-- | Normal map generation method
data NormalMethod
  = MethodAlgebraic    -- Algebraic normal computation from depth
  | MethodNormalCrafter -- NormalCrafter AI method

derive instance Generic NormalMethod _
instance Show NormalMethod where show = genericShow
instance Eq NormalMethod where eq = genericEq
instance EncodeJson NormalMethod where
  encodeJson = genericEncodeJson

-- | Depth generation options
type DepthGenerationOptions =
  { model :: DepthModel
  , returnConfidence :: Boolean
  , returnIntrinsics :: Boolean
  }

-- | Depth metadata
type DepthMetadata =
  { model :: String
  , width :: Int
  , height :: Int
  , depthMin :: Maybe Number
  , depthMax :: Maybe Number
  }

-- | Depth generation result
type DepthGenerationResult =
  { status :: String              -- "success" | "error"
  , depth :: String               -- base64 encoded PNG (grayscale)
  , confidence :: Maybe String    -- base64 encoded PNG (optional)
  , intrinsics :: Maybe (Array (Array Number))  -- Camera intrinsics matrix
  , fallback :: Boolean
  , message :: Maybe String
  , metadata :: Maybe DepthMetadata
  }

-- | Normal generation options
type NormalGenerationOptions =
  { method :: NormalMethod
  , depthModel :: DepthModel
  }

-- | Normal metadata
type NormalMetadata =
  { method :: String
  , width :: Int
  , height :: Int
  }

-- | Normal generation result
type NormalGenerationResult =
  { status :: String              -- "success" | "error"
  , normal :: String              -- base64 encoded PNG (RGB normal map)
  , depth :: Maybe String         -- base64 depth map used (if generated)
  , fallback :: Boolean
  , message :: Maybe String
  , metadata :: Maybe NormalMetadata
  }

-- | Availability check result
type AvailabilityResult =
  { depthAvailable :: Boolean
  , normalAvailable :: Boolean
  , fallbackOnly :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth service request - sent to Haskell backend
data DepthServiceRequest
  = GenerateDepthRequest
      { imageBase64 :: String
      , options :: DepthGenerationOptions
      }
  | GenerateNormalRequest
      { imageBase64 :: Maybe String
      , depthBase64 :: Maybe String
      , options :: NormalGenerationOptions
      }
  | GenerateDepthAndNormalRequest
      { imageBase64 :: String
      , depthOptions :: DepthGenerationOptions
      , normalOptions :: NormalGenerationOptions
      }
  | CheckAvailabilityRequest

derive instance Generic DepthServiceRequest _
instance Show DepthServiceRequest where show = genericShow
instance EncodeJson DepthServiceRequest where
  encodeJson = genericEncodeJson

-- ────────────────────────────────────────────────────────────────────────────
-- Request Builders
-- ────────────────────────────────────────────────────────────────────────────

-- | Create depth generation request
mkGenerateDepthRequest
  :: String
  -> DepthGenerationOptions
  -> DepthServiceRequest
mkGenerateDepthRequest imageBase64 options =
  GenerateDepthRequest { imageBase64, options }

-- | Create normal generation request
mkGenerateNormalRequest
  :: Maybe String
  -> Maybe String
  -> NormalGenerationOptions
  -> DepthServiceRequest
mkGenerateNormalRequest imageBase64 depthBase64 options =
  GenerateNormalRequest { imageBase64, depthBase64, options }

-- | Create combined depth and normal request
mkGenerateDepthAndNormalRequest
  :: String
  -> DepthGenerationOptions
  -> NormalGenerationOptions
  -> DepthServiceRequest
mkGenerateDepthAndNormalRequest imageBase64 depthOptions normalOptions =
  GenerateDepthAndNormalRequest { imageBase64, depthOptions, normalOptions }

-- | Create availability check request
mkCheckAvailabilityRequest :: DepthServiceRequest
mkCheckAvailabilityRequest = CheckAvailabilityRequest

-- ────────────────────────────────────────────────────────────────────────────
-- Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert depth model to string
depthModelToString :: DepthModel -> String
depthModelToString = case _ of
  DA3Large -> "da3-large"
  DA3Giant -> "da3-giant"
  DA3NestedGiant -> "da3-nested-giant"

-- | Convert normal method to string
normalMethodToString :: NormalMethod -> String
normalMethodToString = case _ of
  MethodAlgebraic -> "algebraic"
  MethodNormalCrafter -> "normalcrafter"

-- | Convert base64 string to data URL (pure function)
base64ToDataUrl :: String -> String -> String
base64ToDataUrl mimeType base64 =
  "data:" <> mimeType <> ";base64," <> base64

-- ────────────────────────────────────────────────────────────────────────────
-- Default Options
-- ────────────────────────────────────────────────────────────────────────────

-- | Default depth generation options
defaultDepthOptions :: DepthGenerationOptions
defaultDepthOptions =
  { model: DA3Large
  , returnConfidence: false
  , returnIntrinsics: false
  }

-- | Default normal generation options
defaultNormalOptions :: NormalGenerationOptions
defaultNormalOptions =
  { method: MethodAlgebraic
  , depthModel: DA3Large
  }
