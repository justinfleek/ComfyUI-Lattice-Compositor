-- | Lattice.Services.Video.FrameInterpolation - Frame interpolation service
-- |
-- | @module Lattice.Services.Video.FrameInterpolation
-- | @description RIFE-based frame interpolation for video processing.
-- |
-- | ## Architecture
-- |
-- | This module provides frame interpolation via pure request types that are
-- | sent to the Haskell backend via Bridge. There is ZERO JavaScript FFI.
-- |
-- | Request types:
-- | 1. **GetModelsRequest** - Request available models from server
-- | 2. **PairInterpolationRequest** - Interpolate two frames
-- | 3. **SequenceInterpolationRequest** - Interpolate a sequence
-- | 4. **SlowMoRequest** - Create slow motion effect
-- | 5. **BlendFramesRequest** - Client-side fallback blending
-- | 6. **FrameConversionRequest** - Convert frame formats
-- |
-- | ## Configuration
-- |
-- | The API endpoint is passed explicitly via request types.
-- | There is NO global mutable state. This is a pure functional API.
-- |
-- | ## Banned Constructs
-- |
-- | This module contains ZERO:
-- | - foreign import (ELIMINATED)
-- | - unsafePerformEffect (BANNED)
-- | - unsafePartial (BANNED)
-- | - unsafeCoerce (BANNED)
-- | - Global mutable state (BANNED)
-- |
-- | Source: ui/src/services/video/frameInterpolation.ts (service section)

module Lattice.Services.Video.FrameInterpolation
  ( -- * Types
    ApiEndpoint
  , InterpolationConfig
    -- * Request Types (Pure - for Bridge)
  , GetModelsRequest
  , PairInterpolationBridgeRequest
  , SequenceInterpolationBridgeRequest
  , SlowMoBridgeRequest
  , BlendFramesRequest
  , FrameConversionRequest(..)
    -- * Request Builders (Pure)
  , mkGetModelsRequest
  , mkPairInterpolationRequest
  , mkSequenceInterpolationRequest
  , mkSlowMoRequest
  , mkBlendFramesRequest
  , mkFrameToBase64Request
  , mkBase64ToImageDataRequest
  , mkBase64ToBlobRequest
  , mkClientInterpolationRequest
    -- * Pure Utilities
  , calculateRequiredFrames
  , clampNumber
  , calculateBlendRatios
  , calculateInterpolationTimestamps
  ) where

import Prelude
import Data.Array ((..), mapWithIndex)
import Data.Int (toNumber, floor)

import Lattice.Services.Video.Types
  ( RIFEModel
  , InterpolationFactor
  , InterpolationRequest
  , SequenceRequest
  , SlowMoRequest
  , rifeModelToString
  , factorToInt
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | API endpoint URL (newtype for type safety)
-- |
-- | @constraint Must be a valid URL path starting with "/"
-- | @example "/api/interpolation"
type ApiEndpoint = String

-- | Configuration for interpolation operations
-- |
-- | @field endpoint The API endpoint URL
-- | @field defaultFormat Image format for output ("image/png" or "image/jpeg")
-- | @field defaultQuality Quality for JPEG output (0.0 to 1.0)
type InterpolationConfig =
  { endpoint :: ApiEndpoint
  , defaultFormat :: String
  , defaultQuality :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Types (Pure - for Bridge to Haskell backend)
-- ────────────────────────────────────────────────────────────────────────────

-- | Request to fetch available interpolation models
type GetModelsRequest =
  { url :: String  -- Full API URL for models endpoint
  }

-- | Request to interpolate a pair of frames via API
type PairInterpolationBridgeRequest =
  { url :: String           -- API endpoint URL
  , frame1 :: String        -- Base64-encoded first frame
  , frame2 :: String        -- Base64-encoded second frame
  , model :: String         -- RIFE model identifier string
  , factor :: Int           -- Interpolation factor (2, 4, 8, etc.)
  , ensemble :: Boolean     -- Use ensemble mode for higher quality
  , fastMode :: Boolean     -- Use fast mode (lower quality, faster)
  }

-- | Request to interpolate a sequence of frames
type SequenceInterpolationBridgeRequest =
  { url :: String           -- API endpoint URL
  , frames :: Array String  -- Base64-encoded frames
  , model :: String         -- RIFE model identifier
  , factor :: Int           -- Interpolation factor
  , ensemble :: Boolean     -- Ensemble mode
  , fastMode :: Boolean     -- Fast mode
  , preserveOriginal :: Boolean  -- Keep original frames in output
  }

-- | Request to create slow motion effect
type SlowMoBridgeRequest =
  { url :: String           -- API endpoint URL
  , frames :: Array String  -- Base64-encoded frames
  , model :: String         -- RIFE model identifier
  , slowdownFactor :: Number  -- Slowdown multiplier
  , targetFps :: Number     -- Target frame rate
  , sourceFps :: Number     -- Source frame rate
  , ensemble :: Boolean     -- Ensemble mode
  , fastMode :: Boolean     -- Fast mode
  }

-- | Request to blend two frames (client-side fallback)
type BlendFramesRequest =
  { frame1 :: String        -- Base64-encoded first frame
  , frame2 :: String        -- Base64-encoded second frame
  , ratio :: Number         -- Blend ratio (0.0 = frame1, 1.0 = frame2)
  }

-- | Frame conversion requests
data FrameConversionRequest
  = FrameToBase64Request
      { elementId :: String   -- DOM element ID
      , format :: String      -- "image/png" or "image/jpeg"
      , quality :: Number     -- Quality for JPEG (0.0 to 1.0)
      }
  | Base64ToImageDataRequest
      { base64 :: String      -- Base64-encoded image
      }
  | Base64ToBlobRequest
      { base64 :: String      -- Base64-encoded data
      , mimeType :: String    -- MIME type (e.g., "image/png")
      }
  | ClientInterpolationRequest
      { frame1 :: String      -- Base64-encoded first frame
      , frame2 :: String      -- Base64-encoded second frame
      , count :: Int          -- Number of intermediate frames
      }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Builders (Pure Functions)
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a request to fetch available models
-- |
-- | @param endpoint The API endpoint (e.g., "/api/interpolation")
-- | @returns Request that can be sent via Bridge
mkGetModelsRequest :: ApiEndpoint -> GetModelsRequest
mkGetModelsRequest endpoint =
  { url: endpoint <> "/models"
  }

-- | Create a pair interpolation request
-- |
-- | @param endpoint The API endpoint
-- | @param req Interpolation request containing frames and settings
-- | @returns Request that can be sent via Bridge
mkPairInterpolationRequest :: ApiEndpoint -> InterpolationRequest -> PairInterpolationBridgeRequest
mkPairInterpolationRequest endpoint req =
  { url: endpoint <> "/pair"
  , frame1: req.frame1
  , frame2: req.frame2
  , model: rifeModelToString req.model
  , factor: factorToInt req.factor
  , ensemble: req.ensemble
  , fastMode: req.fastMode
  }

-- | Create a sequence interpolation request
-- |
-- | @param endpoint The API endpoint
-- | @param req Sequence request containing frames array and settings
-- | @returns Request that can be sent via Bridge
mkSequenceInterpolationRequest :: ApiEndpoint -> SequenceRequest -> SequenceInterpolationBridgeRequest
mkSequenceInterpolationRequest endpoint req =
  { url: endpoint <> "/sequence"
  , frames: req.frames
  , model: rifeModelToString req.model
  , factor: factorToInt req.factor
  , ensemble: req.ensemble
  , fastMode: req.fastMode
  , preserveOriginal: req.preserveOriginal
  }

-- | Create a slow motion request
-- |
-- | @param endpoint The API endpoint
-- | @param req Slow motion request with target FPS
-- | @returns Request that can be sent via Bridge
mkSlowMoRequest :: ApiEndpoint -> SlowMoRequest -> SlowMoBridgeRequest
mkSlowMoRequest endpoint req =
  { url: endpoint <> "/slowmo"
  , frames: req.frames
  , model: rifeModelToString req.model
  , slowdownFactor: req.slowdownFactor
  , targetFps: req.targetFps
  , sourceFps: req.sourceFps
  , ensemble: req.ensemble
  , fastMode: req.fastMode
  }

-- | Create a blend frames request (client-side fallback)
-- |
-- | @param frame1 Base64-encoded first frame
-- | @param frame2 Base64-encoded second frame
-- | @param ratio Blend ratio (will be clamped to 0.0-1.0)
-- | @returns Request that can be sent via Bridge
mkBlendFramesRequest :: String -> String -> Number -> BlendFramesRequest
mkBlendFramesRequest frame1 frame2 ratio =
  { frame1
  , frame2
  , ratio: clampNumber 0.0 1.0 ratio
  }

-- | Create a frame-to-base64 conversion request
mkFrameToBase64Request :: String -> String -> Number -> FrameConversionRequest
mkFrameToBase64Request elementId format quality =
  FrameToBase64Request { elementId, format, quality }

-- | Create a base64-to-imagedata conversion request
mkBase64ToImageDataRequest :: String -> FrameConversionRequest
mkBase64ToImageDataRequest base64 =
  Base64ToImageDataRequest { base64 }

-- | Create a base64-to-blob conversion request
mkBase64ToBlobRequest :: String -> String -> FrameConversionRequest
mkBase64ToBlobRequest base64 mimeType =
  Base64ToBlobRequest { base64, mimeType }

-- | Create a client-side interpolation request
mkClientInterpolationRequest :: String -> String -> Int -> FrameConversionRequest
mkClientInterpolationRequest frame1 frame2 count =
  ClientInterpolationRequest { frame1, frame2, count }

-- ────────────────────────────────────────────────────────────────────────────
-- Pure Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate required intermediate frames for target FPS
-- |
-- | @param sourceFps Source frame rate
-- | @param targetFps Target frame rate (must be >= sourceFps)
-- | @param frameCount Number of source frames
-- | @returns Total frames needed at target FPS
-- |
-- | @example
-- | ```purescript
-- | -- 24fps to 60fps with 100 frames
-- | calculateRequiredFrames 24.0 60.0 100  -- Returns 250
-- | ```
calculateRequiredFrames :: Number -> Number -> Int -> Int
calculateRequiredFrames sourceFps targetFps frameCount =
  let ratio = targetFps / sourceFps
      totalFrames = toNumber frameCount * ratio
  in floor totalFrames

-- | Clamp a number to a range
-- |
-- | @param minVal Minimum allowed value
-- | @param maxVal Maximum allowed value
-- | @param value Value to clamp
-- | @returns Value clamped to [minVal, maxVal]
-- |
-- | @invariant minVal <= result <= maxVal
clampNumber :: Number -> Number -> Number -> Number
clampNumber minVal maxVal value =
  if value < minVal
    then minVal
    else if value > maxVal
      then maxVal
      else value

-- | Calculate blend ratios for a number of intermediate frames
-- |
-- | @param count Number of intermediate frames
-- | @returns Array of blend ratios (0.0 to 1.0)
-- |
-- | @example
-- | ```purescript
-- | calculateBlendRatios 3  -- Returns [0.25, 0.5, 0.75]
-- | ```
calculateBlendRatios :: Int -> Array Number
calculateBlendRatios count =
  let total = count + 1
  in map (\i -> toNumber (i + 1) / toNumber total) (0 .. (count - 1))

-- | Calculate timestamps for interpolated frames
-- |
-- | @param count Number of intermediate frames
-- | @returns Array of timestamps (0.0 to 1.0)
calculateInterpolationTimestamps :: Int -> Array { frameIndex :: Int, timestamp :: Number, confidence :: Number }
calculateInterpolationTimestamps count =
  mapWithIndex toTimestamp (0 .. (count - 1))
  where
    toTimestamp :: Int -> Int -> { frameIndex :: Int, timestamp :: Number, confidence :: Number }
    toTimestamp idx _ =
      { frameIndex: idx + 1
      , timestamp: toNumber (idx + 1) / toNumber (count + 1)
      , confidence: 0.5  -- Client blending has lower confidence than RIFE
      }
