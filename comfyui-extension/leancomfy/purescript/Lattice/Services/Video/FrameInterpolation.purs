-- | Lattice.Services.Video.FrameInterpolation - Frame interpolation service
-- |
-- | @module Lattice.Services.Video.FrameInterpolation
-- | @description RIFE-based frame interpolation for video processing.
-- |
-- | ## Architecture
-- |
-- | This module provides frame interpolation via:
-- | 1. **Server-side RIFE** - Neural network interpolation (high quality)
-- | 2. **Client-side blending** - Alpha blending fallback (fast, lower quality)
-- |
-- | ## Configuration
-- |
-- | The API endpoint is passed explicitly to all functions that need it.
-- | There is NO global mutable state. This is a pure functional API.
-- |
-- | ## Example Usage
-- |
-- | ```purescript
-- | let endpoint = "/api/interpolation"
-- |
-- | -- Get available models
-- | models <- getInterpolationModels endpoint
-- |
-- | -- Interpolate two frames
-- | result <- interpolateFramePair endpoint
-- |   { frame1: base64Frame1
-- |   , frame2: base64Frame2
-- |   , model: RIFEv4_6
-- |   , factor: Factor2X
-- |   , ensemble: true
-- |   , fastMode: false
-- |   }
-- | ```
-- |
-- | ## Banned Constructs
-- |
-- | This module contains ZERO:
-- | - unsafePerformEffect (BANNED)
-- | - unsafePartial (BANNED)
-- | - unsafeCoerce (BANNED)
-- | - Global mutable state (BANNED)
-- |
-- | Source: ui/src/services/video/frameInterpolation.ts (service section)

module Lattice.Services.Video.FrameInterpolation
  ( -- * Types
    ApiEndpoint
  , InterpolationConfig(..)
  , ImageData
  , Blob
    -- * API Functions
  , getInterpolationModels
  , interpolateFramePair
  , interpolateSequence
  , createSlowMotion
    -- * Client-side Fallback
  , blendFrames
  , interpolateFramesClient
    -- * Utilities
  , frameToBase64
  , base64ToImageData
  , base64ToBlob
  , calculateRequiredFrames
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Class (liftEffect)
import Data.Array (mapWithIndex)
import Data.Int (toNumber, floor)

import Lattice.Services.Video.Types
  ( RIFEModel
  , InterpolationFactor
  , InterpolationModel
  , PairInterpolationResult
  , SequenceInterpolationResult
  , SlowMoResult
  , InterpolatedFrame
  , InterpolationRequest
  , SequenceRequest
  , SlowMoRequest
  , rifeModelToString
  , factorToInt
  )

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- FFI Types
--------------------------------------------------------------------------------

-- | Canvas rendering context (opaque FFI type)
-- | @internal Used for canvas operations in FFI layer
foreign import data CanvasContext :: Type

-- | ImageData from canvas (opaque FFI type)
-- | @internal Contains pixel data (Uint8ClampedArray) and dimensions
foreign import data ImageData :: Type

-- | Blob for binary data (opaque FFI type)
-- | @internal Web API Blob for file operations
foreign import data Blob :: Type

--------------------------------------------------------------------------------
-- FFI Imports - API
--------------------------------------------------------------------------------

-- | @ffi Fetch available interpolation models from server
-- | @param url Full API URL for models endpoint
-- | @returns Array of available InterpolationModel records
foreign import getModelsImpl :: String -> EffectFnAff (Array InterpolationModel)

-- | @ffi Interpolate a pair of frames via API
-- | @param url API endpoint URL
-- | @param frame1 Base64-encoded first frame
-- | @param frame2 Base64-encoded second frame
-- | @param model RIFE model identifier string
-- | @param factor Interpolation factor (2, 4, 8, etc.)
-- | @param ensemble Use ensemble mode for higher quality
-- | @param fastMode Use fast mode (lower quality, faster)
foreign import interpolatePairImpl
  :: String
  -> String
  -> String
  -> String
  -> Int
  -> Boolean
  -> Boolean
  -> EffectFnAff PairInterpolationResult

-- | @ffi Interpolate a sequence of frames via API
foreign import interpolateSequenceImpl
  :: String
  -> Array String
  -> String
  -> Int
  -> Boolean
  -> Boolean
  -> Boolean
  -> EffectFnAff SequenceInterpolationResult

-- | @ffi Create slow motion via API
foreign import createSlowMotionImpl
  :: String
  -> Array String
  -> String
  -> Number
  -> Number
  -> Number
  -> Boolean
  -> Boolean
  -> EffectFnAff SlowMoResult

--------------------------------------------------------------------------------
-- FFI Imports - Canvas Operations
--------------------------------------------------------------------------------

-- | @ffi Convert frame (canvas/image element) to base64 string
-- | @param elementId DOM element ID
-- | @param format Image format ("image/png" or "image/jpeg")
-- | @param quality Quality for JPEG (0.0 to 1.0)
foreign import frameToBase64Impl :: String -> String -> Number -> Effect String

-- | @ffi Convert base64 string to ImageData
foreign import base64ToImageDataImpl :: String -> EffectFnAff ImageData

-- | @ffi Convert base64 string to Blob
foreign import base64ToBlobImpl :: String -> String -> Effect Blob

-- | @ffi Blend two frames at a given ratio (0-1)
-- | @param frame1 Base64-encoded first frame
-- | @param frame2 Base64-encoded second frame
-- | @param ratio Blend ratio (0.0 = frame1, 1.0 = frame2)
foreign import blendFramesImpl :: String -> String -> Number -> EffectFnAff String

-- | @ffi Client-side interpolation between frames
foreign import interpolateClientImpl
  :: String
  -> String
  -> Int
  -> EffectFnAff (Array String)

--------------------------------------------------------------------------------
-- API Functions
--------------------------------------------------------------------------------

-- | Fetch available interpolation models from server
-- |
-- | @param endpoint The API endpoint (e.g., "/api/interpolation")
-- | @returns Aff containing array of available models
-- |
-- | @example
-- | ```purescript
-- | models <- getInterpolationModels "/api/interpolation"
-- | ```
getInterpolationModels :: ApiEndpoint -> Aff (Array InterpolationModel)
getInterpolationModels endpoint =
  fromEffectFnAff (getModelsImpl (endpoint <> "/models"))

-- | Interpolate between two frames using RIFE
-- |
-- | @param endpoint The API endpoint
-- | @param req Interpolation request containing frames and settings
-- | @returns Result containing interpolated frames and metadata
-- |
-- | @precondition Both frames must be valid base64-encoded images
-- | @postcondition Result contains (factor - 1) intermediate frames
interpolateFramePair :: ApiEndpoint -> InterpolationRequest -> Aff PairInterpolationResult
interpolateFramePair endpoint req =
  fromEffectFnAff $ interpolatePairImpl
    (endpoint <> "/pair")
    req.frame1
    req.frame2
    (rifeModelToString req.model)
    (factorToInt req.factor)
    req.ensemble
    req.fastMode

-- | Interpolate a sequence of frames
-- |
-- | @param endpoint The API endpoint
-- | @param req Sequence request containing frames array and settings
-- | @returns Result with all interpolated frames
-- |
-- | @precondition frames array length >= 2
-- | @postcondition Output frames = (input frames - 1) * factor + 1
interpolateSequence :: ApiEndpoint -> SequenceRequest -> Aff SequenceInterpolationResult
interpolateSequence endpoint req =
  fromEffectFnAff $ interpolateSequenceImpl
    (endpoint <> "/sequence")
    req.frames
    (rifeModelToString req.model)
    (factorToInt req.factor)
    req.ensemble
    req.fastMode
    req.preserveOriginal

-- | Create slow motion effect
-- |
-- | @param endpoint The API endpoint
-- | @param req Slow motion request with target FPS
-- | @returns Frames at target FPS
-- |
-- | @example
-- | ```purescript
-- | -- Convert 24fps footage to 120fps (5x slow motion)
-- | result <- createSlowMotion "/api/interpolation"
-- |   { frames: videoFrames
-- |   , model: RIFEv4_6
-- |   , slowdownFactor: 5.0
-- |   , targetFps: 120.0
-- |   , sourceFps: 24.0
-- |   , ensemble: true
-- |   , fastMode: false
-- |   }
-- | ```
createSlowMotion :: ApiEndpoint -> SlowMoRequest -> Aff SlowMoResult
createSlowMotion endpoint req =
  fromEffectFnAff $ createSlowMotionImpl
    (endpoint <> "/slowmo")
    req.frames
    (rifeModelToString req.model)
    req.slowdownFactor
    req.targetFps
    req.sourceFps
    req.ensemble
    req.fastMode

--------------------------------------------------------------------------------
-- Client-side Fallback
--------------------------------------------------------------------------------

-- | Blend two frames at a ratio (0 = frame1, 1 = frame2)
-- |
-- | Client-side fallback when RIFE API is unavailable.
-- | Uses simple alpha blending - lower quality than neural interpolation.
-- |
-- | @param frame1 Base64-encoded first frame
-- | @param frame2 Base64-encoded second frame
-- | @param ratio Blend ratio (clamped to 0.0-1.0)
-- | @returns Blended frame as base64 string
-- |
-- | @invariant 0.0 <= ratio <= 1.0 (enforced by clamping)
blendFrames :: String -> String -> Number -> Aff String
blendFrames frame1 frame2 ratio =
  let clampedRatio = clampNumber 0.0 1.0 ratio
  in fromEffectFnAff (blendFramesImpl frame1 frame2 clampedRatio)

-- | Client-side frame interpolation using blending
-- |
-- | Generates intermediate frames between two frames using alpha blending.
-- | Lower quality than RIFE but works offline.
-- |
-- | @param frame1 Base64-encoded first frame
-- | @param frame2 Base64-encoded second frame
-- | @param count Number of intermediate frames to generate
-- | @returns Array of InterpolatedFrame records
-- |
-- | @postcondition length result == count
interpolateFramesClient :: String -> String -> Int -> Aff (Array InterpolatedFrame)
interpolateFramesClient frame1 frame2 count = do
  results <- fromEffectFnAff (interpolateClientImpl frame1 frame2 count)
  pure (mapWithIndex (toInterpolatedFrame count) results)
  where
    toInterpolatedFrame :: Int -> Int -> String -> InterpolatedFrame
    toInterpolatedFrame total idx dataUrl =
      { frameIndex: idx + 1
      , timestamp: toNumber (idx + 1) / toNumber (total + 1)
      , dataUrl
      , confidence: 0.5  -- Client blending has lower confidence than RIFE
      }

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Convert frame element to base64
-- |
-- | @param elementId DOM element ID (canvas or image)
-- | @param format "image/png" or "image/jpeg"
-- | @param quality Quality for JPEG (0.0 to 1.0)
-- | @returns Base64-encoded image data
frameToBase64 :: String -> String -> Number -> Effect String
frameToBase64 = frameToBase64Impl

-- | Convert base64 string to ImageData
-- |
-- | @param base64 Base64-encoded image
-- | @returns ImageData for canvas manipulation
base64ToImageData :: String -> Aff ImageData
base64ToImageData = fromEffectFnAff <<< base64ToImageDataImpl

-- | Convert base64 string to Blob
-- |
-- | @param base64 Base64-encoded data
-- | @param mimeType MIME type (e.g., "image/png")
-- | @returns Blob for file operations
base64ToBlob :: String -> String -> Effect Blob
base64ToBlob = base64ToBlobImpl

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

--------------------------------------------------------------------------------
-- Internal Helpers (Pure Functions)
--------------------------------------------------------------------------------

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
