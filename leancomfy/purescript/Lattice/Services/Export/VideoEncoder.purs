-- | Lattice.Services.Export.VideoEncoder - Video encoding service
-- |
-- | Uses WebCodecs API to encode frame sequences into video.
-- | Uses webm-muxer/mp4-muxer for proper container generation.
-- | Supports H.264/AVC and VP9 codecs with configurable quality.
-- |
-- | Source: ui/src/services/export/videoEncoder.ts

module Lattice.Services.Export.VideoEncoder
  ( -- * Types
    VideoCodec(..)
  , VideoQuality(..)
  , VideoEncoderConfig
  , EncodingProgressData
  , EncodedVideoResult
    -- * Support Check
  , isWebCodecsSupported
  , getSupportedCodecs
    -- * Encoder Handle
  , VideoEncoderHandle
  , FrameData
  , createEncoder
  , initializeEncoder
  , encodeFrame
  , finalizeEncoder
  , cancelEncoder
    -- * Convenience Functions
  , encodeFrameSequence
  , downloadVideo
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Foreign (Foreign)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Video codec options
data VideoCodec
  = CodecAVC    -- H.264 → MP4 container
  | CodecVP9    -- VP9 → WebM container
  | CodecVP8    -- VP8 → WebM container

derive instance Generic VideoCodec _
instance Show VideoCodec where show = genericShow
instance Eq VideoCodec where eq = genericEq

-- | Video quality presets
data VideoQuality
  = QualityLow
  | QualityMedium
  | QualityHigh
  | QualityLossless

derive instance Generic VideoQuality _
instance Show VideoQuality where show = genericShow
instance Eq VideoQuality where eq = genericEq

-- | Video encoder configuration
type VideoEncoderConfig =
  { width :: Int
  , height :: Int
  , frameRate :: Int
  , codec :: VideoCodec
  , bitrate :: Maybe Int       -- bits per second, auto-calculated if Nothing
  , quality :: VideoQuality
  }

-- | Encoding progress data
type EncodingProgressData =
  { framesEncoded :: Int
  , totalFrames :: Int
  , percentage :: Number
  , bytesWritten :: Int
  }

-- | Encoded video result
type EncodedVideoResult =
  { blobUrl :: String           -- Object URL to blob
  , mimeType :: String
  , duration :: Number
  , frameCount :: Int
  , size :: Int
  }

--------------------------------------------------------------------------------
-- FFI Types
--------------------------------------------------------------------------------

-- | Opaque handle to WebCodecs encoder
foreign import data VideoEncoderHandle :: Type

-- | Opaque handle to frame data (ImageData, Canvas, etc.)
foreign import data FrameData :: Type

--------------------------------------------------------------------------------
-- Support Check
--------------------------------------------------------------------------------

-- | Check if WebCodecs API is supported
foreign import isWebCodecsSupported :: Effect Boolean

-- | Get list of supported codecs
foreign import getSupportedCodecsImpl :: EffectFnAff (Array String)

getSupportedCodecs :: Aff (Array String)
getSupportedCodecs = fromEffectFnAff getSupportedCodecsImpl

--------------------------------------------------------------------------------
-- Encoder Operations
--------------------------------------------------------------------------------

-- | Create a new encoder instance
foreign import createEncoderImpl :: Foreign -> Effect VideoEncoderHandle

createEncoder :: VideoEncoderConfig -> Effect VideoEncoderHandle
createEncoder config = createEncoderImpl (configToForeign config)

-- | Initialize encoder (async)
foreign import initializeEncoderImpl :: VideoEncoderHandle -> (EncodingProgressData -> Effect Unit) -> EffectFnAff Unit

initializeEncoder :: VideoEncoderHandle -> (EncodingProgressData -> Effect Unit) -> Aff Unit
initializeEncoder handle onProgress = fromEffectFnAff (initializeEncoderImpl handle onProgress)

-- | Encode a single frame
foreign import encodeFrameImpl :: VideoEncoderHandle -> FrameData -> Int -> Int -> Boolean -> EffectFnAff Unit

encodeFrame :: VideoEncoderHandle -> FrameData -> Int -> Int -> Boolean -> Aff Unit
encodeFrame handle frame frameIndex totalFrames keyFrame =
  fromEffectFnAff (encodeFrameImpl handle frame frameIndex totalFrames keyFrame)

-- | Finalize encoding and get result
foreign import finalizeEncoderImpl :: VideoEncoderHandle -> EffectFnAff EncodedVideoResult

finalizeEncoder :: VideoEncoderHandle -> Aff EncodedVideoResult
finalizeEncoder handle = fromEffectFnAff (finalizeEncoderImpl handle)

-- | Cancel encoding
foreign import cancelEncoderImpl :: VideoEncoderHandle -> Effect Unit

cancelEncoder :: VideoEncoderHandle -> Effect Unit
cancelEncoder = cancelEncoderImpl

--------------------------------------------------------------------------------
-- Convenience Functions
--------------------------------------------------------------------------------

-- | Encode a sequence of frames to video
foreign import encodeFrameSequenceImpl
  :: Array FrameData
  -> Foreign
  -> (EncodingProgressData -> Effect Unit)
  -> EffectFnAff EncodedVideoResult

encodeFrameSequence
  :: Array FrameData
  -> VideoEncoderConfig
  -> (EncodingProgressData -> Effect Unit)
  -> Aff EncodedVideoResult
encodeFrameSequence frames config onProgress =
  fromEffectFnAff (encodeFrameSequenceImpl frames (configToForeign config) onProgress)

-- | Download encoded video to user's device
foreign import downloadVideo :: EncodedVideoResult -> String -> Effect Unit

--------------------------------------------------------------------------------
-- Internal Helpers
--------------------------------------------------------------------------------

-- | Convert codec to string
codecToString :: VideoCodec -> String
codecToString = case _ of
  CodecAVC -> "avc"
  CodecVP9 -> "vp9"
  CodecVP8 -> "vp8"

-- | Convert quality to string
qualityToString :: VideoQuality -> String
qualityToString = case _ of
  QualityLow -> "low"
  QualityMedium -> "medium"
  QualityHigh -> "high"
  QualityLossless -> "lossless"

-- | Convert config to Foreign for FFI
foreign import configToForeign :: VideoEncoderConfig -> Foreign
