-- | Lattice.Services.Export.VideoEncoder - Video encoding service
-- |
-- | Prepares video encoding requests for the Haskell backend.
-- | All actual encoding is done server-side via Bridge.
-- |
-- | Source: ui/src/services/export/videoEncoder.ts

module Lattice.Services.Export.VideoEncoder
  ( -- * Types
    VideoCodec(..)
  , VideoQuality(..)
  , VideoEncoderConfig
  , EncodingProgressData
  , EncodedVideoResult
    -- * Request Types (for Bridge)
  , VideoEncoderRequest(..)
  , VideoEncodeFrameRequest
  , VideoFinalizeRequest
    -- * Request Builders
  , mkCreateEncoderRequest
  , mkEncodeFrameRequest
  , mkFinalizeRequest
  , mkEncodeSequenceRequest
    -- * Config Utilities
  , codecToString
  , qualityToString
  , calculateBitrate
  , defaultConfig
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Video codec options
data VideoCodec
  = CodecAVC    -- H.264 -> MP4 container
  | CodecVP9    -- VP9 -> WebM container
  | CodecVP8    -- VP8 -> WebM container

derive instance Generic VideoCodec _
instance Show VideoCodec where show = genericShow
instance Eq VideoCodec where eq = genericEq
instance EncodeJson VideoCodec where
  encodeJson = genericEncodeJson

-- | Video quality presets
data VideoQuality
  = QualityLow
  | QualityMedium
  | QualityHigh
  | QualityLossless

derive instance Generic VideoQuality _
instance Show VideoQuality where show = genericShow
instance Eq VideoQuality where eq = genericEq
instance EncodeJson VideoQuality where
  encodeJson = genericEncodeJson

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
  { outputPath :: String        -- Path to encoded video on server
  , mimeType :: String
  , duration :: Number
  , frameCount :: Int
  , size :: Int
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Types (for Bridge)
-- ────────────────────────────────────────────────────────────────────────────

-- | Video encoder request - sent to Haskell backend
data VideoEncoderRequest
  = CreateEncoderRequest VideoEncoderConfig
  | EncodeFrameRequest VideoEncodeFrameRequest
  | FinalizeEncoderRequest VideoFinalizeRequest
  | EncodeSequenceRequest
      { config :: VideoEncoderConfig
      , framePaths :: Array String  -- Paths to frame images on server
      }

derive instance Generic VideoEncoderRequest _
instance Show VideoEncoderRequest where show = genericShow
instance EncodeJson VideoEncoderRequest where
  encodeJson = genericEncodeJson

-- | Single frame encode request
type VideoEncodeFrameRequest =
  { encoderId :: String       -- Session ID for encoder
  , framePath :: String       -- Path to frame image on server
  , frameIndex :: Int
  , totalFrames :: Int
  , keyFrame :: Boolean
  }

-- | Finalize encoder request
type VideoFinalizeRequest =
  { encoderId :: String
  , outputPath :: String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Builders
-- ────────────────────────────────────────────────────────────────────────────

-- | Create encoder initialization request
mkCreateEncoderRequest :: VideoEncoderConfig -> VideoEncoderRequest
mkCreateEncoderRequest = CreateEncoderRequest

-- | Create frame encode request
mkEncodeFrameRequest
  :: String    -- encoderId
  -> String    -- framePath
  -> Int       -- frameIndex
  -> Int       -- totalFrames
  -> Boolean   -- keyFrame
  -> VideoEncoderRequest
mkEncodeFrameRequest encoderId framePath frameIndex totalFrames keyFrame =
  EncodeFrameRequest
    { encoderId
    , framePath
    , frameIndex
    , totalFrames
    , keyFrame
    }

-- | Create finalize request
mkFinalizeRequest :: String -> String -> VideoEncoderRequest
mkFinalizeRequest encoderId outputPath =
  FinalizeEncoderRequest { encoderId, outputPath }

-- | Create full sequence encode request
mkEncodeSequenceRequest :: VideoEncoderConfig -> Array String -> VideoEncoderRequest
mkEncodeSequenceRequest config framePaths =
  EncodeSequenceRequest { config, framePaths }

-- ────────────────────────────────────────────────────────────────────────────
-- Config Utilities
-- ────────────────────────────────────────────────────────────────────────────

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

-- | Calculate bitrate based on resolution and quality
calculateBitrate :: Int -> Int -> VideoQuality -> Int
calculateBitrate width height quality =
  let
    pixels = width * height
    -- Base bitrate per megapixel
    baseBitrate = case quality of
      QualityLow -> 2000000       -- 2 Mbps per MP
      QualityMedium -> 5000000    -- 5 Mbps per MP
      QualityHigh -> 10000000     -- 10 Mbps per MP
      QualityLossless -> 50000000 -- 50 Mbps per MP (approximation)
    megapixels = pixels / 1000000
  in
    -- Using Int multiplication (no pow needed)
    baseBitrate * (pixels / 1000000 + 1)

-- | Default video encoder config
defaultConfig :: VideoEncoderConfig
defaultConfig =
  { width: 1920
  , height: 1080
  , frameRate: 30
  , codec: CodecAVC
  , bitrate: Nothing
  , quality: QualityHigh
  }
