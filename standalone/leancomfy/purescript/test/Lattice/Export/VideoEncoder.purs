-- | Port of video encoder tests (pure subset)
-- |
-- | Tests type structures, codec enumerations, and quality presets.
-- | Browser-dependent tests (WebCodecs API) are omitted.
-- |
-- | Sources:
-- |   - videoEncoder.test.ts
-- |
-- | 7 tests across 2 describe blocks

module Test.Lattice.Export.VideoEncoder (spec) where

import Prelude

import Data.Array (length)
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

import Lattice.Services.Export.VideoEncoder
  ( VideoCodec(..)
  , VideoQuality(..)
  )

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "VideoEncoder" do
    codecTests
    typeStructureTests

--------------------------------------------------------------------------------
-- 1. Codec enumerations
--------------------------------------------------------------------------------

codecTests :: Spec Unit
codecTests = do
  describe "codec enumerations" do

    it "VideoCodec has 3 constructors" do
      let codecs = [CodecAVC, CodecVP9, CodecVP8]
      length codecs `shouldEqual` 3

    it "VideoQuality has 4 constructors" do
      let qualities = [QualityLow, QualityMedium, QualityHigh, QualityLossless]
      length qualities `shouldEqual` 4

--------------------------------------------------------------------------------
-- 2. Type structures
--------------------------------------------------------------------------------

typeStructureTests :: Spec Unit
typeStructureTests = do
  describe "type structures" do

    it "VideoEncoderConfig has correct structure" do
      let config =
            { width: 1920
            , height: 1080
            , frameRate: 30
            , codec: CodecAVC
            , bitrate: Just 8000000
            , quality: QualityHigh
            }
      config.width `shouldEqual` 1920
      config.height `shouldEqual` 1080
      config.frameRate `shouldEqual` 30
      config.codec `shouldEqual` CodecAVC
      config.bitrate `shouldEqual` Just 8000000
      config.quality `shouldEqual` QualityHigh

    it "EncodingProgressData has correct structure" do
      let progress =
            { framesEncoded: 50
            , totalFrames: 100
            , percentage: 50.0
            , bytesWritten: 1024000
            }
      progress.framesEncoded `shouldEqual` 50
      progress.totalFrames `shouldEqual` 100
      (progress.percentage > 0.0) `shouldEqual` true
      (progress.bytesWritten > 0) `shouldEqual` true

    it "EncodedVideoResult has correct structure" do
      let result =
            { blobUrl: "blob:http://localhost/video"
            , mimeType: "video/mp4"
            , duration: 3.33
            , frameCount: 100
            , size: 5000000
            }
      result.mimeType `shouldEqual` "video/mp4"
      result.frameCount `shouldEqual` 100
      (result.duration > 0.0) `shouldEqual` true

    it "valid codec values are distinct" do
      (CodecAVC /= CodecVP9) `shouldEqual` true
      (CodecVP9 /= CodecVP8) `shouldEqual` true
      (CodecAVC /= CodecVP8) `shouldEqual` true

    it "valid quality values are ordered" do
      -- Each quality level is distinct
      (QualityLow /= QualityMedium) `shouldEqual` true
      (QualityMedium /= QualityHigh) `shouldEqual` true
      (QualityHigh /= QualityLossless) `shouldEqual` true
