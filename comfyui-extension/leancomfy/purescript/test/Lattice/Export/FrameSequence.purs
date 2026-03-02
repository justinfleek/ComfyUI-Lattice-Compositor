-- | Port of frame sequence exporter tests (pure subset)
-- |
-- | Tests format utilities: formatFrameNumber, generateFilename,
-- | isBrowserFormat, getFormatInfo.
-- |
-- | Sources:
-- |   - frameSequenceExporter.test.ts
-- |
-- | 13 tests across 4 describe blocks

module Test.Lattice.Export.FrameSequence (spec) where

import Prelude

import Data.Array (length)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

import Lattice.Services.Export.FrameSequence
  ( FrameFormat(..)
  , isBrowserFormat
  , formatFrameNumber
  , generateFilename
  , getFormatInfo
  )

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "FrameSequence" do
    isBrowserFormatTests
    formatFrameNumberTests
    generateFilenameTests
    getFormatInfoTests

--------------------------------------------------------------------------------
-- 1. isBrowserFormat
--------------------------------------------------------------------------------

isBrowserFormatTests :: Spec Unit
isBrowserFormatTests = do
  describe "isBrowserFormat" do

    it "returns true for browser formats (PNG, JPEG, WebP)" do
      isBrowserFormat FormatPNG `shouldEqual` true
      isBrowserFormat FormatJPEG `shouldEqual` true
      isBrowserFormat FormatWebP `shouldEqual` true

    it "returns false for backend formats (TIFF, EXR, DPX)" do
      isBrowserFormat FormatTIFF `shouldEqual` false
      isBrowserFormat FormatEXR `shouldEqual` false
      isBrowserFormat FormatDPX `shouldEqual` false

--------------------------------------------------------------------------------
-- 2. formatFrameNumber
--------------------------------------------------------------------------------

formatFrameNumberTests :: Spec Unit
formatFrameNumberTests = do
  describe "formatFrameNumber" do

    it "pads frame number to specified digits" do
      let result = formatFrameNumber "frame_{frame:04d}" 42
      -- Should produce "frame_0042"
      result `shouldEqual` "frame_0042"

    it "handles different padding widths" do
      let r2 = formatFrameNumber "f_{frame:02d}" 5
      r2 `shouldEqual` "f_05"

    it "handles zero frame number" do
      let result = formatFrameNumber "frame_{frame:04d}" 0
      result `shouldEqual` "frame_0000"

    it "returns pattern unchanged if no placeholder" do
      let result = formatFrameNumber "static_name" 42
      result `shouldEqual` "static_name"

--------------------------------------------------------------------------------
-- 3. generateFilename
--------------------------------------------------------------------------------

generateFilenameTests :: Spec Unit
generateFilenameTests = do
  describe "generateFilename" do

    it "appends correct extension for PNG" do
      let result = generateFilename "frame_{frame:04d}" 1 FormatPNG
      result `shouldEqual` "frame_0001.png"

    it "appends correct extension for JPEG" do
      let result = generateFilename "frame_{frame:04d}" 10 FormatJPEG
      result `shouldEqual` "frame_0010.jpg"

    it "appends correct extension for EXR" do
      let result = generateFilename "render_{frame:04d}" 5 FormatEXR
      result `shouldEqual` "render_0005.exr"

--------------------------------------------------------------------------------
-- 4. getFormatInfo
--------------------------------------------------------------------------------

getFormatInfoTests :: Spec Unit
getFormatInfoTests = do
  describe "getFormatInfo" do

    it "returns correct info for PNG" do
      let info = getFormatInfo FormatPNG
      info.name `shouldEqual` "PNG"
      info.extension `shouldEqual` "png"
      info.requiresBackend `shouldEqual` false
      info.supportsAlpha `shouldEqual` true
      info.lossy `shouldEqual` false

    it "returns correct info for JPEG" do
      let info = getFormatInfo FormatJPEG
      info.name `shouldEqual` "JPEG"
      info.extension `shouldEqual` "jpg"
      info.supportsAlpha `shouldEqual` false
      info.lossy `shouldEqual` true

    it "returns correct info for EXR" do
      let info = getFormatInfo FormatEXR
      info.name `shouldEqual` "OpenEXR"
      info.extension `shouldEqual` "exr"
      info.requiresBackend `shouldEqual` true
      info.supportsAlpha `shouldEqual` true

    it "returns correct info for DPX" do
      let info = getFormatInfo FormatDPX
      info.name `shouldEqual` "DPX"
      info.extension `shouldEqual` "dpx"
      info.requiresBackend `shouldEqual` true
      info.supportsAlpha `shouldEqual` false

    it "all formats have at least one bit depth" do
      let checkFormat fmt = (length (getFormatInfo fmt).bitDepths > 0) `shouldEqual` true
      checkFormat FormatPNG
      checkFormat FormatJPEG
      checkFormat FormatWebP
      checkFormat FormatTIFF
      checkFormat FormatEXR
      checkFormat FormatDPX
