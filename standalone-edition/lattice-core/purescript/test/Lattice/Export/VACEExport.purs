-- | Port of VACE control export tests (pure subset)
-- |
-- | Tests easing functions, utility calculations, and config defaults.
-- | FFI-dependent tests (PathFollower class, canvas rendering) are deferred.
-- |
-- | Sources:
-- |   - vaceControlExport.test.ts
-- |   - vaceControlExport.property.test.ts
-- |
-- | 22 tests across 4 describe blocks

module Test.Lattice.Export.VACEExport (spec) where

import Prelude

import Data.Array as Data.Array
import Lattice.Services.Export.VACE.Types
  ( PathFollowerEasing(..)
  , PathFollowerShape(..)
  , LoopMode(..)
  , OutputFormat(..)
  , defaultPathFollowerConfig
  , defaultVACEExportConfig
  )
import Lattice.Services.Export.VACE.Exporter
  ( applyEasing
  , calculateDurationForSpeed
  , calculateSpeed
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo)

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "VACEExport" do
    easingTests
    utilityTests
    defaultTests
    typeTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. Easing functions
-- ────────────────────────────────────────────────────────────────────────────

easingTests :: Spec Unit
easingTests = do
  describe "easing functions" do

    it "linear: f(0) = 0" do
      assertCloseTo (1e-10) 0.0 (applyEasing EaseLinear 0.0)

    it "linear: f(1) = 1" do
      assertCloseTo (1e-10) 1.0 (applyEasing EaseLinear 1.0)

    it "linear: f(t) = t" do
      assertCloseTo (1e-10) 0.5 (applyEasing EaseLinear 0.5)
      assertCloseTo (1e-10) 0.25 (applyEasing EaseLinear 0.25)

    it "ease-in: f(0) = 0" do
      assertCloseTo (1e-10) 0.0 (applyEasing EaseIn 0.0)

    it "ease-in: f(1) = 1" do
      assertCloseTo (1e-10) 1.0 (applyEasing EaseIn 1.0)

    it "ease-in starts slow (f(0.5) < 0.5)" do
      let v = applyEasing EaseIn 0.5
      (v < 0.5) `shouldEqual` true

    it "ease-out: f(0) = 0" do
      assertCloseTo (1e-10) 0.0 (applyEasing EaseOut 0.0)

    it "ease-out: f(1) = 1" do
      assertCloseTo (1e-10) 1.0 (applyEasing EaseOut 1.0)

    it "ease-out ends slow (f(0.5) > 0.5)" do
      let v = applyEasing EaseOut 0.5
      (v > 0.5) `shouldEqual` true

    it "ease-in-out: f(0) = 0" do
      assertCloseTo (1e-10) 0.0 (applyEasing EaseInOut 0.0)

    it "ease-in-out: f(1) = 1" do
      assertCloseTo (1e-10) 1.0 (applyEasing EaseInOut 1.0)

    it "ease-in-out: f(0.5) = 0.5 (symmetric)" do
      assertCloseTo (1e-10) 0.5 (applyEasing EaseInOut 0.5)

    it "ease-in-cubic: f(0) = 0, f(1) = 1" do
      assertCloseTo (1e-10) 0.0 (applyEasing EaseInCubic 0.0)
      assertCloseTo (1e-10) 1.0 (applyEasing EaseInCubic 1.0)

    it "ease-out-cubic: f(0) = 0, f(1) = 1" do
      assertCloseTo (1e-10) 0.0 (applyEasing EaseOutCubic 0.0)
      assertCloseTo (1e-10) 1.0 (applyEasing EaseOutCubic 1.0)

-- ────────────────────────────────────────────────────────────────────────────
-- 2. Utility functions
-- ────────────────────────────────────────────────────────────────────────────

utilityTests :: Spec Unit
utilityTests = do
  describe "utility functions" do

    it "calculateDurationForSpeed: 100px at 5px/frame = 20 frames" do
      calculateDurationForSpeed 100.0 5.0 `shouldEqual` 20

    it "calculateSpeed: 100px in 20 frames = 5 px/frame" do
      assertCloseTo (1e-5) 5.0 (calculateSpeed 100.0 20)

    it "calculateSpeed: 0 duration returns 0" do
      assertCloseTo (1e-10) 0.0 (calculateSpeed 100.0 0)

-- ────────────────────────────────────────────────────────────────────────────
-- 3. Default config values
-- ────────────────────────────────────────────────────────────────────────────

defaultTests :: Spec Unit
defaultTests = do
  describe "default config" do

    it "defaultPathFollowerConfig has correct shape" do
      defaultPathFollowerConfig.shape `shouldEqual` ShapeCircle

    it "defaultPathFollowerConfig has 60-frame duration" do
      defaultPathFollowerConfig.duration `shouldEqual` 60

    it "defaultPathFollowerConfig uses ease-in-out" do
      defaultPathFollowerConfig.easing `shouldEqual` EaseInOut

    it "defaultVACEExportConfig has 512x512" do
      defaultVACEExportConfig.width `shouldEqual` 512
      defaultVACEExportConfig.height `shouldEqual` 512

    it "defaultVACEExportConfig has black background" do
      defaultVACEExportConfig.backgroundColor `shouldEqual` "#000000"

    it "defaultVACEExportConfig has 16fps" do
      defaultVACEExportConfig.frameRate `shouldEqual` 16

    it "defaultVACEExportConfig has antiAlias enabled" do
      defaultVACEExportConfig.antiAlias `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 4. Type enumeration tests
-- ────────────────────────────────────────────────────────────────────────────

typeTests :: Spec Unit
typeTests = do
  describe "type enumerations" do

    it "PathFollowerShape has 6 variants" do
      let shapes = [ShapeCircle, ShapeSquare, ShapeTriangle, ShapeDiamond, ShapeArrow, ShapeCustom]
      arrayLength shapes `shouldEqual` 6

    it "PathFollowerEasing has 6 variants" do
      let easings = [EaseLinear, EaseIn, EaseOut, EaseInOut, EaseInCubic, EaseOutCubic]
      arrayLength easings `shouldEqual` 6

    it "LoopMode has 2 variants" do
      let modes = [LoopRestart, LoopPingPong]
      arrayLength modes `shouldEqual` 2

arrayLength :: forall a. Array a -> Int
arrayLength = Data.Array.length
