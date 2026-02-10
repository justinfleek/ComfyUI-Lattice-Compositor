-- | Port of opacity range contract tests
-- |
-- | Tests opacity conversion formula (0-100 → 0-1), clamping,
-- | visibility interaction, and regression bug prevention.
-- |
-- | Sources:
-- |   - opacity-range.contract.test.ts
-- |
-- | 15 tests across 4 describe blocks

module Test.Lattice.Export.OpacityRange (spec) where

import Prelude

import Data.Number (isNaN)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Convert opacity (0-100) to alpha (0-1), matching the TS convention
opacityToAlpha :: Number -> Number
opacityToAlpha opacity = opacity / 100.0

-- | Clamp a number to [min, max]
clamp :: Number -> Number -> Number -> Number
clamp lo hi x
  | x < lo = lo
  | x > hi = hi
  | otherwise = x

-- | Safe opacity conversion with clamping and NaN handling
safeOpacityToAlpha :: Number -> Number
safeOpacityToAlpha opacity =
  if isNaN opacity then 0.0
  else clamp 0.0 1.0 (opacity / 100.0)

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "OpacityRange" do
    conversionTests
    clampingTests
    visibilityInteractionTests
    regressionTests

--------------------------------------------------------------------------------
-- 1. Opacity conversion formula
--------------------------------------------------------------------------------

conversionTests :: Spec Unit
conversionTests = do
  describe "opacity conversion formula" do

    it "0% opacity converts to 0.0 alpha" do
      assertCloseTo 1e-10 0.0 (opacityToAlpha 0.0)

    it "100% opacity converts to 1.0 alpha" do
      assertCloseTo 1e-10 1.0 (opacityToAlpha 100.0)

    it "50% opacity converts to 0.5 alpha" do
      assertCloseTo 1e-10 0.5 (opacityToAlpha 50.0)

    it "75.5% opacity converts correctly" do
      assertCloseTo 1e-10 0.755 (opacityToAlpha 75.5)

    it "common opacity values convert correctly" do
      assertCloseTo 1e-10 0.1 (opacityToAlpha 10.0)
      assertCloseTo 1e-10 0.25 (opacityToAlpha 25.0)
      assertCloseTo 1e-10 0.33 (opacityToAlpha 33.0)
      assertCloseTo 1e-10 0.66 (opacityToAlpha 66.0)
      assertCloseTo 1e-10 0.75 (opacityToAlpha 75.0)
      assertCloseTo 1e-10 0.9 (opacityToAlpha 90.0)

--------------------------------------------------------------------------------
-- 2. Invalid opacity clamping
--------------------------------------------------------------------------------

clampingTests :: Spec Unit
clampingTests = do
  describe "invalid opacity clamping" do

    it "clamps negative to 0" do
      assertCloseTo 1e-10 0.0 (safeOpacityToAlpha (-50.0))

    it "clamps >100 to 1" do
      assertCloseTo 1e-10 1.0 (safeOpacityToAlpha 200.0)

    it "NaN converts to 0" do
      let nan = 0.0 / 0.0
      assertCloseTo 1e-10 0.0 (safeOpacityToAlpha nan)

--------------------------------------------------------------------------------
-- 3. Visibility and opacity interaction
--------------------------------------------------------------------------------

visibilityInteractionTests :: Spec Unit
visibilityInteractionTests = do
  describe "visibility and opacity interaction" do

    it "invisible layer skips render regardless of opacity" do
      let visible = false
      let opacity = 100.0
      let shouldRender = visible && opacity > 0.0
      shouldRender `shouldEqual` false

    it "visible layer with opacity > 0 renders" do
      let visible = true
      let opacity = 50.0
      let shouldRender = visible && opacity > 0.0
      shouldRender `shouldEqual` true

    it "visible layer with opacity = 0 skips render" do
      let visible = true
      let opacity = 0.0
      let shouldRender = visible && opacity > 0.0
      shouldRender `shouldEqual` false

    it "group * layer opacity multiplication" do
      let groupOpacity = 80.0
      let layerOpacity = 50.0
      let combined = (groupOpacity / 100.0) * (layerOpacity / 100.0)
      assertCloseTo 1e-10 0.4 combined

--------------------------------------------------------------------------------
-- 4. Regression prevention
--------------------------------------------------------------------------------

regressionTests :: Spec Unit
regressionTests = do
  describe "opacity regression prevention" do

    it "globalAlpha never exceeds 1.0" do
      let alpha = safeOpacityToAlpha 150.0
      (alpha <= 1.0) `shouldEqual` true

    it "opacity 100 means fully opaque" do
      assertCloseTo 1e-10 1.0 (opacityToAlpha 100.0)

    it "opacity 1 is 0.01, not 1.0" do
      assertCloseTo 1e-10 0.01 (opacityToAlpha 1.0)
