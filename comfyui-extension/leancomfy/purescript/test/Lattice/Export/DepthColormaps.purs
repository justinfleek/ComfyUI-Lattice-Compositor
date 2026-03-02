-- | Port of depth colormap tests from export-format-contracts.test.ts
-- |
-- | Tests colormap functions: grayscale, viridis, magma, plasma, inferno, turbo
-- | All pure - no FFI or DOM needed.
-- |
-- | 20 tests across 3 describe blocks

module Test.Lattice.Export.DepthColormaps (spec) where

import Prelude

import Lattice.Services.Export.DepthRenderer.Colormaps
  ( getColormapColor
  , applyColormapToValue
  , viridisColormap
  , magmaColormap
  , plasmaColormap
  , infernoColormap
  , turboColormap
  , grayscaleColormap
  , RGB
  )
import Lattice.Services.Export.DepthRenderer.Types
  ( Colormap(..)
  , DepthMapFormat(..)
  , defaultDepthFormatSpec
  , defaultDepthMetadata
  )
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Check that RGB channels are in valid range [0, 255]
isValidRGB :: RGB -> Boolean
isValidRGB c =
  c.r >= 0 && c.r <= 255 &&
  c.g >= 0 && c.g <= 255 &&
  c.b >= 0 && c.b <= 255

assertValidRGB :: RGB -> Aff Unit
assertValidRGB c =
  if isValidRGB c then pure unit
  else fail ("RGB out of range: " <> show c.r <> "," <> show c.g <> "," <> show c.b)

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "DepthColormaps" do
    grayscaleTests
    colormapRangeTests
    colormapDispatchTests

--------------------------------------------------------------------------------
-- 1. Grayscale colormap
--------------------------------------------------------------------------------

grayscaleTests :: Spec Unit
grayscaleTests = do
  describe "grayscale colormap" do

    it "t=0 produces black" do
      let c = grayscaleColormap 0.0
      c.r `shouldEqual` 0
      c.g `shouldEqual` 0
      c.b `shouldEqual` 0

    it "t=1 produces white" do
      let c = grayscaleColormap 1.0
      c.r `shouldEqual` 255
      c.g `shouldEqual` 255
      c.b `shouldEqual` 255

    it "t=0.5 produces mid-gray" do
      let c = grayscaleColormap 0.5
      -- round(0.5 * 255) = 128
      c.r `shouldEqual` 128
      c.g `shouldEqual` 128
      c.b `shouldEqual` 128

    it "grayscale always has r == g == b" do
      let c1 = grayscaleColormap 0.25
      (c1.r == c1.g && c1.g == c1.b) `shouldEqual` true
      let c2 = grayscaleColormap 0.75
      (c2.r == c2.g && c2.g == c2.b) `shouldEqual` true

--------------------------------------------------------------------------------
-- 2. Colormap range validation
--------------------------------------------------------------------------------

colormapRangeTests :: Spec Unit
colormapRangeTests = do
  describe "colormap range validation" do

    it "viridis at t=0 produces valid RGB" do
      assertValidRGB (viridisColormap 0.0)

    it "viridis at t=1 produces valid RGB" do
      assertValidRGB (viridisColormap 1.0)

    it "viridis at t=0.5 produces valid RGB" do
      assertValidRGB (viridisColormap 0.5)

    it "magma at endpoints produces valid RGB" do
      assertValidRGB (magmaColormap 0.0)
      assertValidRGB (magmaColormap 1.0)

    it "plasma at endpoints produces valid RGB" do
      assertValidRGB (plasmaColormap 0.0)
      assertValidRGB (plasmaColormap 1.0)

    it "inferno at endpoints produces valid RGB" do
      assertValidRGB (infernoColormap 0.0)
      assertValidRGB (infernoColormap 1.0)

    it "turbo at endpoints produces valid RGB" do
      assertValidRGB (turboColormap 0.0)
      assertValidRGB (turboColormap 1.0)

    it "all colormaps produce valid RGB at t=0.25" do
      assertValidRGB (viridisColormap 0.25)
      assertValidRGB (magmaColormap 0.25)
      assertValidRGB (plasmaColormap 0.25)
      assertValidRGB (infernoColormap 0.25)
      assertValidRGB (turboColormap 0.25)

    it "all colormaps produce valid RGB at t=0.75" do
      assertValidRGB (viridisColormap 0.75)
      assertValidRGB (magmaColormap 0.75)
      assertValidRGB (plasmaColormap 0.75)
      assertValidRGB (infernoColormap 0.75)
      assertValidRGB (turboColormap 0.75)

--------------------------------------------------------------------------------
-- 3. Colormap dispatch via getColormapColor
--------------------------------------------------------------------------------

colormapDispatchTests :: Spec Unit
colormapDispatchTests = do
  describe "getColormapColor dispatch" do

    it "dispatches to grayscale" do
      let c = getColormapColor 0.0 ColormapGrayscale
      c.r `shouldEqual` 0
      c.g `shouldEqual` 0
      c.b `shouldEqual` 0

    it "dispatches to viridis" do
      let c = getColormapColor 0.0 ColormapViridis
      assertValidRGB c

    it "dispatches to magma" do
      let c = getColormapColor 0.5 ColormapMagma
      assertValidRGB c

    it "dispatches to plasma" do
      let c = getColormapColor 1.0 ColormapPlasma
      assertValidRGB c

    it "dispatches to inferno" do
      let c = getColormapColor 0.5 ColormapInferno
      assertValidRGB c

    it "dispatches to turbo" do
      let c = getColormapColor 0.5 ColormapTurbo
      assertValidRGB c

    it "clamps t below 0" do
      let c = getColormapColor (-0.5) ColormapGrayscale
      c.r `shouldEqual` 0
      c.g `shouldEqual` 0
      c.b `shouldEqual` 0

    it "clamps t above 1" do
      let c = getColormapColor 1.5 ColormapGrayscale
      c.r `shouldEqual` 255
      c.g `shouldEqual` 255
      c.b `shouldEqual` 255
