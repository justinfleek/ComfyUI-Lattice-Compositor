-- | Port of ui/src/__tests__/types/camera.property.test.ts
-- |
-- | Tests camera defaults and presets:
-- |   - defaultDepthOfField properties
-- |   - defaultIris properties
-- |   - defaultHighlight properties
-- |   - defaultCustomViewState properties
-- |   - defaultViewportState properties
-- |   - defaultViewOptions properties
-- |   - cameraPresets (standard focal lengths)
-- |
-- | 18 tests across 8 describe blocks

module Test.Lattice.Types.Camera (spec) where

import Prelude

import Data.Array (length, index)
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Lattice.Primitives (unPositiveFloat, unFiniteFloat, unUnitFloat)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

import Lattice.Camera
  ( WireframeVisibility(..)
  , ViewLayout(..)
  , defaultDepthOfField
  , defaultIris
  , defaultHighlight
  , defaultCustomViewState
  , defaultViewportState
  , defaultViewOptions
  , cameraPresets
  )

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

shouldBeCloseTo :: Number -> Number -> Number -> Aff Unit
shouldBeCloseTo actual expected tolerance =
  let diff = if actual > expected then actual - expected else expected - actual
  in if diff <= tolerance
    then pure unit
    else fail ("Expected " <> show actual <> " to be close to " <> show expected
               <> " (tolerance " <> show tolerance <> ", diff " <> show diff <> ")")

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Camera - Type Tests" do
    depthOfFieldTests
    irisTests
    highlightTests
    customViewStateTests
    viewportStateTests
    viewOptionsTests
    cameraPresetsTests

--------------------------------------------------------------------------------
-- 1. defaultDepthOfField
--------------------------------------------------------------------------------

depthOfFieldTests :: Spec Unit
depthOfFieldTests = do
  describe "defaultDepthOfField" do

    it "should be disabled by default" do
      defaultDepthOfField.enabled `shouldEqual` false

    it "should have correct default values" do
      shouldBeCloseTo (unPositiveFloat defaultDepthOfField.focusDistance) 1500.0 0.01
      shouldBeCloseTo (unPositiveFloat defaultDepthOfField.aperture) 50.0 0.01
      shouldBeCloseTo (unPositiveFloat defaultDepthOfField.fStop) 2.8 0.01
      shouldBeCloseTo (unUnitFloat defaultDepthOfField.blurLevel) 1.0 0.01

    it "should have lockToZoom disabled" do
      defaultDepthOfField.lockToZoom `shouldEqual` false

--------------------------------------------------------------------------------
-- 2. defaultIris
--------------------------------------------------------------------------------

irisTests :: Spec Unit
irisTests = do
  describe "defaultIris" do

    it "should have correct default shape (heptagon)" do
      shouldBeCloseTo (unFiniteFloat defaultIris.shape) 7.0 0.01

    it "should have zero rotation and roundness" do
      shouldBeCloseTo (unFiniteFloat defaultIris.rotation) 0.0 0.01
      shouldBeCloseTo (unUnitFloat defaultIris.roundness) 0.0 0.01

    it "should have aspect ratio of 1.0" do
      shouldBeCloseTo (unFiniteFloat defaultIris.aspectRatio) 1.0 0.01

--------------------------------------------------------------------------------
-- 3. defaultHighlight
--------------------------------------------------------------------------------

highlightTests :: Spec Unit
highlightTests = do
  describe "defaultHighlight" do

    it "should have correct default values" do
      shouldBeCloseTo (unUnitFloat defaultHighlight.gain) 0.0 0.01
      shouldBeCloseTo (unUnitFloat defaultHighlight.threshold) 1.0 0.01
      shouldBeCloseTo (unUnitFloat defaultHighlight.saturation) 1.0 0.01

--------------------------------------------------------------------------------
-- 4. defaultCustomViewState
--------------------------------------------------------------------------------

customViewStateTests :: Spec Unit
customViewStateTests = do
  describe "defaultCustomViewState" do

    it "should have orbit center at origin" do
      shouldBeCloseTo (unFiniteFloat defaultCustomViewState.orbitCenter.x) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat defaultCustomViewState.orbitCenter.y) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat defaultCustomViewState.orbitCenter.z) 0.0 0.01

    it "should have correct orbit distance and angles" do
      shouldBeCloseTo (unPositiveFloat defaultCustomViewState.orbitDistance) 2000.0 0.01
      shouldBeCloseTo (unFiniteFloat defaultCustomViewState.orbitPhi) 60.0 0.01
      shouldBeCloseTo (unFiniteFloat defaultCustomViewState.orbitTheta) 45.0 0.01

    it "should have orthographic zoom of 1.0" do
      shouldBeCloseTo (unPositiveFloat defaultCustomViewState.orthoZoom) 1.0 0.01

--------------------------------------------------------------------------------
-- 5. defaultViewportState
--------------------------------------------------------------------------------

viewportStateTests :: Spec Unit
viewportStateTests = do
  describe "defaultViewportState" do

    it "should default to single view layout" do
      defaultViewportState.layout `shouldEqual` VLOneView

    it "should have active camera as default view" do
      length defaultViewportState.views `shouldEqual` 1

    it "should have active view index 0" do
      defaultViewportState.activeViewIndex `shouldEqual` 0

--------------------------------------------------------------------------------
-- 6. defaultViewOptions
--------------------------------------------------------------------------------

viewOptionsTests :: Spec Unit
viewOptionsTests = do
  describe "defaultViewOptions" do

    it "should show wireframes when selected" do
      defaultViewOptions.cameraWireframes `shouldEqual` WVSelected
      defaultViewOptions.lightWireframes `shouldEqual` WVSelected

    it "should show motion paths and layer elements" do
      defaultViewOptions.showMotionPaths `shouldEqual` true
      defaultViewOptions.showLayerPaths `shouldEqual` true
      defaultViewOptions.showLayerHandles `shouldEqual` true

    it "should show rulers and 3D axes but not grid" do
      defaultViewOptions.showGrid `shouldEqual` false
      defaultViewOptions.showRulers `shouldEqual` true
      defaultViewOptions.show3DReferenceAxes `shouldEqual` true
      defaultViewOptions.showCompositionBounds `shouldEqual` true

    it "should not show safe zones or focal plane" do
      defaultViewOptions.showSafeZones `shouldEqual` false
      defaultViewOptions.showFocalPlane `shouldEqual` false

--------------------------------------------------------------------------------
-- 7. cameraPresets
--------------------------------------------------------------------------------

cameraPresetsTests :: Spec Unit
cameraPresetsTests = do
  describe "cameraPresets" do

    it "should have 8 standard presets" do
      length cameraPresets `shouldEqual` 8

    it "should have increasing focal lengths" do
      -- Check first < last focal length
      case index cameraPresets 0, index cameraPresets 7 of
        Just first, Just last ->
          if unPositiveFloat first.focalLength < unPositiveFloat last.focalLength
            then pure unit
            else fail "Expected first focal length < last focal length"
        _, _ -> fail "Expected at least 8 presets"

    it "should have increasing zoom values (longer focal = more zoom)" do
      case index cameraPresets 0, index cameraPresets 7 of
        Just first, Just last ->
          if unPositiveFloat first.zoom < unPositiveFloat last.zoom
            then pure unit
            else fail "Expected zoom to increase with focal length"
        _, _ -> fail "Expected at least 8 presets"
