-- | Port of ui/src/__tests__/types/camera.property.test.ts
-- |
-- | Tests camera factory functions:
-- |   - createDefaultCamera (position, lens, DoF, iris, highlight)
-- |   - defaultViewportState (layout, views, custom views)
-- |   - defaultViewOptions (wireframes, paths, grid)
-- |   - cameraPresets (8 presets, monotonic focal length)
-- |   - Determinism
-- |
-- | 35 tests across 4 describe blocks

module Test.Lattice.Types.CameraProps (spec) where

import Prelude

import Data.Array (length, all, sortBy)
import Data.Maybe (Maybe(..))
import Data.Ordering (Ordering(..))
import Effect.Aff (Aff)
import Lattice.Primitives
  ( NonEmptyString(..), mkNonEmptyString
  , unNonEmptyString, unPositiveFloat, unFiniteFloat, unUnitFloat
  )
import Lattice.Camera
  ( createDefaultCamera
  , defaultViewportState
  , defaultViewOptions
  , cameraPresets
  , CameraType(..)
  , AutoOrientMode(..)
  , MeasureFilmSize(..)
  , WireframeVisibility(..)
  , ViewLayout(..)
  , ViewType(..)
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

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

nes :: String -> NonEmptyString
nes s = case mkNonEmptyString s of
  Just v -> v
  Nothing -> NonEmptyString "error"

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Camera Properties" do
    cameraFactoryTests
    viewportTests
    viewOptionsTests
    presetTests

--------------------------------------------------------------------------------
-- 1. createDefaultCamera
--------------------------------------------------------------------------------

cameraFactoryTests :: Spec Unit
cameraFactoryTests = do
  describe "createDefaultCamera" do
    let cam = createDefaultCamera (nes "cam-1") 1920.0 1080.0

    it "has correct id" do
      unNonEmptyString cam.id `shouldEqual` "cam-1"

    it "name is 'Camera 1'" do
      unNonEmptyString cam.name `shouldEqual` "Camera 1"

    it "type is two-node" do
      cam.cameraType `shouldEqual` CTTwoNode

    it "position.x = compWidth / 2" do
      shouldBeCloseTo (unFiniteFloat cam.position.x) 960.0 0.01

    it "position.y = compHeight / 2" do
      shouldBeCloseTo (unFiniteFloat cam.position.y) 540.0 0.01

    it "position.z = -1500" do
      shouldBeCloseTo (unFiniteFloat cam.position.z) (-1500.0) 0.01

    it "pointOfInterest centered at (w/2, h/2, 0)" do
      shouldBeCloseTo (unFiniteFloat cam.pointOfInterest.x) 960.0 0.01
      shouldBeCloseTo (unFiniteFloat cam.pointOfInterest.y) 540.0 0.01
      shouldBeCloseTo (unFiniteFloat cam.pointOfInterest.z) 0.0 0.01

    it "orientation is (0, 0, 0)" do
      shouldBeCloseTo (unFiniteFloat cam.orientation.x) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat cam.orientation.y) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat cam.orientation.z) 0.0 0.01

    it "individual rotations are 0" do
      shouldBeCloseTo (unFiniteFloat cam.xRotation) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat cam.yRotation) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat cam.zRotation) 0.0 0.01

    it "zoom is 1778 (50mm equivalent)" do
      shouldBeCloseTo (unPositiveFloat cam.zoom) 1778.0 0.01

    it "focalLength is 50mm" do
      shouldBeCloseTo (unPositiveFloat cam.focalLength) 50.0 0.01

    it "angleOfView is 39.6 degrees" do
      shouldBeCloseTo (unPositiveFloat cam.angleOfView) 39.6 0.01

    it "filmSize is 36mm (full frame)" do
      shouldBeCloseTo (unPositiveFloat cam.filmSize) 36.0 0.01

    it "measureFilmSize is horizontal" do
      cam.measureFilmSize `shouldEqual` MFSHorizontal

    it "depthOfField defaults (disabled)" do
      cam.depthOfField.enabled `shouldEqual` false
      shouldBeCloseTo (unPositiveFloat cam.depthOfField.focusDistance) 1500.0 0.01
      shouldBeCloseTo (unPositiveFloat cam.depthOfField.aperture) 50.0 0.01
      shouldBeCloseTo (unPositiveFloat cam.depthOfField.fStop) 2.8 0.01
      shouldBeCloseTo (unUnitFloat cam.depthOfField.blurLevel) 1.0 0.01
      cam.depthOfField.lockToZoom `shouldEqual` false

    it "iris defaults" do
      shouldBeCloseTo (unFiniteFloat cam.iris.shape) 7.0 0.01
      shouldBeCloseTo (unFiniteFloat cam.iris.rotation) 0.0 0.01
      shouldBeCloseTo (unUnitFloat cam.iris.roundness) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat cam.iris.aspectRatio) 1.0 0.01
      shouldBeCloseTo (unUnitFloat cam.iris.diffractionFringe) 0.0 0.01

    it "highlight defaults" do
      shouldBeCloseTo (unUnitFloat cam.highlight.gain) 0.0 0.01
      shouldBeCloseTo (unUnitFloat cam.highlight.threshold) 1.0 0.01
      shouldBeCloseTo (unUnitFloat cam.highlight.saturation) 1.0 0.01

    it "autoOrient is off" do
      cam.autoOrient `shouldEqual` AOMOff

    it "clip planes valid" do
      shouldBeCloseTo (unPositiveFloat cam.nearClip) 1.0 0.01
      shouldBeCloseTo (unPositiveFloat cam.farClip) 10000.0 0.01

    it "is deterministic" do
      let cam1 = createDefaultCamera (nes "cam-d") 1920.0 1080.0
      let cam2 = createDefaultCamera (nes "cam-d") 1920.0 1080.0
      unNonEmptyString cam1.name `shouldEqual` unNonEmptyString cam2.name
      cam1.cameraType `shouldEqual` cam2.cameraType
      unPositiveFloat cam1.zoom `shouldEqual` unPositiveFloat cam2.zoom

--------------------------------------------------------------------------------
-- 2. defaultViewportState
--------------------------------------------------------------------------------

viewportTests :: Spec Unit
viewportTests = do
  describe "defaultViewportState" do
    let vs = defaultViewportState

    it "layout is 1-view" do
      vs.layout `shouldEqual` VLOneView

    it "views contains active-camera" do
      length vs.views `shouldEqual` 1

    it "custom-1 defaults (phi=60, theta=45)" do
      shouldBeCloseTo (unFiniteFloat vs.customViews.custom1.orbitPhi) 60.0 0.01
      shouldBeCloseTo (unFiniteFloat vs.customViews.custom1.orbitTheta) 45.0 0.01

    it "custom-2 defaults (phi=90, theta=0)" do
      shouldBeCloseTo (unFiniteFloat vs.customViews.custom2.orbitPhi) 90.0 0.01
      shouldBeCloseTo (unFiniteFloat vs.customViews.custom2.orbitTheta) 0.0 0.01

    it "custom-3 defaults (phi=0, theta=0)" do
      shouldBeCloseTo (unFiniteFloat vs.customViews.custom3.orbitPhi) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat vs.customViews.custom3.orbitTheta) 0.0 0.01

    it "activeViewIndex is 0" do
      vs.activeViewIndex `shouldEqual` 0

    it "is deterministic" do
      let vs1 = defaultViewportState
      let vs2 = defaultViewportState
      vs1.layout `shouldEqual` vs2.layout
      vs1.activeViewIndex `shouldEqual` vs2.activeViewIndex

--------------------------------------------------------------------------------
-- 3. defaultViewOptions
--------------------------------------------------------------------------------

viewOptionsTests :: Spec Unit
viewOptionsTests = do
  describe "defaultViewOptions" do
    let vo = defaultViewOptions

    it "cameraWireframes is selected" do
      vo.cameraWireframes `shouldEqual` WVSelected

    it "lightWireframes is selected" do
      vo.lightWireframes `shouldEqual` WVSelected

    it "showMotionPaths is true" do
      vo.showMotionPaths `shouldEqual` true

    it "showGrid is false" do
      vo.showGrid `shouldEqual` false

    it "showRulers is true" do
      vo.showRulers `shouldEqual` true

    it "show3DReferenceAxes is true" do
      vo.show3DReferenceAxes `shouldEqual` true

    it "showFocalPlane is false" do
      vo.showFocalPlane `shouldEqual` false

    it "is deterministic" do
      let vo1 = defaultViewOptions
      let vo2 = defaultViewOptions
      vo1.showMotionPaths `shouldEqual` vo2.showMotionPaths
      vo1.showGrid `shouldEqual` vo2.showGrid

--------------------------------------------------------------------------------
-- 4. cameraPresets
--------------------------------------------------------------------------------

presetTests :: Spec Unit
presetTests = do
  describe "cameraPresets" do

    it "has 8 presets" do
      length cameraPresets `shouldEqual` 8

    it "all presets have positive focalLength" do
      let allPositive = all (\p -> unPositiveFloat p.focalLength > 0.0) cameraPresets
      allPositive `shouldEqual` true

    it "all presets have positive angleOfView" do
      let allPositive = all (\p -> unPositiveFloat p.angleOfView > 0.0) cameraPresets
      allPositive `shouldEqual` true

    it "all presets have positive zoom" do
      let allPositive = all (\p -> unPositiveFloat p.zoom > 0.0) cameraPresets
      allPositive `shouldEqual` true

    it "focalLength increases monotonically" do
      -- Presets are ordered wider to telephoto
      let fls = map (\p -> unPositiveFloat p.focalLength) cameraPresets
      let sorted = sortBy compare fls
      fls `shouldEqual` sorted

    it "angleOfView decreases as focalLength increases" do
      -- First preset should have widest angle
      case cameraPresets of
        [] -> fail "No presets"
        [_] -> pure unit
        _ -> do
          let aovs = map (\p -> unPositiveFloat p.angleOfView) cameraPresets
          let sortedDesc = sortBy (flip compare) aovs
          aovs `shouldEqual` sortedDesc
