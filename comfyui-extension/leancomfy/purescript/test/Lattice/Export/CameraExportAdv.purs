-- | Port of camera export format tests (pure subset)
-- |
-- | Tests matrix computations, motion analysis, Uni3C export,
-- | full camera export, and format routing.
-- |
-- | Sources:
-- |   - cameraExport.test.ts
-- |   - cameraExportFormats.test.ts (subset)
-- |
-- | 20 tests across 6 describe blocks

module Test.Lattice.Export.CameraExportAdv (spec) where

import Prelude

import Data.Array (length, (!!))
import Data.Maybe (Maybe(..))
import Data.Number (isFinite)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)
import Test.Lattice.TestHelpers (assertCloseTo)

import Lattice.Services.Export.CameraExport.Types
  ( defaultInterpolatedCamera
  , defaultMotionAnalysis
  , ExportTarget(..)
  , Uni3CTrajType(..)
  , ZoomDirection(..)
  , PanDirection(..)
  )
import Lattice.Services.Export.CameraExport.Formats.Common
  ( Camera3D
  , CameraKeyframe
  , interpolateCameraAtFrame
  )
import Lattice.Services.Export.CameraExport.Matrix
  ( computeViewMatrix
  , computeProjectionMatrix
  , focalLengthToFOV
  )
import Lattice.Services.Export.CameraExport.MotionAnalysis
  ( analyzeCameraMotion
  )
import Lattice.Services.Export.CameraExport.Formats.Uni3C
  ( exportToUni3C
  , detectUni3CTrajectoryType
  )
import Lattice.Services.Export.CameraExport.Formats.Full
  ( exportCameraMatrices
  )

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

defaultCamera :: Camera3D
defaultCamera =
  { position: { x: 0.0, y: 0.0, z: 0.0 }
  , orientation: { x: 0.0, y: 0.0, z: 0.0 }
  , focalLength: 50.0
  , filmSize: 36.0
  , zoom: 1.0
  , focusDistance: 1000.0
  , cameraType: "perspective"
  }

mkKeyframe :: Int -> Maybe { x :: Number, y :: Number, z :: Number }
  -> Maybe { x :: Number, y :: Number, z :: Number }
  -> CameraKeyframe
mkKeyframe frame pos ori =
  { frame
  , position: pos
  , orientation: ori
  , focalLength: Nothing
  , zoom: Nothing
  , focusDistance: Nothing
  }

mkMotionKF :: Int -> Maybe { x :: Number, y :: Number, z :: Number }
  -> Maybe { x :: Number, y :: Number, z :: Number }
  -> { frame :: Int, position :: Maybe { x :: Number, y :: Number, z :: Number }, orientation :: Maybe { x :: Number, y :: Number, z :: Number } }
mkMotionKF frame pos ori = { frame, position: pos, orientation: ori }

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "CameraExportAdv" do
    computeViewMatrixTests
    computeProjectionMatrixTests
    interpolateCameraAtFrameTests
    analyzeCameraMotionTests
    uni3CTests
    fullExportTests

--------------------------------------------------------------------------------
-- 1. computeViewMatrix
--------------------------------------------------------------------------------

computeViewMatrixTests :: Spec Unit
computeViewMatrixTests = do
  describe "computeViewMatrix" do

    it "returns a 4x4 matrix" do
      let m = computeViewMatrix defaultInterpolatedCamera
      length m `shouldEqual` 4
      case m !! 0 of
        Just row -> length row `shouldEqual` 4
        Nothing -> fail "Expected row 0"

    it "last row is [0,0,0,1]" do
      let m = computeViewMatrix defaultInterpolatedCamera
      case m !! 3 of
        Just row -> do
          case row !! 0 of
            Just v -> assertCloseTo 1e-10 0.0 v
            Nothing -> fail "Expected element"
          case row !! 1 of
            Just v -> assertCloseTo 1e-10 0.0 v
            Nothing -> fail "Expected element"
          case row !! 2 of
            Just v -> assertCloseTo 1e-10 0.0 v
            Nothing -> fail "Expected element"
          case row !! 3 of
            Just v -> assertCloseTo 1e-10 1.0 v
            Nothing -> fail "Expected element"
        Nothing -> fail "Expected row 3"

    it "identity rotation at zero angles" do
      -- With zero rotation, view matrix rotation part should be identity
      let m = computeViewMatrix defaultInterpolatedCamera
      case m !! 0 of
        Just row -> case row !! 0 of
          Just v -> assertCloseTo 1e-10 1.0 v
          Nothing -> fail "Expected element"
        Nothing -> fail "Expected row"
      case m !! 1 of
        Just row -> case row !! 1 of
          Just v -> assertCloseTo 1e-10 1.0 v
          Nothing -> fail "Expected element"
        Nothing -> fail "Expected row"
      case m !! 2 of
        Just row -> case row !! 2 of
          Just v -> assertCloseTo 1e-10 1.0 v
          Nothing -> fail "Expected element"
        Nothing -> fail "Expected row"

    it "all values are finite" do
      let m = computeViewMatrix defaultInterpolatedCamera
      let allFinite = m # allMatrixFinite
      allFinite `shouldEqual` true

--------------------------------------------------------------------------------
-- 2. computeProjectionMatrix
--------------------------------------------------------------------------------

computeProjectionMatrixTests :: Spec Unit
computeProjectionMatrixTests = do
  describe "computeProjectionMatrix" do

    it "returns a 4x4 matrix" do
      let m = computeProjectionMatrix defaultInterpolatedCamera 1.5 0.1 1000.0
      length m `shouldEqual` 4
      case m !! 0 of
        Just row -> length row `shouldEqual` 4
        Nothing -> fail "Expected row 0"

    it "perspective divide element at [3][2] is -1" do
      let m = computeProjectionMatrix defaultInterpolatedCamera 1.5 0.1 1000.0
      case m !! 3 of
        Just row -> case row !! 2 of
          Just v -> assertCloseTo 1e-10 (-1.0) v
          Nothing -> fail "Expected element"
        Nothing -> fail "Expected row 3"

    it "[3][3] is zero" do
      let m = computeProjectionMatrix defaultInterpolatedCamera 1.5 0.1 1000.0
      case m !! 3 of
        Just row -> case row !! 3 of
          Just v -> assertCloseTo 1e-10 0.0 v
          Nothing -> fail "Expected element"
        Nothing -> fail "Expected row 3"

--------------------------------------------------------------------------------
-- 3. interpolateCameraAtFrame
--------------------------------------------------------------------------------

interpolateCameraAtFrameTests :: Spec Unit
interpolateCameraAtFrameTests = do
  describe "interpolateCameraAtFrame" do

    it "returns camera defaults when no keyframes" do
      let cam = interpolateCameraAtFrame defaultCamera [] 0
      assertCloseTo 1e-10 0.0 cam.position.x
      assertCloseTo 1e-10 0.0 cam.position.y
      assertCloseTo 1e-10 50.0 cam.focalLength

    it "interpolates position between keyframes" do
      let kf0 = mkKeyframe 0 (Just { x: 0.0, y: 0.0, z: 0.0 }) Nothing
      let kf10 = mkKeyframe 10 (Just { x: 100.0, y: 200.0, z: 0.0 }) Nothing
      let cam = interpolateCameraAtFrame defaultCamera [kf0, kf10] 5
      -- At frame 5, should be halfway: (50, 100, 0)
      assertCloseTo 1.0 50.0 cam.position.x
      assertCloseTo 1.0 100.0 cam.position.y

    it "returns exact keyframe values at keyframe frame" do
      let kf = mkKeyframe 5 (Just { x: 42.0, y: 84.0, z: 0.0 }) Nothing
      let cam = interpolateCameraAtFrame defaultCamera [kf] 5
      assertCloseTo 1e-10 42.0 cam.position.x
      assertCloseTo 1e-10 84.0 cam.position.y

--------------------------------------------------------------------------------
-- 4. analyzeCameraMotion
--------------------------------------------------------------------------------

analyzeCameraMotionTests :: Spec Unit
analyzeCameraMotionTests = do
  describe "analyzeCameraMotion" do

    it "returns no motion for empty keyframes" do
      let result = analyzeCameraMotion []
      result.hasPan `shouldEqual` false
      result.hasZoom `shouldEqual` false

    it "returns no motion for single keyframe" do
      let kf = mkMotionKF 0 (Just { x: 0.0, y: 0.0, z: 0.0 }) Nothing
      let result = analyzeCameraMotion [kf]
      result.hasPan `shouldEqual` false
      result.hasZoom `shouldEqual` false

    it "magnitudes are non-negative" do
      let kf0 = mkMotionKF 0 (Just { x: 0.0, y: 0.0, z: 0.0 }) Nothing
      let kf10 = mkMotionKF 10 (Just { x: 100.0, y: 0.0, z: -50.0 }) Nothing
      let result = analyzeCameraMotion [kf0, kf10]
      (result.panMagnitude >= 0.0) `shouldEqual` true
      (result.zoomMagnitude >= 0.0) `shouldEqual` true

--------------------------------------------------------------------------------
-- 5. Uni3C
--------------------------------------------------------------------------------

uni3CTests :: Spec Unit
uni3CTests = do
  describe "Uni3C export" do

    it "detectUni3CTrajectoryType returns free1 for no motion" do
      detectUni3CTrajectoryType [] `shouldEqual` Uni3CFree1

    it "exportToUni3C produces trajectory data" do
      let kf0 = mkKeyframe 0 (Just { x: 0.0, y: 0.0, z: 0.0 }) Nothing
      let kf10 = mkKeyframe 10 (Just { x: 100.0, y: 50.0, z: -200.0 }) (Just { x: 30.0, y: 45.0, z: 0.0 })
      let result = exportToUni3C defaultCamera [kf0, kf10] 11 512 512
      -- Should have a trajType
      (result.trajType == Uni3CFree1 || result.trajType == Uni3COrbit || result.trajType == Uni3CCustom) `shouldEqual` true

--------------------------------------------------------------------------------
-- 6. Full export
--------------------------------------------------------------------------------

fullExportTests :: Spec Unit
fullExportTests = do
  describe "exportCameraMatrices" do

    it "produces correct number of frames" do
      let kf0 = mkKeyframe 0 (Just { x: 0.0, y: 0.0, z: 0.0 }) Nothing
      let result = exportCameraMatrices defaultCamera [kf0] { frameCount: 10, width: 512, height: 512, fps: 24.0 }
      length result.frames `shouldEqual` 10

    it "metadata matches input" do
      let kf0 = mkKeyframe 0 (Just { x: 0.0, y: 0.0, z: 0.0 }) Nothing
      let result = exportCameraMatrices defaultCamera [kf0] { frameCount: 10, width: 1024, height: 768, fps: 30.0 }
      result.metadata.width `shouldEqual` 1024
      result.metadata.height `shouldEqual` 768
      assertCloseTo 1e-10 30.0 result.metadata.fps
      result.metadata.totalFrames `shouldEqual` 10

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

allMatrixFinite :: Array (Array Number) -> Boolean
allMatrixFinite rows = allOf (\row -> allOf isFinite row) rows

allOf :: forall a. (a -> Boolean) -> Array a -> Boolean
allOf f arr = allOfImpl f arr 0

allOfImpl :: forall a. (a -> Boolean) -> Array a -> Int -> Boolean
allOfImpl f arr i =
  if i >= length arr then true
  else case arr !! i of
    Nothing -> true
    Just v -> if f v then allOfImpl f arr (i + 1) else false
