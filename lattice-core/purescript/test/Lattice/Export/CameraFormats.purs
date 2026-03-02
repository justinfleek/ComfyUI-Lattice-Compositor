-- | Port of camera export format tests
-- |
-- | Tests camera interpolation, matrix computation, motion analysis,
-- | and format-specific export (MotionCtrl, Wan22, CameraCtrl).
-- |
-- | Sources:
-- |   - cameraExportFormats.test.ts
-- |   - cameraExportFormats.property.test.ts
-- |   - cameraExportFormats.adversarial.test.ts
-- |
-- | 45 tests across 7 describe blocks

module Test.Lattice.Export.CameraFormats (spec) where

import Prelude

import Data.Array (length, (!!))
import Data.Maybe (Maybe(..), isJust)
import Data.Number (pi, abs, sqrt, isFinite)

import Lattice.Services.Export.CameraExport.Types
  ( InterpolatedCamera
  , Vec3
  , CameraMotionAnalysis
  , PanDirection(..)
  , ZoomDirection(..)
  , OrbitDirection(..)
  , MotionCtrlSVDPreset(..)
  , Wan22CameraMotion(..)
  , CameraCtrlMotionType(..)
  , defaultInterpolatedCamera
  , defaultMotionAnalysis
  )
import Lattice.Services.Export.CameraExport.Interpolation
  ( lerp
  , lerpAngle
  , normalizeAngle
  )
import Lattice.Services.Export.CameraExport.Matrix
  ( computeViewMatrix
  , computeProjectionMatrix
  , focalLengthToFOV
  , degreesToRadians
  )
import Lattice.Services.Export.CameraExport.MotionAnalysis
  ( analyzeCameraMotion
  , detectDominantMotion
  , panThreshold
  , zoomThreshold
  , orbitThreshold
  )
import Lattice.Services.Export.CameraExport.Formats.MotionCtrl
  ( exportToMotionCtrl
  , detectMotionCtrlSVDPreset
  )
import Lattice.Services.Export.CameraExport.Formats.Wan22
  ( mapToWan22FunCamera
  )
import Lattice.Services.Export.CameraExport.Formats.Common
  ( Camera3D
  , CameraKeyframe
  , interpolateCameraAtFrame
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)
import Test.Lattice.TestHelpers (assertCloseTo)

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

mkCamera :: Camera3D
mkCamera =
  { position: { x: 0.0, y: 0.0, z: (-500.0) }
  , orientation: { x: 0.0, y: 0.0, z: 0.0 }
  , focalLength: 50.0
  , filmSize: 36.0
  , zoom: 1.0
  , focusDistance: 1000.0
  , cameraType: "perspective"
  }

mkKeyframe :: Int -> CameraKeyframe
mkKeyframe frame =
  { frame
  , position: Nothing
  , orientation: Nothing
  , focalLength: Nothing
  , zoom: Nothing
  , focusDistance: Nothing
  }

mkKeyframeWithPos :: Int -> Vec3 -> CameraKeyframe
mkKeyframeWithPos frame pos =
  (mkKeyframe frame) { position = Just pos }

mkKeyframeWithOri :: Int -> Vec3 -> CameraKeyframe
mkKeyframeWithOri frame ori =
  (mkKeyframe frame) { orientation = Just ori }

mkKeyframeWithPosOri :: Int -> Vec3 -> Vec3 -> CameraKeyframe
mkKeyframeWithPosOri frame pos ori =
  (mkKeyframe frame) { position = Just pos, orientation = Just ori }

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "CameraFormats" do
    interpolationMathTests
    interpolationTests
    matrixTests
    motionAnalysisTests
    motionCtrlTests
    wan22Tests
    adversarialTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. Interpolation math utilities
-- ────────────────────────────────────────────────────────────────────────────

interpolationMathTests :: Spec Unit
interpolationMathTests = do
  describe "interpolation math" do

    it "lerp at t=0 returns start" do
      assertCloseTo (1e-10) 10.0 (lerp 10.0 20.0 0.0)

    it "lerp at t=1 returns end" do
      assertCloseTo (1e-10) 20.0 (lerp 10.0 20.0 1.0)

    it "lerp at t=0.5 returns midpoint" do
      assertCloseTo (1e-10) 15.0 (lerp 10.0 20.0 0.5)

    it "normalizeAngle wraps negative to [0,360)" do
      let a = normalizeAngle (-10.0)
      (a >= 0.0 && a < 360.0) `shouldEqual` true
      assertCloseTo (1e-5) 350.0 a

    it "normalizeAngle wraps >360 to [0,360)" do
      let a = normalizeAngle 370.0
      assertCloseTo (1e-5) 10.0 a

    it "lerpAngle takes shortest path across 360 boundary" do
      let a = lerpAngle 350.0 10.0 0.5
      -- Shortest path: 350 -> 0 -> 10, midpoint at 0
      assertCloseTo (5.0) 0.0 a

    it "degreesToRadians converts correctly" do
      assertCloseTo (1e-10) pi (degreesToRadians 180.0)
      assertCloseTo (1e-10) (pi / 2.0) (degreesToRadians 90.0)

    it "focalLengthToFOV returns valid FOV" do
      let fov = focalLengthToFOV 50.0 36.0
      (fov > 0.0 && fov < pi) `shouldEqual` true

    it "focalLengthToFOV guards against invalid focal" do
      let fov = focalLengthToFOV 0.0 36.0
      (fov > 0.0 && fov < pi) `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 2. Camera interpolation
-- ────────────────────────────────────────────────────────────────────────────

interpolationTests :: Spec Unit
interpolationTests = do
  describe "camera interpolation" do

    it "returns camera defaults with no keyframes" do
      let result = interpolateCameraAtFrame mkCamera [] 5
      assertCloseTo (1e-10) mkCamera.position.x result.position.x
      assertCloseTo (1e-10) mkCamera.position.z result.position.z

    it "returns keyframe values at keyframe frame" do
      let kf = mkKeyframeWithPos 5 { x: 100.0, y: 0.0, z: (-500.0) }
      let result = interpolateCameraAtFrame mkCamera [kf] 5
      assertCloseTo (1e-5) 100.0 result.position.x

    it "interpolates position between two keyframes" do
      let kf1 = mkKeyframeWithPos 0 { x: 0.0, y: 0.0, z: (-500.0) }
      let kf2 = mkKeyframeWithPos 10 { x: 100.0, y: 0.0, z: (-500.0) }
      let result = interpolateCameraAtFrame mkCamera [kf1, kf2] 5
      assertCloseTo (1.0) 50.0 result.position.x

    it "clamps before first keyframe" do
      let kf = mkKeyframeWithPos 5 { x: 100.0, y: 0.0, z: (-500.0) }
      let result = interpolateCameraAtFrame mkCamera [kf] 0
      -- Before only keyframe, should use that keyframe's value
      assertCloseTo (1e-5) 100.0 result.position.x

    it "clamps after last keyframe" do
      let kf = mkKeyframeWithPos 5 { x: 100.0, y: 0.0, z: (-500.0) }
      let result = interpolateCameraAtFrame mkCamera [kf] 10
      assertCloseTo (1e-5) 100.0 result.position.x

    it "uses camera default for missing keyframe fields" do
      let kf = mkKeyframe 5  -- no position set
      let result = interpolateCameraAtFrame mkCamera [kf] 5
      assertCloseTo (1e-5) mkCamera.position.x result.position.x

-- ────────────────────────────────────────────────────────────────────────────
-- 3. Matrix computation
-- ────────────────────────────────────────────────────────────────────────────

matrixTests :: Spec Unit
matrixTests = do
  describe "matrix computation" do

    it "view matrix is 4x4" do
      let m = computeViewMatrix defaultInterpolatedCamera
      length m `shouldEqual` 4
      case m !! 0 of
        Just row -> length row `shouldEqual` 4
        Nothing -> fail "Expected 4x4 matrix"

    it "view matrix at identity produces identity-like result" do
      let cam = defaultInterpolatedCamera
      let m = computeViewMatrix cam
      -- At origin with no rotation, should be close to identity
      case m !! 3 of
        Just row -> do
          assertCloseTo (1e-10) 0.0 (unsafeIndex row 0)
          assertCloseTo (1e-10) 0.0 (unsafeIndex row 1)
          assertCloseTo (1e-10) 0.0 (unsafeIndex row 2)
          assertCloseTo (1e-10) 1.0 (unsafeIndex row 3)
        Nothing -> fail "Expected row 3"

    it "projection matrix is 4x4" do
      let m = computeProjectionMatrix defaultInterpolatedCamera 1.777 0.1 1000.0
      length m `shouldEqual` 4
      case m !! 0 of
        Just row -> length row `shouldEqual` 4
        Nothing -> fail "Expected 4x4 matrix"

    it "projection matrix has finite values" do
      let m = computeProjectionMatrix defaultInterpolatedCamera 1.777 0.1 1000.0
      let allFinite = checkAllFinite m
      allFinite `shouldEqual` true

    it "view matrix with rotation has finite values" do
      let cam = defaultInterpolatedCamera { rotation = { x: 30.0, y: 45.0, z: 0.0 } }
      let m = computeViewMatrix cam
      let allFinite = checkAllFinite m
      allFinite `shouldEqual` true

    it "view matrix with translation differs from identity" do
      let cam = defaultInterpolatedCamera { position = { x: 100.0, y: 50.0, z: (-500.0) } }
      let m = computeViewMatrix cam
      -- Translation column should be non-zero
      let tx = unsafeIndex2 m 0 3
      let ty = unsafeIndex2 m 1 3
      (abs tx > 0.01 || abs ty > 0.01) `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 4. Motion analysis
-- ────────────────────────────────────────────────────────────────────────────

motionAnalysisTests :: Spec Unit
motionAnalysisTests = do
  describe "motion analysis" do

    it "empty keyframes returns no motion" do
      let result = analyzeCameraMotion []
      result.hasPan `shouldEqual` false
      result.hasZoom `shouldEqual` false
      result.hasOrbit `shouldEqual` false

    it "single keyframe returns no motion" do
      let result = analyzeCameraMotion [{ frame: 0, position: Nothing, orientation: Nothing }]
      result.hasPan `shouldEqual` false
      result.hasZoom `shouldEqual` false

    it "detects zoom in (negative deltaZ)" do
      -- Source convention: deltaZ < 0 → ZoomIn
      let kfs =
            [ { frame: 0, position: Just { x: 0.0, y: 0.0, z: 0.0 }, orientation: Nothing }
            , { frame: 10, position: Just { x: 0.0, y: 0.0, z: (-100.0) }, orientation: Nothing }
            ]
      let result = analyzeCameraMotion kfs
      result.hasZoom `shouldEqual` true
      result.zoomDirection `shouldEqual` Just ZoomIn

    it "detects zoom out (positive deltaZ)" do
      -- Source convention: deltaZ > 0 → ZoomOut
      let kfs =
            [ { frame: 0, position: Just { x: 0.0, y: 0.0, z: (-100.0) }, orientation: Nothing }
            , { frame: 10, position: Just { x: 0.0, y: 0.0, z: 0.0 }, orientation: Nothing }
            ]
      let result = analyzeCameraMotion kfs
      result.hasZoom `shouldEqual` true
      result.zoomDirection `shouldEqual` Just ZoomOut

    it "detects pan from horizontal movement" do
      let kfs =
            [ { frame: 0, position: Just { x: 0.0, y: 0.0, z: (-500.0) }, orientation: Nothing }
            , { frame: 10, position: Just { x: 100.0, y: 0.0, z: (-500.0) }, orientation: Nothing }
            ]
      let result = analyzeCameraMotion kfs
      result.hasPan `shouldEqual` true

    it "detectDominantMotion returns static for no motion" do
      detectDominantMotion defaultMotionAnalysis `shouldEqual` "static"

-- ────────────────────────────────────────────────────────────────────────────
-- 5. MotionCtrl export
-- ────────────────────────────────────────────────────────────────────────────

motionCtrlTests :: Spec Unit
motionCtrlTests = do
  describe "MotionCtrl export" do

    it "exports correct number of poses" do
      let result = exportToMotionCtrl mkCamera [] 24
      length result.cameraPoses `shouldEqual` 24

    it "exports single pose for frame count 1" do
      let result = exportToMotionCtrl mkCamera [] 1
      length result.cameraPoses `shouldEqual` 1

    it "each pose has 4x4 RT matrix" do
      let result = exportToMotionCtrl mkCamera [] 5
      case result.cameraPoses !! 0 of
        Just pose -> do
          length pose.rt `shouldEqual` 4
          case pose.rt !! 0 of
            Just row -> length row `shouldEqual` 4
            Nothing -> fail "Expected 4-element row"
        Nothing -> fail "Expected at least one pose"

    it "detectMotionCtrlSVDPreset returns static for empty" do
      detectMotionCtrlSVDPreset [] `shouldEqual` SVDStatic

    it "detectMotionCtrlSVDPreset returns static for single" do
      detectMotionCtrlSVDPreset [mkKeyframe 0] `shouldEqual` SVDStatic

    it "detectMotionCtrlSVDPreset detects zoom in" do
      let kfs =
            [ mkKeyframeWithPos 0 { x: 0.0, y: 0.0, z: (-500.0) }
            , mkKeyframeWithPos 10 { x: 0.0, y: 0.0, z: (-400.0) }
            ]
      detectMotionCtrlSVDPreset kfs `shouldEqual` SVDZoomIn

    it "detectMotionCtrlSVDPreset detects zoom out" do
      let kfs =
            [ mkKeyframeWithPos 0 { x: 0.0, y: 0.0, z: (-500.0) }
            , mkKeyframeWithPos 10 { x: 0.0, y: 0.0, z: (-600.0) }
            ]
      detectMotionCtrlSVDPreset kfs `shouldEqual` SVDZoomOut

-- ────────────────────────────────────────────────────────────────────────────
-- 6. Wan 2.2 Fun Camera export
-- ────────────────────────────────────────────────────────────────────────────

wan22Tests :: Spec Unit
wan22Tests = do
  describe "Wan22 FunCamera" do

    it "returns Static for no keyframes" do
      let result = mapToWan22FunCamera []
      result.cameraMotion `shouldEqual` Wan22Static

    it "returns Static for single keyframe" do
      let result = mapToWan22FunCamera [mkKeyframe 0]
      result.cameraMotion `shouldEqual` Wan22Static

    it "detects zoom in" do
      -- analyzeCameraMotion convention: deltaZ < 0 → ZoomIn
      let kfs =
            [ mkKeyframeWithPos 0 { x: 0.0, y: 0.0, z: 0.0 }
            , mkKeyframeWithPos 10 { x: 0.0, y: 0.0, z: (-100.0) }
            ]
      let result = mapToWan22FunCamera kfs
      result.cameraMotion `shouldEqual` Wan22ZoomIn

    it "detects pan right" do
      let kfs =
            [ mkKeyframeWithPos 0 { x: 0.0, y: 0.0, z: (-500.0) }
            , mkKeyframeWithPos 10 { x: 100.0, y: 0.0, z: (-500.0) }
            ]
      let result = mapToWan22FunCamera kfs
      result.cameraMotion `shouldEqual` Wan22PanRight

-- ────────────────────────────────────────────────────────────────────────────
-- 7. Adversarial / edge cases
-- ────────────────────────────────────────────────────────────────────────────

adversarialTests :: Spec Unit
adversarialTests = do
  describe "adversarial edge cases" do

    it "keyframes at same frame does not crash" do
      let kfs =
            [ mkKeyframeWithPos 5 { x: 0.0, y: 0.0, z: (-500.0) }
            , mkKeyframeWithPos 5 { x: 100.0, y: 0.0, z: (-500.0) }
            ]
      let result = interpolateCameraAtFrame mkCamera kfs 5
      isFinite result.position.x `shouldEqual` true

    it "projection with zero aspect uses fallback" do
      let m = computeProjectionMatrix defaultInterpolatedCamera 0.0 0.1 1000.0
      let allFinite = checkAllFinite m
      allFinite `shouldEqual` true

    it "view matrix guards against extreme positions" do
      let cam = defaultInterpolatedCamera { position = { x: 1.0e10, y: 1.0e10, z: 1.0e10 } }
      let m = computeViewMatrix cam
      let allFinite = checkAllFinite m
      allFinite `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- Internal helpers
-- ────────────────────────────────────────────────────────────────────────────

unsafeIndex :: Array Number -> Int -> Number
unsafeIndex arr i = case arr !! i of
  Just v -> v
  Nothing -> 0.0

unsafeIndex2 :: Array (Array Number) -> Int -> Int -> Number
unsafeIndex2 m r c = case m !! r of
  Just row -> unsafeIndex row c
  Nothing -> 0.0

checkAllFinite :: Array (Array Number) -> Boolean
checkAllFinite m =
  let
    checkRow row = case row of
      [] -> true
      _ -> allFinite row
  in
    allOf checkRow m

allFinite :: Array Number -> Boolean
allFinite arr = allOf isFinite arr

allOf :: forall a. (a -> Boolean) -> Array a -> Boolean
allOf f arr = case arr !! 0 of
  Nothing -> true
  Just _ -> allOfImpl f arr 0

allOfImpl :: forall a. (a -> Boolean) -> Array a -> Int -> Boolean
allOfImpl f arr i =
  if i >= length arr then true
  else case arr !! i of
    Nothing -> true
    Just v -> if f v then allOfImpl f arr (i + 1) else false
