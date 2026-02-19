-- |
-- Module      : Lattice.State.CameraSpec
-- Description : Test suite for camera state management
--

module Lattice.State.CameraSpec (spec) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import Lattice.State.Camera
  ( framesEqual
  , safeFrame
  , allCameras
  , getCamera
  , getCameraKeyframes
  , activeCamera
  , CameraState(..)
  , CameraKeyframe(..)
  , ViewportState(..)
  , ViewOptions(..)
  )
import Lattice.Types.LayerData3D
  ( Camera3D(..)
  , CameraType(..)
  )
import Lattice.Types.Primitives (Vec3(..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertEqual)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // test // helpers
-- ════════════════════════════════════════════════════════════════════════════

createTestCamera :: Text -> Camera3D
createTestCamera id_ =
  Camera3D
    { camera3DType = CameraTypeTwoNode
    , camera3DPosition = Vec3 0.0 0.0 (-1500.0)
    , camera3DPointOfInterest = Vec3 0.0 0.0 0.0
    , camera3DZoom = 1778.0
    , camera3DDepthOfField = False
    , camera3DFocusDistance = 1500.0
    , camera3DAperture = 50.0
    , camera3DBlurLevel = 1.0
    , camera3DXRotation = 0.0
    , camera3DYRotation = 0.0
    , camera3DZRotation = 0.0
    }

createTestCameraState :: HashMap Text Camera3D -> HashMap Text [CameraKeyframe] -> Maybe Text -> CameraState
createTestCameraState cameras keyframes mActiveId =
  CameraState
    { cameraStateCameras = cameras
    , cameraStateCameraKeyframes = keyframes
    , cameraStateActiveCameraId = mActiveId
    , cameraStateViewportState = ViewportState "1-view" 0
    , cameraStateViewOptions = ViewOptions "selected" False
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Camera"
    [ testGroup
        "framesEqual"
        [ testCase "framesEqual - returns True for equal finite numbers" $ do
            assertBool "Equal frames should return True" (framesEqual 10.0 10.0)
        , testCase "framesEqual - returns False for different finite numbers" $ do
            assertBool "Different frames should return False" (not (framesEqual 10.0 20.0))
        , testCase "framesEqual - returns False for NaN values" $ do
            assertBool "NaN should return False" (not (framesEqual (0.0 / 0.0) 10.0))
            assertBool "NaN should return False" (not (framesEqual 10.0 (0.0 / 0.0)))
        , testCase "framesEqual - returns False for Infinity values" $ do
            assertBool "Infinity should return False" (not (framesEqual (1.0 / 0.0) 10.0))
            assertBool "Infinity should return False" (not (framesEqual 10.0 (1.0 / 0.0)))
        ]
    , testGroup
        "safeFrame"
        [ testCase "safeFrame - returns frame when valid" $ do
            let result = safeFrame (Just 10.0) 0.0
            assertEqual "Should return valid frame" 10.0 result
        , testCase "safeFrame - returns fallback when Nothing" $ do
            let result = safeFrame Nothing 5.0
            assertEqual "Should return fallback" 5.0 result
        , testCase "safeFrame - returns fallback when NaN" $ do
            let result = safeFrame (Just (0.0 / 0.0)) 5.0
            assertEqual "Should return fallback for NaN" 5.0 result
        , testCase "safeFrame - returns fallback when Infinity" $ do
            let result = safeFrame (Just (1.0 / 0.0)) 5.0
            assertEqual "Should return fallback for Infinity" 5.0 result
        ]
    , testGroup
        "allCameras"
        [ testCase "allCameras - returns empty list for empty map" $ do
            let cameras = HM.empty :: HashMap Text Camera3D
            let result = allCameras cameras
            assertEqual "Should return empty list" [] result
        , testCase "allCameras - returns all cameras" $ do
            let camera1 = createTestCamera "camera1"
            let camera2 = createTestCamera "camera2"
            let cameras = HM.fromList [("camera1", camera1), ("camera2", camera2)]
            let result = allCameras cameras
            assertEqual "Should return 2 cameras" 2 (length result)
        ]
    , testGroup
        "getCamera"
        [ testCase "getCamera - returns Nothing for non-existent camera" $ do
            let cameras = HM.empty :: HashMap Text Camera3D
            let result = getCamera "nonexistent" cameras
            assertEqual "Should return Nothing" Nothing result
        , testCase "getCamera - returns camera when exists" $ do
            let camera1 = createTestCamera "camera1"
            let cameras = HM.fromList [("camera1", camera1)]
            let result = getCamera "camera1" cameras
            assertBool "Should return camera" (result == Just camera1)
        ]
    , testGroup
        "getCameraKeyframes"
        [ testCase "getCameraKeyframes - returns empty list for non-existent camera" $ do
            let keyframes = HM.empty :: HashMap Text [CameraKeyframe]
            let result = getCameraKeyframes "nonexistent" keyframes
            assertEqual "Should return empty list" [] result
        , testCase "getCameraKeyframes - returns keyframes when exists" $ do
            let kf1 = CameraKeyframe 10.0
            let kf2 = CameraKeyframe 20.0
            let keyframes = HM.fromList [("camera1", [kf1, kf2])]
            let result = getCameraKeyframes "camera1" keyframes
            assertEqual "Should return 2 keyframes" 2 (length result)
        ]
    , testGroup
        "activeCamera"
        [ testCase "activeCamera - returns Nothing when no active ID" $ do
            let cameras = HM.fromList [("camera1", createTestCamera "camera1")]
            let result = activeCamera Nothing cameras
            assertEqual "Should return Nothing" Nothing result
        , testCase "activeCamera - returns Nothing when active ID doesn't exist" $ do
            let cameras = HM.fromList [("camera1", createTestCamera "camera1")]
            let result = activeCamera (Just "nonexistent") cameras
            assertEqual "Should return Nothing" Nothing result
        , testCase "activeCamera - returns camera when active ID exists" $ do
            let camera1 = createTestCamera "camera1"
            let cameras = HM.fromList [("camera1", camera1)]
            let result = activeCamera (Just "camera1") cameras
            assertBool "Should return camera" (result == Just camera1)
        ]
    ]
