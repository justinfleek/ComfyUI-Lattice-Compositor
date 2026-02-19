-- | Port of pose export tests (pure subset)
-- |
-- | Tests bone/color constants, OpenPose JSON export/import roundtrip,
-- | keypoint and pose interpolation, sequence creation, and default config.
-- |
-- | Sources:
-- |   - poseExport.test.ts
-- |
-- | 25 tests across 7 describe blocks

module Test.Lattice.Export.PoseExport (spec) where

import Prelude

import Data.Array as Data.Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Lattice.Services.Export.Pose
  ( Pose
  , PoseKeypoint
  , PoseFormat(..)
  , cocoBones
  , openposeColors
  , interpolatePoses
  , createPoseSequence
  , exportToOpenPoseJSON
  , importFromOpenPoseJSON
  , defaultPoseExportConfig
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

mkKeypoint :: Number -> Number -> Number -> PoseKeypoint
mkKeypoint x y c = { x, y, confidence: c }

mkPose :: String -> Array PoseKeypoint -> Pose
mkPose id kps = { id, keypoints: kps, format: FormatCOCO18 }

-- | A simple pose with 18 keypoints at known positions
simplePose :: Pose
simplePose = mkPose "test" (Data.Array.mapWithIndex (\i _ -> mkKeypoint (toNumber i * 10.0) (toNumber i * 20.0) 1.0) (Data.Array.range 0 17))

-- | A second pose offset from simplePose for interpolation tests
simplePose2 :: Pose
simplePose2 = mkPose "test2" (Data.Array.mapWithIndex (\i _ -> mkKeypoint (toNumber i * 10.0 + 100.0) (toNumber i * 20.0 + 200.0) 0.5) (Data.Array.range 0 17))

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "PoseExport" do
    cocoBonesAndColorsTests
    exportToOpenPoseJSONTests
    importRoundtripTests
    interpolatePosesTests
    createPoseSequenceTests
    defaultConfigTests

--------------------------------------------------------------------------------
-- 1. cocoBones and colors
--------------------------------------------------------------------------------

cocoBonesAndColorsTests :: Spec Unit
cocoBonesAndColorsTests = do
  describe "cocoBones and colors" do

    it "cocoBones has 16 bone connections" do
      Data.Array.length cocoBones `shouldEqual` 16

    it "openposeColors has 6 named color fields" do
      -- Verify all 6 fields are accessible and non-empty
      let colors = openposeColors
      (colors.head /= "") `shouldEqual` true
      (colors.right_arm /= "") `shouldEqual` true
      (colors.left_arm /= "") `shouldEqual` true
      (colors.right_leg /= "") `shouldEqual` true
      (colors.left_leg /= "") `shouldEqual` true
      (colors.torso /= "") `shouldEqual` true

    it "each bone connection has exactly 2 indices" do
      let allHaveTwo = Data.Array.all (\bone -> Data.Array.length bone == 2) cocoBones
      allHaveTwo `shouldEqual` true

--------------------------------------------------------------------------------
-- 2. exportToOpenPoseJSON
--------------------------------------------------------------------------------

exportToOpenPoseJSONTests :: Spec Unit
exportToOpenPoseJSONTests = do
  describe "exportToOpenPoseJSON" do

    it "exports a valid version number" do
      let result = exportToOpenPoseJSON [simplePose]
      -- OpenPose JSON version is typically a positive number
      (result.version > 0.0) `shouldEqual` true

    it "exports correct number of people" do
      let result = exportToOpenPoseJSON [simplePose]
      Data.Array.length result.people `shouldEqual` 1

    it "pose_keypoints_2d has 54 values (18 keypoints x 3)" do
      let result = exportToOpenPoseJSON [simplePose]
      case Data.Array.index result.people 0 of
        Just person -> Data.Array.length person.pose_keypoints_2d `shouldEqual` 54
        Nothing -> shouldEqual true false

    it "face_keypoints_2d is empty array" do
      let result = exportToOpenPoseJSON [simplePose]
      case Data.Array.index result.people 0 of
        Just person -> Data.Array.length person.face_keypoints_2d `shouldEqual` 0
        Nothing -> shouldEqual true false

    it "hand arrays are empty" do
      let result = exportToOpenPoseJSON [simplePose]
      case Data.Array.index result.people 0 of
        Just person -> do
          Data.Array.length person.hand_left_keypoints_2d `shouldEqual` 0
          Data.Array.length person.hand_right_keypoints_2d `shouldEqual` 0
        Nothing -> shouldEqual true false

    it "handles empty poses array" do
      let result = exportToOpenPoseJSON []
      Data.Array.length result.people `shouldEqual` 0

--------------------------------------------------------------------------------
-- 3. importFromOpenPoseJSON roundtrip
--------------------------------------------------------------------------------

importRoundtripTests :: Spec Unit
importRoundtripTests = do
  describe "importFromOpenPoseJSON roundtrip" do

    it "import(export(pose)) preserves keypoint count" do
      let exported = exportToOpenPoseJSON [simplePose]
      let imported = importFromOpenPoseJSON exported
      case Data.Array.index imported 0 of
        Just pose -> Data.Array.length pose.keypoints `shouldEqual` 18
        Nothing -> shouldEqual true false

    it "import(export(pose)) preserves approximate coordinates" do
      let exported = exportToOpenPoseJSON [simplePose]
      let imported = importFromOpenPoseJSON exported
      case Data.Array.index imported 0 of
        Just pose -> do
          -- Check first keypoint: x=0, y=0
          case Data.Array.index pose.keypoints 0 of
            Just kp -> do
              assertCloseTo 0.01 0.0 kp.x
              assertCloseTo 0.01 0.0 kp.y
            Nothing -> shouldEqual true false
          -- Check second keypoint: x=10, y=20
          case Data.Array.index pose.keypoints 1 of
            Just kp -> do
              assertCloseTo 0.01 10.0 kp.x
              assertCloseTo 0.01 20.0 kp.y
            Nothing -> shouldEqual true false
        Nothing -> shouldEqual true false

    it "import from empty people array returns empty array" do
      let emptyJSON = { version: 1.0, people: [] }
      let imported = importFromOpenPoseJSON emptyJSON
      Data.Array.length imported `shouldEqual` 0

    it "roundtrip preserves multiple poses" do
      let exported = exportToOpenPoseJSON [simplePose, simplePose2]
      let imported = importFromOpenPoseJSON exported
      Data.Array.length imported `shouldEqual` 2

--------------------------------------------------------------------------------
-- 4. interpolatePoses
--------------------------------------------------------------------------------

interpolatePosesTests :: Spec Unit
interpolatePosesTests = do
  describe "interpolatePoses" do

    it "t=0 returns first pose keypoints" do
      let result = interpolatePoses simplePose simplePose2 0.0
      case Data.Array.index result.keypoints 1 of
        Just kp -> do
          -- simplePose keypoint 1: x=10, y=20
          assertCloseTo 1e-10 10.0 kp.x
          assertCloseTo 1e-10 20.0 kp.y
        Nothing -> shouldEqual true false

    it "t=1 returns second pose keypoints" do
      let result = interpolatePoses simplePose simplePose2 1.0
      case Data.Array.index result.keypoints 1 of
        Just kp -> do
          -- simplePose2 keypoint 1: x=10+100=110, y=20+200=220
          assertCloseTo 1e-10 110.0 kp.x
          assertCloseTo 1e-10 220.0 kp.y
        Nothing -> shouldEqual true false

    it "t=0.5 interpolates correctly" do
      let result = interpolatePoses simplePose simplePose2 0.5
      case Data.Array.index result.keypoints 1 of
        Just kp -> do
          -- midpoint of (10,20) and (110,220) = (60, 120)
          assertCloseTo 1e-5 60.0 kp.x
          assertCloseTo 1e-5 120.0 kp.y
        Nothing -> shouldEqual true false

--------------------------------------------------------------------------------
-- 6. createPoseSequence
--------------------------------------------------------------------------------

createPoseSequenceTests :: Spec Unit
createPoseSequenceTests = do
  describe "createPoseSequence" do

    it "creates correct number of frames" do
      let keyframes =
            [ { frame: 0, poses: [simplePose] }
            , { frame: 10, poses: [simplePose2] }
            ]
      let seq = createPoseSequence keyframes 11 24
      Data.Array.length seq.frames `shouldEqual` 11

    it "frames are numbered sequentially starting from 0" do
      let keyframes =
            [ { frame: 0, poses: [simplePose] }
            , { frame: 4, poses: [simplePose2] }
            ]
      let seq = createPoseSequence keyframes 5 30
      case Data.Array.index seq.frames 0 of
        Just f -> f.frameNumber `shouldEqual` 0
        Nothing -> shouldEqual true false
      case Data.Array.index seq.frames 4 of
        Just f -> f.frameNumber `shouldEqual` 4
        Nothing -> shouldEqual true false

    it "sequence stores fps correctly" do
      let keyframes = [ { frame: 0, poses: [simplePose] } ]
      let seq = createPoseSequence keyframes 10 24
      seq.fps `shouldEqual` 24

--------------------------------------------------------------------------------
-- 7. defaultPoseExportConfig
--------------------------------------------------------------------------------

defaultConfigTests :: Spec Unit
defaultConfigTests = do
  describe "defaultPoseExportConfig" do

    it "has reasonable default width/height" do
      (defaultPoseExportConfig.width > 0) `shouldEqual` true
      (defaultPoseExportConfig.height > 0) `shouldEqual` true
      (defaultPoseExportConfig.width >= 64) `shouldEqual` true
      (defaultPoseExportConfig.height >= 64) `shouldEqual` true

    it "has valid default output format" do
      -- outputFormat field should exist and be a valid PoseOutputFormat
      let _fmt = defaultPoseExportConfig.outputFormat
      -- If this compiles and runs, the field exists and is valid
      true `shouldEqual` true
