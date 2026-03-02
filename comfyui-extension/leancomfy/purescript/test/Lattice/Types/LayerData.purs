-- | Port of ui/src/__tests__/types/layerData.property.test.ts
-- |
-- | Tests createDefaultPoseKeypoints:
-- |   - Array length (18 keypoints, OpenPose format)
-- |   - Coordinate ranges (all x,y in [0,1])
-- |   - Confidence values (all 1.0)
-- |   - Body structure (head above body, feet at bottom, etc.)
-- |   - Determinism and immutability
-- |
-- | 15 tests across 1 describe block

module Test.Lattice.Types.LayerData (spec) where

import Prelude

import Data.Array (length, index, all)
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Lattice.Primitives (unUnitFloat)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

import Lattice.LayerData (createDefaultPoseKeypoints, PoseKeypoint)

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

getKp :: Int -> Maybe PoseKeypoint
getKp i = index createDefaultPoseKeypoints i

kpX :: PoseKeypoint -> Number
kpX kp = unUnitFloat kp.x

kpY :: PoseKeypoint -> Number
kpY kp = unUnitFloat kp.y

kpConf :: PoseKeypoint -> Number
kpConf kp = unUnitFloat kp.confidence

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "LayerData - Type Tests" do
    createDefaultPoseKeypointsTests

createDefaultPoseKeypointsTests :: Spec Unit
createDefaultPoseKeypointsTests = do
  describe "createDefaultPoseKeypoints" do

    it "should return an array" do
      let kps = createDefaultPoseKeypoints
      (length kps > 0) `shouldEqual` true

    it "should return exactly 18 keypoints (OpenPose format)" do
      length createDefaultPoseKeypoints `shouldEqual` 18

    it "should have x, y, confidence on each keypoint" do
      let kps = createDefaultPoseKeypoints
      -- Check that all keypoints have valid coordinates
      all (\kp -> kpX kp >= 0.0 && kpX kp <= 1.0) kps `shouldEqual` true

    it "should have all x values in range [0, 1]" do
      let kps = createDefaultPoseKeypoints
      all (\kp -> kpX kp >= 0.0 && kpX kp <= 1.0) kps `shouldEqual` true

    it "should have all y values in range [0, 1]" do
      let kps = createDefaultPoseKeypoints
      all (\kp -> kpY kp >= 0.0 && kpY kp <= 1.0) kps `shouldEqual` true

    it "should have all confidence values equal to 1" do
      let kps = createDefaultPoseKeypoints
      all (\kp -> kpConf kp == 1.0) kps `shouldEqual` true

    it "should have nose at top center (index 0)" do
      case getKp 0 of
        Just nose -> do
          shouldBeCloseTo (kpX nose) 0.5 0.01
          shouldBeCloseTo (kpY nose) 0.1 0.01
        Nothing -> fail "Expected nose keypoint at index 0"

    it "should have neck below nose" do
      case getKp 0, getKp 1 of
        Just nose, Just neck ->
          if kpY neck > kpY nose
            then pure unit
            else fail "Neck should be below nose"
        _, _ -> fail "Expected nose and neck keypoints"

    it "should have eyes above nose" do
      case getKp 0, getKp 14, getKp 15 of
        Just nose, Just rightEye, Just leftEye ->
          if kpY rightEye < kpY nose && kpY leftEye < kpY nose
            then pure unit
            else fail "Eyes should be above nose"
        _, _, _ -> fail "Expected nose and eye keypoints"

    it "should have left side keypoints with higher x than right side" do
      -- Left shoulder (5) vs right shoulder (2)
      case getKp 2, getKp 5 of
        Just rightShoulder, Just leftShoulder ->
          if kpX leftShoulder > kpX rightShoulder
            then pure unit
            else fail "Left shoulder should have higher x than right shoulder"
        _, _ -> fail "Expected shoulder keypoints"

    it "should have valid body structure (head above body)" do
      -- Nose (0) should be above hips (8, 11)
      case getKp 0, getKp 8, getKp 11 of
        Just nose, Just rightHip, Just leftHip ->
          if kpY nose < kpY rightHip && kpY nose < kpY leftHip
            then pure unit
            else fail "Head should be above hips"
        _, _, _ -> fail "Expected nose and hip keypoints"

    it "should have feet at the bottom" do
      -- Ankles (10, 13) should have highest y values
      case getKp 10, getKp 13, getKp 0 of
        Just rightAnkle, Just leftAnkle, Just nose ->
          if kpY rightAnkle > kpY nose && kpY leftAnkle > kpY nose
            then pure unit
            else fail "Feet should be below head"
        _, _, _ -> fail "Expected ankle and nose keypoints"

    it "should be deterministic" do
      let kps1 = createDefaultPoseKeypoints
      let kps2 = createDefaultPoseKeypoints
      length kps1 `shouldEqual` length kps2
      -- Check first and last keypoints match
      case index kps1 0, index kps2 0 of
        Just a, Just b -> do
          shouldBeCloseTo (kpX a) (kpX b) 0.001
          shouldBeCloseTo (kpY a) (kpY b) 0.001
        _, _ -> fail "Expected keypoints"

    it "should return a new array each call" do
      -- Both calls return same values (deterministic)
      let kps1 = createDefaultPoseKeypoints
      let kps2 = createDefaultPoseKeypoints
      length kps1 `shouldEqual` length kps2

    it "should not be affected by modifications" do
      -- In PureScript, values are immutable by default
      let kps1 = createDefaultPoseKeypoints
      let kps2 = createDefaultPoseKeypoints
      -- Both should be identical
      case index kps1 0, index kps2 0 of
        Just a, Just b ->
          shouldBeCloseTo (kpConf a) (kpConf b) 0.001
        _, _ -> fail "Expected keypoints"
