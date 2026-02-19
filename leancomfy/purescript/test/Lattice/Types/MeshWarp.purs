-- | Port of ui/src/__tests__/types/meshWarp.property.test.ts
-- |
-- | Tests MeshWarp pin type helpers:
-- |   - warpPinTypeUsesPosition
-- |   - warpPinTypeUsesRotation
-- |   - warpPinTypeUsesScale
-- |   - warpPinTypeUsesStiffness
-- |   - warpPinTypeUsesOverlap
-- |   - warpPinTypeDefaultStiffness
-- |
-- | 12 tests across 6 describe blocks

module Test.Lattice.Types.MeshWarp (spec) where

import Prelude

import Data.Foldable (for_)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

import Lattice.MeshWarp
  ( WarpPinType(..)
  , warpPinTypeUsesPosition
  , warpPinTypeUsesRotation
  , warpPinTypeUsesScale
  , warpPinTypeUsesStiffness
  , warpPinTypeUsesOverlap
  , warpPinTypeDefaultStiffness
  )

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "MeshWarp - Pin Type Tests" do
    usesPositionTests
    usesRotationTests
    usesScaleTests
    usesStiffnessTests
    usesOverlapTests
    defaultStiffnessTests

--------------------------------------------------------------------------------
-- All pin types for exhaustive testing
--------------------------------------------------------------------------------

allPinTypes :: Array WarpPinType
allPinTypes = [WPTPosition, WPTRotation, WPTStarch, WPTOverlap, WPTBend, WPTAdvanced]

--------------------------------------------------------------------------------
-- 1. warpPinTypeUsesPosition
--------------------------------------------------------------------------------

usesPositionTests :: Spec Unit
usesPositionTests = do
  describe "warpPinTypeUsesPosition" do

    it "should return true for Position and Advanced pins" do
      warpPinTypeUsesPosition WPTPosition `shouldEqual` true
      warpPinTypeUsesPosition WPTAdvanced `shouldEqual` true

    it "should return false for non-position pins" do
      warpPinTypeUsesPosition WPTRotation `shouldEqual` false
      warpPinTypeUsesPosition WPTStarch `shouldEqual` false
      warpPinTypeUsesPosition WPTOverlap `shouldEqual` false
      warpPinTypeUsesPosition WPTBend `shouldEqual` false

--------------------------------------------------------------------------------
-- 2. warpPinTypeUsesRotation
--------------------------------------------------------------------------------

usesRotationTests :: Spec Unit
usesRotationTests = do
  describe "warpPinTypeUsesRotation" do

    it "should return true for Rotation, Bend, and Advanced pins" do
      warpPinTypeUsesRotation WPTRotation `shouldEqual` true
      warpPinTypeUsesRotation WPTBend `shouldEqual` true
      warpPinTypeUsesRotation WPTAdvanced `shouldEqual` true

    it "should return false for non-rotation pins" do
      warpPinTypeUsesRotation WPTPosition `shouldEqual` false
      warpPinTypeUsesRotation WPTStarch `shouldEqual` false
      warpPinTypeUsesRotation WPTOverlap `shouldEqual` false

--------------------------------------------------------------------------------
-- 3. warpPinTypeUsesScale
--------------------------------------------------------------------------------

usesScaleTests :: Spec Unit
usesScaleTests = do
  describe "warpPinTypeUsesScale" do

    it "should return true for Bend and Advanced pins" do
      warpPinTypeUsesScale WPTBend `shouldEqual` true
      warpPinTypeUsesScale WPTAdvanced `shouldEqual` true

    it "should return false for non-scale pins" do
      warpPinTypeUsesScale WPTPosition `shouldEqual` false
      warpPinTypeUsesScale WPTRotation `shouldEqual` false
      warpPinTypeUsesScale WPTStarch `shouldEqual` false
      warpPinTypeUsesScale WPTOverlap `shouldEqual` false

--------------------------------------------------------------------------------
-- 4. warpPinTypeUsesStiffness
--------------------------------------------------------------------------------

usesStiffnessTests :: Spec Unit
usesStiffnessTests = do
  describe "warpPinTypeUsesStiffness" do

    it "should return true only for Starch pins" do
      warpPinTypeUsesStiffness WPTStarch `shouldEqual` true

    it "should return false for all other pin types" do
      warpPinTypeUsesStiffness WPTPosition `shouldEqual` false
      warpPinTypeUsesStiffness WPTRotation `shouldEqual` false
      warpPinTypeUsesStiffness WPTOverlap `shouldEqual` false
      warpPinTypeUsesStiffness WPTBend `shouldEqual` false
      warpPinTypeUsesStiffness WPTAdvanced `shouldEqual` false

--------------------------------------------------------------------------------
-- 5. warpPinTypeUsesOverlap
--------------------------------------------------------------------------------

usesOverlapTests :: Spec Unit
usesOverlapTests = do
  describe "warpPinTypeUsesOverlap" do

    it "should return true only for Overlap pins" do
      warpPinTypeUsesOverlap WPTOverlap `shouldEqual` true

    it "should return false for all other pin types" do
      warpPinTypeUsesOverlap WPTPosition `shouldEqual` false
      warpPinTypeUsesOverlap WPTRotation `shouldEqual` false
      warpPinTypeUsesOverlap WPTStarch `shouldEqual` false
      warpPinTypeUsesOverlap WPTBend `shouldEqual` false
      warpPinTypeUsesOverlap WPTAdvanced `shouldEqual` false

--------------------------------------------------------------------------------
-- 6. warpPinTypeDefaultStiffness
--------------------------------------------------------------------------------

defaultStiffnessTests :: Spec Unit
defaultStiffnessTests = do
  describe "warpPinTypeDefaultStiffness" do

    it "should return 1.0 for Starch pins" do
      warpPinTypeDefaultStiffness WPTStarch `shouldEqual` 1.0

    it "should return 0.0 for all other pin types" do
      for_ [WPTPosition, WPTRotation, WPTOverlap, WPTBend, WPTAdvanced] \pt ->
        warpPinTypeDefaultStiffness pt `shouldEqual` 0.0
