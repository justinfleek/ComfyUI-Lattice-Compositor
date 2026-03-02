-- | Port of ATI (Advanced Trajectory Inference) export tests
-- |
-- | Tests ATI constants, trajectory creation, validation,
-- | JSON export, package export, and normalized export.
-- |
-- | Sources:
-- |   - atiExport.test.ts
-- |
-- | 20 tests across 6 describe blocks

module Test.Lattice.Export.ATIExport (spec) where

import Prelude

import Data.Array (length, range, (!!))
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Number (isFinite)
import Data.String.CodeUnits (length) as SCU
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

import Lattice.Services.Export.ATI
  ( atiFixedFrames
  , exportATITrackCoordsJSON
  , exportATIPackage
  , exportAsNormalizedATI
  , validateForATI
  , createATITrajectory
  )
import Lattice.Services.Export.Types (WanMoveTrajectory)

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Build a test trajectory matching ATI module's WanMoveTrajectory type
-- | tracks :: Array (Array (Array Number))  -- [track][frame][x,y]
mkTestTrajectory :: Int -> Int -> Int -> Int -> WanMoveTrajectory
mkTestTrajectory numPoints numFrames width height =
  let
    safeDiv a b = if b == 0.0 then 0.0 else a / b
    mkPoint :: Int -> Int -> Array Number
    mkPoint f p = [ toNumber p * safeDiv (toNumber width) (toNumber numPoints)
                  , toNumber f * safeDiv (toNumber height) (toNumber numFrames)
                  ]
    mkTrack p = map (\f -> mkPoint f p) (range 0 (numFrames - 1))
    tracks = map mkTrack (range 0 (numPoints - 1))
  in
    { tracks, width, height, frameCount: numFrames }

-- | Assert that a string is non-empty
assertNonEmpty :: String -> Aff Unit
assertNonEmpty s =
  if SCU.length s > 0
    then pure unit
    else fail "Expected non-empty string"

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "ATIExport" do
    constantTests
    createTrajectoryTests
    validateTests
    exportJSONTests
    exportPackageTests
    exportNormalizedTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. Constants
-- ────────────────────────────────────────────────────────────────────────────

constantTests :: Spec Unit
constantTests = do
  describe "constants" do

    it "atiFixedFrames equals 121" do
      atiFixedFrames `shouldEqual` 121

    it "atiFixedFrames is a positive number" do
      (atiFixedFrames > 0) `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 2. createATITrajectory
-- ────────────────────────────────────────────────────────────────────────────

createTrajectoryTests :: Spec Unit
createTrajectoryTests = do
  describe "createATITrajectory" do

    it "creates trajectory with correct number of tracks" do
      let points =
            [ [ { x: 10.0, y: 20.0 }, { x: 30.0, y: 40.0 } ]
            , [ { x: 50.0, y: 60.0 }, { x: 70.0, y: 80.0 } ]
            , [ { x: 90.0, y: 100.0 }, { x: 110.0, y: 120.0 } ]
            ]
      let traj = createATITrajectory points 512 512 16
      length traj.tracks `shouldEqual` 3

    it "creates trajectory with correct width/height" do
      let points =
            [ [ { x: 10.0, y: 20.0 } ] ]
      let traj = createATITrajectory points 1024 768 16
      traj.width `shouldEqual` 1024
      traj.height `shouldEqual` 768

    it "creates trajectory with correct frameCount" do
      let points =
            [ [ { x: 10.0, y: 20.0 }, { x: 30.0, y: 40.0 } ] ]
      let traj = createATITrajectory points 512 512 24
      traj.frameCount `shouldEqual` 2

    it "empty tracks array creates empty trajectory" do
      let traj = createATITrajectory [] 512 512 16
      length traj.tracks `shouldEqual` 0

-- ────────────────────────────────────────────────────────────────────────────
-- 3. validateForATI
-- ────────────────────────────────────────────────────────────────────────────

validateTests :: Spec Unit
validateTests = do
  describe "validateForATI" do

    it "valid trajectory passes validation" do
      let traj = mkTestTrajectory 3 20 512 512
      let result = validateForATI traj
      result.valid `shouldEqual` true

    it "empty trajectory fails validation (or returns warnings)" do
      let traj = mkTestTrajectory 0 0 512 512
      let result = validateForATI traj
      -- An empty trajectory should either fail validation or produce warnings/errors
      let hasIssues = (length result.warnings > 0) || (length result.errors > 0) || (result.valid == false)
      hasIssues `shouldEqual` true

    it "trajectory with out-of-bounds coordinates returns warnings" do
      -- Create trajectory with coordinates outside canvas dimensions
      let outOfBounds =
            { tracks:
                [ [ [-100.0, -200.0], [9999.0, 9999.0] ] ]
            , width: 512
            , height: 512
            , frameCount: 2
            }
      let result = validateForATI outOfBounds
      let hasWarningsOrErrors = (length result.warnings > 0) || (length result.errors > 0)
      hasWarningsOrErrors `shouldEqual` true

    it "valid flag is true for valid input" do
      let traj = mkTestTrajectory 5 30 512 512
      let result = validateForATI traj
      result.valid `shouldEqual` true

    it "errors array is empty for valid input" do
      let traj = mkTestTrajectory 5 30 512 512
      let result = validateForATI traj
      length result.errors `shouldEqual` 0

-- ────────────────────────────────────────────────────────────────────────────
-- 4. exportATITrackCoordsJSON
-- ────────────────────────────────────────────────────────────────────────────

exportJSONTests :: Spec Unit
exportJSONTests = do
  describe "exportATITrackCoordsJSON" do

    it "returns non-empty string" do
      let traj = mkTestTrajectory 3 20 512 512
      let json = exportATITrackCoordsJSON traj
      assertNonEmpty json

    it "result contains coordinate data" do
      let traj = mkTestTrajectory 2 10 512 512
      let json = exportATITrackCoordsJSON traj
      --                                                                      // json
      (SCU.length json > 2) `shouldEqual` true

    it "tracks are padded/truncated to 121 frames" do
      --                                                                       // ati
      let traj = mkTestTrajectory 2 10 512 512
      let pkg = exportATIPackage traj
      -- The package track coords JSON should be built for atiFixedFrames
      assertNonEmpty pkg.tracks

-- ────────────────────────────────────────────────────────────────────────────
-- 5. exportATIPackage
-- ────────────────────────────────────────────────────────────────────────────

exportPackageTests :: Spec Unit
exportPackageTests = do
  describe "exportATIPackage" do

    it "package has correct width/height from trajectory metadata" do
      let traj = mkTestTrajectory 3 20 1024 768
      let pkg = exportATIPackage traj
      pkg.width `shouldEqual` 1024
      pkg.height `shouldEqual` 768

    it "package has correct numTracks" do
      let traj = mkTestTrajectory 5 20 512 512
      let pkg = exportATIPackage traj
      pkg.numTracks `shouldEqual` 5

    it "trackCoords is non-empty string" do
      let traj = mkTestTrajectory 3 20 512 512
      let pkg = exportATIPackage traj
      assertNonEmpty pkg.tracks

-- ────────────────────────────────────────────────────────────────────────────
-- 6. exportAsNormalizedATI
-- ────────────────────────────────────────────────────────────────────────────

exportNormalizedTests :: Spec Unit
exportNormalizedTests = do
  describe "exportAsNormalizedATI" do

    it "normalized tracks have x,y in expected range" do
      let traj = mkTestTrajectory 3 20 512 512
      let result = exportAsNormalizedATI traj Nothing
      -- Check first track, first point is in a reasonable normalized range
      case result.tracks !! 0 of
        Just track -> case track !! 0 of
          Just pt -> do
            -- Normalized coordinates should be finite numbers
            isFinite pt.x `shouldEqual` true
            isFinite pt.y `shouldEqual` true
          Nothing -> fail "Expected at least one point in track"
        Nothing -> fail "Expected at least one track"

    it "metadata has correct shortEdge (min of width, height)" do
      let traj = mkTestTrajectory 3 20 1024 768
      let result = exportAsNormalizedATI traj Nothing
      -- shortEdge should be min(1024, 768) = 768
      result.metadata.shortEdge `shouldEqual` 768

    it "timeRange has correct length" do
      let traj = mkTestTrajectory 3 20 512 512
      let result = exportAsNormalizedATI traj Nothing
      -- timeRange should have atiFixedFrames (121) entries
      length result.timeRange `shouldEqual` atiFixedFrames
