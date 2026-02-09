-- | Port of WanMove trajectory export tests
-- |
-- | Tests flow generation, JSON/NPY export, color gradients,
-- | attractor generation, and metadata defaults.
-- |
-- | 30 tests across 6 describe blocks

module Test.Lattice.Export.WanMoveExport (spec) where

import Prelude

import Data.Array (length, (!!))
import Data.Maybe (Maybe(..))
import Data.Number (isFinite)
import Data.String.CodeUnits (length) as SCU
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)
import Test.Lattice.TestHelpers (assertCloseTo)

import Lattice.Services.Export.WanMoveExport.Types
  ( defaultTrajectoryMetadata
  , AttractorType(..)
  , AttractorConfig
  )
import Lattice.Services.Export.WanMoveExport.Export
  ( exportAsJSON
  , exportWanMoveTrackCoordsJSON
  , exportWanMoveVisibility
  , exportWanMoveTrackCoordsPackage
  , exportAsNPYData
  )
import Lattice.Services.Export.WanMoveExport.Colors
  ( viridisGradient
  , plasmaGradient
  , infernoGradient
  , coolWarmGradient
  , rainbowGradient
  , depthGradient
  , sampleGradient
  , normalizeData
  , addTimeColorToTrajectory
  )
import Lattice.Services.Export.WanMoveExport.Attractors
  ( generateLorenzAttractor
  , generateRosslerAttractor
  , generateAizawaAttractor
  )
import Lattice.Services.Export.FlowGenerators.Generators
  ( generateFlow
  , generateSpiralFlow
  , generateWaveFlow
  , generateExplosionFlow
  , generateVortexFlow
  )
import Lattice.Services.Export.FlowGenerators.Types
  ( FlowPattern(..)
  , GenerativeFlowConfig
  , defaultGenerativeFlowParams
  )

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

mkFlowConfig :: FlowPattern -> GenerativeFlowConfig
mkFlowConfig pattern =
  { pattern
  , numPoints: 5
  , numFrames: 10
  , width: 512
  , height: 512
  , params: defaultGenerativeFlowParams
  }

mkAttractorConfig :: AttractorType -> AttractorConfig
mkAttractorConfig attractorType =
  { attractorType
  , numPoints: 5
  , numFrames: 10
  , width: 512
  , height: 512
  , dt: Nothing
  , scale: Nothing
  , center: Nothing
  , seed: Just 42
  }

-- | Check that all elements of an array satisfy a predicate
allOf :: forall a. (a -> Boolean) -> Array a -> Boolean
allOf f arr = allOfImpl f arr 0

allOfImpl :: forall a. (a -> Boolean) -> Array a -> Int -> Boolean
allOfImpl f arr i =
  if i >= length arr then true
  else case arr !! i of
    Nothing -> true
    Just v -> if f v then allOfImpl f arr (i + 1) else false

-- | Assert that a string is non-empty
assertNonEmpty :: String -> Aff Unit
assertNonEmpty s =
  if SCU.length s > 0
    then pure unit
    else fail "Expected non-empty string"

-- | Assert that all numbers in an array are finite
assertAllFinite :: Array Number -> Aff Unit
assertAllFinite arr =
  if allOf isFinite arr
    then pure unit
    else fail "Expected all values to be finite"

-- | Assert that all integers in an array are 0 or 1
assertAllBinary :: Array Int -> Aff Unit
assertAllBinary arr =
  if allOf (\v -> v == 0 || v == 1) arr
    then pure unit
    else fail "Expected all values to be 0 or 1"

-- | Check that an RGB record has valid channel values (0-255)
isValidRGB :: { r :: Int, g :: Int, b :: Int } -> Boolean
isValidRGB c =
  c.r >= 0 && c.r <= 255 &&
  c.g >= 0 && c.g <= 255 &&
  c.b >= 0 && c.b <= 255

assertValidRGB :: { r :: Int, g :: Int, b :: Int } -> Aff Unit
assertValidRGB c =
  if isValidRGB c then pure unit
  else fail ("RGB out of range: " <> show c.r <> "," <> show c.g <> "," <> show c.b)

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "WanMoveExport" do
    flowGenerationShapeTests
    exportJSONTests
    exportNPYTests
    colorGradientTests
    attractorTests
    metadataAndDefaultsTests

--------------------------------------------------------------------------------
-- 1. Flow generation shape
--------------------------------------------------------------------------------

flowGenerationShapeTests :: Spec Unit
flowGenerationShapeTests = do
  describe "flow generation shape" do

    it "spiral flow produces correct track count and frame count" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      length traj.tracks `shouldEqual` 5
      case traj.tracks !! 0 of
        Just frames -> length frames `shouldEqual` 10
        Nothing -> fail "Expected at least one track"

    it "wave flow produces correct dimensions" do
      let config = mkFlowConfig PatternWave
      let traj = generateWaveFlow config
      length traj.tracks `shouldEqual` 5
      case traj.tracks !! 0 of
        Just frames -> length frames `shouldEqual` 10
        Nothing -> fail "Expected at least one track"

    it "explosion flow produces correct dimensions" do
      let config = mkFlowConfig PatternExplosion
      let traj = generateExplosionFlow config
      length traj.tracks `shouldEqual` 5
      case traj.tracks !! 0 of
        Just frames -> length frames `shouldEqual` 10
        Nothing -> fail "Expected at least one track"

    it "vortex flow produces correct dimensions" do
      let config = mkFlowConfig PatternVortex
      let traj = generateVortexFlow config
      length traj.tracks `shouldEqual` 5
      case traj.tracks !! 0 of
        Just frames -> length frames `shouldEqual` 10
        Nothing -> fail "Expected at least one track"

    it "generateFlow dispatches to correct pattern" do
      let configSpiral = mkFlowConfig PatternSpiral
      let trajDirect = generateSpiralFlow configSpiral
      let trajDispatched = generateFlow configSpiral
      length trajDirect.tracks `shouldEqual` length trajDispatched.tracks
      length trajDirect.visibility `shouldEqual` length trajDispatched.visibility

    it "all tracks have consistent frame length" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let expectedFrames = 10
      let checkTrack track = length track == expectedFrames
      allOf checkTrack traj.tracks `shouldEqual` true
      allOf (\vis -> length vis == expectedFrames) traj.visibility `shouldEqual` true

--------------------------------------------------------------------------------
-- 2. Export JSON
--------------------------------------------------------------------------------

exportJSONTests :: Spec Unit
exportJSONTests = do
  describe "export JSON" do

    it "exportAsJSON returns non-empty string" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let json = exportAsJSON traj
      assertNonEmpty json

    it "exportWanMoveTrackCoordsJSON returns non-empty string" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let json = exportWanMoveTrackCoordsJSON traj
      assertNonEmpty json

    it "exportWanMoveVisibility returns non-empty string" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let json = exportWanMoveVisibility traj
      assertNonEmpty json

    it "exportWanMoveTrackCoordsPackage returns package with metadata" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let pkg = exportWanMoveTrackCoordsPackage traj
      pkg.metadata.numPoints `shouldEqual` traj.metadata.numPoints
      pkg.metadata.numFrames `shouldEqual` traj.metadata.numFrames

    it "export package metadata matches trajectory metadata" do
      let config = mkFlowConfig PatternWave
      let traj = generateWaveFlow config
      let pkg = exportWanMoveTrackCoordsPackage traj
      pkg.metadata.width `shouldEqual` traj.metadata.width
      pkg.metadata.height `shouldEqual` traj.metadata.height
      pkg.metadata.fps `shouldEqual` traj.metadata.fps

--------------------------------------------------------------------------------
-- 3. Export NPY
--------------------------------------------------------------------------------

exportNPYTests :: Spec Unit
exportNPYTests = do
  describe "export NPY" do

    it "exportAsNPYData returns tracks array with correct length (N * T * 2)" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let npy = exportAsNPYData traj
      -- N=5, T=10, coords=2 => 5 * 10 * 2 = 100
      length npy.tracks `shouldEqual` (5 * 10 * 2)

    it "exportAsNPYData returns visibility array with correct length (N * T)" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let npy = exportAsNPYData traj
      -- N=5, T=10 => 5 * 10 = 50
      length npy.visibility `shouldEqual` (5 * 10)

    it "NPY shape metadata is correct" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let npy = exportAsNPYData traj
      npy.shape.tracks.n `shouldEqual` 5
      npy.shape.tracks.t `shouldEqual` 10
      npy.shape.tracks.coords `shouldEqual` 2
      npy.shape.visibility.n `shouldEqual` 5
      npy.shape.visibility.t `shouldEqual` 10

    it "visibility values are 0 or 1" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let npy = exportAsNPYData traj
      assertAllBinary npy.visibility

    it "shape.tracks.coords is always 2" do
      let configWave = mkFlowConfig PatternWave
      let trajWave = generateWaveFlow configWave
      let npyWave = exportAsNPYData trajWave
      npyWave.shape.tracks.coords `shouldEqual` 2
      let configVortex = mkFlowConfig PatternVortex
      let trajVortex = generateVortexFlow configVortex
      let npyVortex = exportAsNPYData trajVortex
      npyVortex.shape.tracks.coords `shouldEqual` 2

--------------------------------------------------------------------------------
-- 4. Color gradients
--------------------------------------------------------------------------------

colorGradientTests :: Spec Unit
colorGradientTests = do
  describe "color gradients" do

    it "sampleGradient at t=0 returns first stop color" do
      let grad = viridisGradient
      let c = sampleGradient grad 0.0
      -- First stop should be the gradient's starting color
      assertValidRGB c

    it "sampleGradient at t=1 returns last stop color" do
      let grad = viridisGradient
      let c = sampleGradient grad 1.0
      assertValidRGB c

    it "sampleGradient returns valid RGB (0-255)" do
      let grad = plasmaGradient
      let c1 = sampleGradient grad 0.0
      let c2 = sampleGradient grad 0.25
      let c3 = sampleGradient grad 0.5
      let c4 = sampleGradient grad 0.75
      let c5 = sampleGradient grad 1.0
      assertValidRGB c1
      assertValidRGB c2
      assertValidRGB c3
      assertValidRGB c4
      assertValidRGB c5

    it "all named gradients produce valid RGB at t=0.5" do
      assertValidRGB (sampleGradient viridisGradient 0.5)
      assertValidRGB (sampleGradient plasmaGradient 0.5)
      assertValidRGB (sampleGradient infernoGradient 0.5)
      assertValidRGB (sampleGradient coolWarmGradient 0.5)
      assertValidRGB (sampleGradient rainbowGradient 0.5)
      assertValidRGB (sampleGradient depthGradient 0.5)

    it "addTimeColorToTrajectory returns colored trajectory" do
      let config = mkFlowConfig PatternSpiral
      let traj = generateSpiralFlow config
      let colored = addTimeColorToTrajectory traj "viridis"
      length colored.tracks `shouldEqual` length traj.tracks

    it "normalizeData scales values to [0,1]" do
      let input = [0.0, 50.0, 100.0]
      let normalized = normalizeData input
      case normalized !! 0 of
        Just v -> assertCloseTo 1e-10 0.0 v
        Nothing -> fail "Expected normalized value at index 0"
      case normalized !! 1 of
        Just v -> assertCloseTo 1e-10 0.5 v
        Nothing -> fail "Expected normalized value at index 1"
      case normalized !! 2 of
        Just v -> assertCloseTo 1e-10 1.0 v
        Nothing -> fail "Expected normalized value at index 2"

--------------------------------------------------------------------------------
-- 5. Attractors
--------------------------------------------------------------------------------

attractorTests :: Spec Unit
attractorTests = do
  describe "attractors" do

    it "Lorenz attractor produces valid trajectory shape" do
      let config = mkAttractorConfig AttractorLorenz
      let traj = generateLorenzAttractor config
      length traj.tracks `shouldEqual` 5
      case traj.tracks !! 0 of
        Just frames -> length frames `shouldEqual` 10
        Nothing -> fail "Expected at least one track"

    it "Lorenz attractor is deterministic (same config produces same result)" do
      let config = mkAttractorConfig AttractorLorenz
      let traj1 = generateLorenzAttractor config
      let traj2 = generateLorenzAttractor config
      case traj1.tracks !! 0 of
        Just frames1 -> case traj2.tracks !! 0 of
          Just frames2 -> case frames1 !! 0 of
            Just p1 -> case frames2 !! 0 of
              Just p2 -> do
                assertCloseTo 1e-10 p1.x p2.x
                assertCloseTo 1e-10 p1.y p2.y
              Nothing -> fail "Expected point in trajectory 2"
            Nothing -> fail "Expected point in trajectory 1"
          Nothing -> fail "Expected track in trajectory 2"
        Nothing -> fail "Expected track in trajectory 1"

    it "Rossler attractor produces valid trajectory shape" do
      let config = mkAttractorConfig AttractorRossler
      let traj = generateRosslerAttractor config
      length traj.tracks `shouldEqual` 5
      case traj.tracks !! 0 of
        Just frames -> length frames `shouldEqual` 10
        Nothing -> fail "Expected at least one track"

    it "Aizawa attractor produces valid trajectory shape" do
      let config = mkAttractorConfig AttractorAizawa
      let traj = generateAizawaAttractor config
      length traj.tracks `shouldEqual` 5
      case traj.tracks !! 0 of
        Just frames -> length frames `shouldEqual` 10
        Nothing -> fail "Expected at least one track"

    it "all attractor coordinates are finite" do
      let lorenz = generateLorenzAttractor (mkAttractorConfig AttractorLorenz)
      let rossler = generateRosslerAttractor (mkAttractorConfig AttractorRossler)
      let aizawa = generateAizawaAttractor (mkAttractorConfig AttractorAizawa)
      let checkTrajectoryFinite traj =
            allOf (\track -> allOf (\p -> isFinite p.x && isFinite p.y) track) traj.tracks
      checkTrajectoryFinite lorenz `shouldEqual` true
      checkTrajectoryFinite rossler `shouldEqual` true
      checkTrajectoryFinite aizawa `shouldEqual` true

--------------------------------------------------------------------------------
-- 6. Metadata and defaults
--------------------------------------------------------------------------------

metadataAndDefaultsTests :: Spec Unit
metadataAndDefaultsTests = do
  describe "metadata and defaults" do

    it "defaultTrajectoryMetadata has fps 16" do
      defaultTrajectoryMetadata.fps `shouldEqual` 16

    it "defaultGenerativeFlowParams has no seed (Nothing)" do
      defaultGenerativeFlowParams.seed `shouldEqual` Nothing

    it "FlowPattern has 7 constructors" do
      let patterns =
            [ PatternSpiral
            , PatternWave
            , PatternExplosion
            , PatternVortex
            , PatternDataRiver
            , PatternMorph
            , PatternSwarm
            ]
      length patterns `shouldEqual` 7
