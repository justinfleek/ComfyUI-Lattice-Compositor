-- | Port of flow generator tests
-- |
-- | Tests generative flow patterns: spiral, wave, explosion, vortex,
-- | dispatch via generateFlow, trajectory metadata, and type enumerations.
-- |
-- | 25 tests across 7 describe blocks

module Test.Lattice.Export.FlowGenerators (spec) where

import Prelude

import Data.Array (length)
import Data.Foldable (foldl, for_)
import Data.Int (toNumber)
import Data.Number (isFinite)
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

import Lattice.Services.Export.FlowGenerators.Generators
  ( generateFlow
  , generateSpiralFlow
  , generateWaveFlow
  , generateExplosionFlow
  , generateVortexFlow
  )
import Lattice.Services.Export.FlowGenerators.Types
  ( FlowPattern(..)
  , MorphShape(..)
  , MorphEasing(..)
  , WanMoveTrajectory
  , GenerativeFlowConfig
  , defaultGenerativeFlowParams
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Build a GenerativeFlowConfig with the given pattern and sensible defaults
mkConfig :: FlowPattern -> GenerativeFlowConfig
mkConfig pat =
  { pattern: pat
  , numPoints: 5
  , numFrames: 10
  , width: 512
  , height: 512
  , params: defaultGenerativeFlowParams
  }

-- | Check a predicate across all elements in a nested array
allOfNested :: forall a. (a -> Boolean) -> Array (Array a) -> Boolean
allOfNested f outer =
  let
    checkInner :: Array a -> Boolean
    checkInner inner = foldl (\acc el -> acc && f el) true inner
  in
    foldl (\acc row -> acc && checkInner row) true outer

-- | All coordinates in the trajectory are finite numbers
allCoordsFinite :: WanMoveTrajectory -> Boolean
allCoordsFinite traj =
  allOfNested (\pt -> isFinite pt.x && isFinite pt.y) traj.tracks

-- | All coordinates are within canvas bounds [0, w] x [0, h]
allCoordsInBounds :: Int -> Int -> WanMoveTrajectory -> Boolean
allCoordsInBounds w h traj =
  let
    wn = toNumber w
    hn = toNumber h
  in
    allOfNested
      (\pt -> pt.x >= 0.0 && pt.x <= wn && pt.y >= 0.0 && pt.y <= hn)
      traj.tracks

-- | Assert that a boolean condition holds, with a descriptive message on failure
assertTrue :: String -> Boolean -> Aff Unit
assertTrue msg cond =
  if cond then pure unit
  else fail msg

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "FlowGenerators" do
    spiralFlowTests
    waveFlowTests
    explosionFlowTests
    vortexFlowTests
    generateFlowDispatchTests
    metadataTests
    typeEnumerationTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. Spiral flow (5 tests)
-- ────────────────────────────────────────────────────────────────────────────

spiralFlowTests :: Spec Unit
spiralFlowTests = do
  describe "Spiral flow" do
    let cfg = mkConfig PatternSpiral
    let traj = generateSpiralFlow cfg

    it "produces correct number of tracks" do
      length traj.tracks `shouldEqual` cfg.numPoints

    it "produces correct number of frames per track" do
      for_ traj.tracks \track ->
        length track `shouldEqual` cfg.numFrames

    it "all coordinates are finite" do
      assertTrue "Expected all spiral coordinates to be finite" (allCoordsFinite traj)

    it "coordinates are within canvas bounds" do
      assertTrue
        "Expected all spiral coordinates within [0, width] x [0, height]"
        (allCoordsInBounds cfg.width cfg.height traj)

    it "deterministic - same config produces same result" do
      let traj2 = generateSpiralFlow cfg
      (traj.tracks == traj2.tracks) `shouldEqual` true
      (traj.visibility == traj2.visibility) `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 2. Wave flow (4 tests)
-- ────────────────────────────────────────────────────────────────────────────

waveFlowTests :: Spec Unit
waveFlowTests = do
  describe "Wave flow" do
    let cfg = mkConfig PatternWave
    let traj = generateWaveFlow cfg

    it "produces correct number of tracks" do
      length traj.tracks `shouldEqual` cfg.numPoints

    it "produces correct number of frames per track" do
      for_ traj.tracks \track ->
        length track `shouldEqual` cfg.numFrames

    it "all coordinates are finite" do
      assertTrue "Expected all wave coordinates to be finite" (allCoordsFinite traj)

    it "coordinates are within canvas bounds" do
      assertTrue
        "Expected all wave coordinates within bounds"
        (allCoordsInBounds cfg.width cfg.height traj)

-- ────────────────────────────────────────────────────────────────────────────
-- 3. Explosion flow (3 tests)
-- ────────────────────────────────────────────────────────────────────────────

explosionFlowTests :: Spec Unit
explosionFlowTests = do
  describe "Explosion flow" do
    let cfg = mkConfig PatternExplosion
    let traj = generateExplosionFlow cfg

    it "produces correct dimensions" do
      length traj.tracks `shouldEqual` cfg.numPoints
      for_ traj.tracks \track ->
        length track `shouldEqual` cfg.numFrames

    it "all coordinates are finite" do
      assertTrue "Expected all explosion coordinates to be finite" (allCoordsFinite traj)

    it "coordinates are within canvas bounds" do
      assertTrue
        "Expected all explosion coordinates within bounds"
        (allCoordsInBounds cfg.width cfg.height traj)

-- ────────────────────────────────────────────────────────────────────────────
-- 4. Vortex flow (3 tests)
-- ────────────────────────────────────────────────────────────────────────────

vortexFlowTests :: Spec Unit
vortexFlowTests = do
  describe "Vortex flow" do
    let cfg = mkConfig PatternVortex
    let traj = generateVortexFlow cfg

    it "produces correct dimensions" do
      length traj.tracks `shouldEqual` cfg.numPoints
      for_ traj.tracks \track ->
        length track `shouldEqual` cfg.numFrames

    it "all coordinates are finite" do
      assertTrue "Expected all vortex coordinates to be finite" (allCoordsFinite traj)

    it "coordinates are within canvas bounds" do
      assertTrue
        "Expected all vortex coordinates within bounds"
        (allCoordsInBounds cfg.width cfg.height traj)

-- ────────────────────────────────────────────────────────────────────────────
-- 5. generateFlow dispatch (4 tests)
-- ────────────────────────────────────────────────────────────────────────────

generateFlowDispatchTests :: Spec Unit
generateFlowDispatchTests = do
  describe "generateFlow dispatch" do
    let cfg = mkConfig PatternSpiral

    it "PatternSpiral dispatches to generateSpiralFlow" do
      let fromDispatch = generateFlow cfg
      let fromDirect = generateSpiralFlow cfg
      (fromDispatch.tracks == fromDirect.tracks) `shouldEqual` true
      (fromDispatch.visibility == fromDirect.visibility) `shouldEqual` true

    it "PatternWave dispatches to generateWaveFlow" do
      let waveCfg = mkConfig PatternWave
      let fromDispatch = generateFlow waveCfg
      let fromDirect = generateWaveFlow waveCfg
      (fromDispatch.tracks == fromDirect.tracks) `shouldEqual` true
      (fromDispatch.visibility == fromDirect.visibility) `shouldEqual` true

    it "PatternExplosion dispatches to generateExplosionFlow" do
      let explCfg = mkConfig PatternExplosion
      let fromDispatch = generateFlow explCfg
      let fromDirect = generateExplosionFlow explCfg
      (fromDispatch.tracks == fromDirect.tracks) `shouldEqual` true
      (fromDispatch.visibility == fromDirect.visibility) `shouldEqual` true

    it "PatternVortex dispatches to generateVortexFlow" do
      let vortCfg = mkConfig PatternVortex
      let fromDispatch = generateFlow vortCfg
      let fromDirect = generateVortexFlow vortCfg
      (fromDispatch.tracks == fromDirect.tracks) `shouldEqual` true
      (fromDispatch.visibility == fromDirect.visibility) `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 6. Metadata (3 tests)
-- ────────────────────────────────────────────────────────────────────────────

metadataTests :: Spec Unit
metadataTests = do
  describe "Trajectory metadata" do
    let cfg = mkConfig PatternSpiral
    let traj = generateSpiralFlow cfg

    it "metadata numPoints and numFrames match config" do
      traj.metadata.numPoints `shouldEqual` cfg.numPoints
      traj.metadata.numFrames `shouldEqual` cfg.numFrames

    it "metadata width and height match config" do
      traj.metadata.width `shouldEqual` cfg.width
      traj.metadata.height `shouldEqual` cfg.height

    it "metadata fps is 16" do
      traj.metadata.fps `shouldEqual` 16

-- ────────────────────────────────────────────────────────────────────────────
-- 7. Type enumerations (3 tests)
-- ────────────────────────────────────────────────────────────────────────────

typeEnumerationTests :: Spec Unit
typeEnumerationTests = do
  describe "Type enumerations" do

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

    it "MorphShape has 3 constructors" do
      let shapes =
            [ ShapeCircle
            , ShapeGrid
            , ShapeRandom
            ]
      length shapes `shouldEqual` 3

    it "MorphEasing has 4 constructors" do
      let easings =
            [ EasingLinear
            , EasingIn
            , EasingOut
            , EasingInOut
            ]
      length easings `shouldEqual` 4
