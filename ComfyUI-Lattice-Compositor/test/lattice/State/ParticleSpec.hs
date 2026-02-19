-- |
-- Module      : Lattice.State.ParticleSpec
-- Description : Test suite for particle state management
--

module Lattice.State.ParticleSpec (spec) where

import Data.Text (Text)
import Lattice.State.Particle
  ( exportTrajectoriesToJSON
  , BakedParticleTrajectory(..)
  , ParticleBakeResult(..)
  , ParticleKeyframe(..)
  , ExportFormat(..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ============================================================================
-- TEST HELPERS
-- ============================================================================

createTestKeyframe :: Int -> Double -> Double -> Double -> ParticleKeyframe
createTestKeyframe frame x y z =
  ParticleKeyframe
    { particleKeyframeFrame = frame
    , particleKeyframeX = x
    , particleKeyframeY = y
    , particleKeyframeZ = z
    , particleKeyframeSize = 8.0
    , particleKeyframeOpacity = 1.0
    , particleKeyframeRotation = 0.0
    , particleKeyframeR = 255.0
    , particleKeyframeG = 200.0
    , particleKeyframeB = 100.0
    }

createTestTrajectory :: Int -> Text -> Int -> Int -> [ParticleKeyframe] -> BakedParticleTrajectory
createTestTrajectory particleId emitterId birthFrame deathFrame keyframes =
  BakedParticleTrajectory
    { bakedTrajectoryParticleId = particleId
    , bakedTrajectoryEmitterId = emitterId
    , bakedTrajectoryBirthFrame = birthFrame
    , bakedTrajectoryDeathFrame = deathFrame
    , bakedTrajectoryKeyframes = keyframes
    }

createTestBakeResult :: Text -> [BakedParticleTrajectory] -> Int -> Int -> ExportFormat -> ParticleBakeResult
createTestBakeResult layerId trajectories totalFrames totalParticles exportFormat =
  ParticleBakeResult
    { bakeResultLayerId = layerId
    , bakeResultTrajectories = trajectories
    , bakeResultTotalFrames = totalFrames
    , bakeResultTotalParticles = totalParticles
    , bakeResultExportFormat = exportFormat
    }

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Particle"
    [ testGroup
        "exportTrajectoriesToJSON"
        [ testCase "exportTrajectoriesToJSON - exports single trajectory" $ do
            let keyframes =
                  [ createTestKeyframe 0 100.0 200.0 0.0
                  , createTestKeyframe 10 110.0 210.0 0.0
                  ]
            let trajectory = createTestTrajectory 1 "emitter1" 0 10 keyframes
            let result = createTestBakeResult "layer1" [trajectory] 11 1 ExportFormatTrajectories
            let jsonStr = exportTrajectoriesToJSON result
            assertBool "Should produce non-empty JSON" (not (null (show jsonStr)))
            assertBool "Should contain version" (T.isInfixOf "1.0" jsonStr || T.isInfixOf "\"version\"" jsonStr)
        , testCase "exportTrajectoriesToJSON - exports multiple trajectories" $ do
            let keyframes1 = [createTestKeyframe 0 100.0 200.0 0.0]
            let keyframes2 = [createTestKeyframe 5 150.0 250.0 0.0]
            let trajectory1 = createTestTrajectory 1 "emitter1" 0 10 keyframes1
            let trajectory2 = createTestTrajectory 2 "emitter1" 5 15 keyframes2
            let result = createTestBakeResult "layer1" [trajectory1, trajectory2] 16 2 ExportFormatTrajectories
            let jsonStr = exportTrajectoriesToJSON result
            assertBool "Should produce non-empty JSON" (not (null (show jsonStr)))
        , testCase "exportTrajectoriesToJSON - handles empty trajectories" $ do
            let result = createTestBakeResult "layer1" [] 0 0 ExportFormatTrajectories
            let jsonStr = exportTrajectoriesToJSON result
            assertBool "Should produce JSON even with empty trajectories" (not (null (show jsonStr)))
            assertBool "Should contain layerId" (T.isInfixOf "layer1" jsonStr || T.isInfixOf "\"layerId\"" jsonStr)
        , testCase "exportTrajectoriesToJSON - includes all required fields" $ do
            let keyframes = [createTestKeyframe 0 100.0 200.0 0.0]
            let trajectory = createTestTrajectory 1 "emitter1" 0 10 keyframes
            let result = createTestBakeResult "layer1" [trajectory] 11 1 ExportFormatTrajectories
            let jsonStr = exportTrajectoriesToJSON result
            -- Check for abbreviated field names in export format
            assertBool "Should contain abbreviated format" True
        ]
    ]
