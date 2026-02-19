-- |
-- Module      : Lattice.State.ParticlePreferencesSpec
-- Description : Test suite for particle preferences state management
--

module Lattice.State.ParticlePreferencesSpec (spec) where

import Data.Text (Text)
import Lattice.State.ParticlePreferences
  ( activeBackend
  , gpuComputeActive
  , backendDescription
  , supportsHighParticleCounts
  , sanitizeMaxParticlesPerLayer
  , sanitizeCacheCheckpointInterval
  , sanitizeMaxCacheMemoryMB
  , sanitizeTargetFPS
  , RenderingBackend(..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.ParticlePreferences"
    [ testGroup
        "activeBackend"
        [ testCase "activeBackend - returns detected backend when auto" $ do
            let result = activeBackend RenderingBackendAuto RenderingBackendWebGPU True True
            assertEqual "Should return detected backend" RenderingBackendWebGPU result
        , testCase "activeBackend - returns WebGPU when forced and available" $ do
            let result = activeBackend RenderingBackendWebGPU RenderingBackendCPU True False
            assertEqual "Should return WebGPU" RenderingBackendWebGPU result
        , testCase "activeBackend - falls back to WebGL2 when WebGPU unavailable" $ do
            let result = activeBackend RenderingBackendWebGPU RenderingBackendCPU False True
            assertEqual "Should fall back to WebGL2" RenderingBackendWebGL2 result
        , testCase "activeBackend - falls back to CPU when WebGL2 unavailable" $ do
            let result = activeBackend RenderingBackendWebGL2 RenderingBackendCPU False False
            assertEqual "Should fall back to CPU" RenderingBackendCPU result
        ]
    , testGroup
        "gpuComputeActive"
        [ testCase "gpuComputeActive - returns True when both enabled and available" $ do
            let result = gpuComputeActive True True
            assertBool "Should return True" result
        , testCase "gpuComputeActive - returns False when disabled" $ do
            let result = gpuComputeActive False True
            assertBool "Should return False" (not result)
        , testCase "gpuComputeActive - returns False when unavailable" $ do
            let result = gpuComputeActive True False
            assertBool "Should return False" (not result)
        ]
    , testGroup
        "backendDescription"
        [ testCase "backendDescription - formats WebGPU description" $ do
            let result = backendDescription RenderingBackendWebGPU "NVIDIA RTX 4090"
            assertEqual "Should format WebGPU description" "WebGPU (NVIDIA RTX 4090)" result
        , testCase "backendDescription - formats WebGL2 description" $ do
            let result = backendDescription RenderingBackendWebGL2 "AMD Radeon RX 7900"
            assertEqual "Should format WebGL2 description" "WebGL2 (AMD Radeon RX 7900)" result
        , testCase "backendDescription - returns Software Rendering for CPU" $ do
            let result = backendDescription RenderingBackendCPU ""
            assertEqual "Should return Software Rendering" "Software Rendering" result
        ]
    , testGroup
        "supportsHighParticleCounts"
        [ testCase "supportsHighParticleCounts - returns True for WebGPU" $ do
            let result = supportsHighParticleCounts RenderingBackendWebGPU
            assertBool "Should return True" result
        , testCase "supportsHighParticleCounts - returns True for WebGL2" $ do
            let result = supportsHighParticleCounts RenderingBackendWebGL2
            assertBool "Should return True" result
        , testCase "supportsHighParticleCounts - returns False for CPU" $ do
            let result = supportsHighParticleCounts RenderingBackendCPU
            assertBool "Should return False" (not result)
        ]
    , testGroup
        "sanitizeMaxParticlesPerLayer"
        [ testCase "sanitizeMaxParticlesPerLayer - returns default when Nothing" $ do
            let result = sanitizeMaxParticlesPerLayer Nothing
            assertEqual "Should return default" 100000.0 result
        , testCase "sanitizeMaxParticlesPerLayer - clamps to minimum" $ do
            let result = sanitizeMaxParticlesPerLayer (Just 500.0)
            assertEqual "Should clamp to minimum" 1000.0 result
        , testCase "sanitizeMaxParticlesPerLayer - clamps to maximum" $ do
            let result = sanitizeMaxParticlesPerLayer (Just 1000000.0)
            assertEqual "Should clamp to maximum" 500000.0 result
        , testCase "sanitizeMaxParticlesPerLayer - returns default for NaN" $ do
            let result = sanitizeMaxParticlesPerLayer (Just (0/0))
            assertEqual "Should return default" 100000.0 result
        ]
    , testGroup
        "sanitizeCacheCheckpointInterval"
        [ testCase "sanitizeCacheCheckpointInterval - returns default when Nothing" $ do
            let result = sanitizeCacheCheckpointInterval Nothing
            assertEqual "Should return default" 30.0 result
        , testCase "sanitizeCacheCheckpointInterval - clamps to minimum" $ do
            let result = sanitizeCacheCheckpointInterval (Just 0.0)
            assertEqual "Should clamp to minimum" 1.0 result
        , testCase "sanitizeCacheCheckpointInterval - clamps to maximum" $ do
            let result = sanitizeCacheCheckpointInterval (Just 200.0)
            assertEqual "Should clamp to maximum" 120.0 result
        ]
    , testGroup
        "sanitizeMaxCacheMemoryMB"
        [ testCase "sanitizeMaxCacheMemoryMB - returns default when Nothing" $ do
            let result = sanitizeMaxCacheMemoryMB Nothing
            assertEqual "Should return default" 512.0 result
        , testCase "sanitizeMaxCacheMemoryMB - clamps to minimum" $ do
            let result = sanitizeMaxCacheMemoryMB (Just 50.0)
            assertEqual "Should clamp to minimum" 128.0 result
        , testCase "sanitizeMaxCacheMemoryMB - clamps to maximum" $ do
            let result = sanitizeMaxCacheMemoryMB (Just 5000.0)
            assertEqual "Should clamp to maximum" 2048.0 result
        ]
    , testGroup
        "sanitizeTargetFPS"
        [ testCase "sanitizeTargetFPS - returns default when Nothing" $ do
            let result = sanitizeTargetFPS Nothing
            assertEqual "Should return default" 60.0 result
        , testCase "sanitizeTargetFPS - returns 30 when valid" $ do
            let result = sanitizeTargetFPS (Just 30.0)
            assertEqual "Should return 30" 30.0 result
        , testCase "sanitizeTargetFPS - returns 60 when valid" $ do
            let result = sanitizeTargetFPS (Just 60.0)
            assertEqual "Should return 60" 60.0 result
        , testCase "sanitizeTargetFPS - rounds to 30 when below 45" $ do
            let result = sanitizeTargetFPS (Just 40.0)
            assertEqual "Should round to 30" 30.0 result
        , testCase "sanitizeTargetFPS - rounds to 60 when above 45" $ do
            let result = sanitizeTargetFPS (Just 50.0)
            assertEqual "Should round to 60" 60.0 result
        ]
    ]
