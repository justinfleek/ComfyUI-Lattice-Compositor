-- | Port of ui/src/__tests__/stores/particlePreferences.property.test.ts
-- |
-- | Tests particle preference configuration:
-- |   - Default values and validation
-- |   - Preset configurations (low-end, high-end)
-- |   - Update operations with validation
-- |   - Backend descriptions
-- |   - Preference invariants
-- |
-- | Effectful tests (localStorage persistence) are deferred.
-- |
-- | 20 tests across 5 describe blocks

module Test.Lattice.State.ParticleConfig (spec) where

import Prelude

import Lattice.State.ParticleConfig
  ( ParticlePreferences
  , RenderingBackend(..)
  , SimulationMode(..)
  , defaultPreferences
  , lowEndPreset
  , highEndPreset
  , updateMaxParticles
  , updateTargetFps
  , updateCheckpointInterval
  , updateBackend
  , updateSimulationMode
  , isValidMaxParticles
  , isValidTargetFps
  , isValidCheckpointInterval
  , backendDescription
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "ParticleConfig" do
    defaultTests
    presetTests
    updateTests
    validationTests
    invariantTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. Default values
-- ────────────────────────────────────────────────────────────────────────────

defaultTests :: Spec Unit
defaultTests = do
  describe "defaultPreferences" do

    it "maxParticles is 10000" do
      defaultPreferences.maxParticles `shouldEqual` 10000

    it "targetFps is 60" do
      defaultPreferences.targetFps `shouldEqual` 60

    it "checkpointInterval is 300" do
      defaultPreferences.checkpointInterval `shouldEqual` 300

    it "backend is WebGL2" do
      defaultPreferences.backend `shouldEqual` RBWebGL2

    it "simulationMode is Realtime" do
      defaultPreferences.simulationMode `shouldEqual` SMRealtime

    it "enableTrails is false" do
      defaultPreferences.enableTrails `shouldEqual` false

    it "enableCollisions is false" do
      defaultPreferences.enableCollisions `shouldEqual` false

    it "is deterministic" do
      let p1 = defaultPreferences
      let p2 = defaultPreferences
      p1.maxParticles `shouldEqual` p2.maxParticles
      p1.targetFps `shouldEqual` p2.targetFps
      p1.backend `shouldEqual` p2.backend

-- ────────────────────────────────────────────────────────────────────────────
-- 2. Presets
-- ────────────────────────────────────────────────────────────────────────────

presetTests :: Spec Unit
presetTests = do
  describe "presets" do

    it "lowEndPreset has reduced particles" do
      lowEndPreset.maxParticles `shouldEqual` 1000

    it "lowEndPreset uses CPU fallback" do
      lowEndPreset.backend `shouldEqual` RBCPUFallback

    it "lowEndPreset targets 30fps" do
      lowEndPreset.targetFps `shouldEqual` 30

    it "highEndPreset has many particles" do
      highEndPreset.maxParticles `shouldEqual` 100000

    it "highEndPreset uses WebGPU" do
      highEndPreset.backend `shouldEqual` RBWebGPU

    it "highEndPreset targets 120fps" do
      highEndPreset.targetFps `shouldEqual` 120

    it "highEndPreset enables trails" do
      highEndPreset.enableTrails `shouldEqual` true

    it "highEndPreset enables collisions" do
      highEndPreset.enableCollisions `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 3. Update operations
-- ────────────────────────────────────────────────────────────────────────────

updateTests :: Spec Unit
updateTests = do
  describe "update operations" do

    it "updateMaxParticles with valid value" do
      let result = updateMaxParticles 5000 defaultPreferences
      result.maxParticles `shouldEqual` 5000

    it "updateMaxParticles ignores zero" do
      let result = updateMaxParticles 0 defaultPreferences
      result.maxParticles `shouldEqual` 10000

    it "updateMaxParticles ignores negative" do
      let result = updateMaxParticles (-100) defaultPreferences
      result.maxParticles `shouldEqual` 10000

    it "updateTargetFps with valid value" do
      let result = updateTargetFps 144 defaultPreferences
      result.targetFps `shouldEqual` 144

    it "updateTargetFps ignores zero" do
      let result = updateTargetFps 0 defaultPreferences
      result.targetFps `shouldEqual` 60

    it "updateTargetFps ignores above 240" do
      let result = updateTargetFps 300 defaultPreferences
      result.targetFps `shouldEqual` 60

    it "updateCheckpointInterval with valid value" do
      let result = updateCheckpointInterval 600 defaultPreferences
      result.checkpointInterval `shouldEqual` 600

    it "updateCheckpointInterval ignores zero" do
      let result = updateCheckpointInterval 0 defaultPreferences
      result.checkpointInterval `shouldEqual` 300

    it "updateBackend changes backend" do
      let result = updateBackend RBWebGPU defaultPreferences
      result.backend `shouldEqual` RBWebGPU

    it "updateSimulationMode changes mode" do
      let result = updateSimulationMode SMSubstepped defaultPreferences
      result.simulationMode `shouldEqual` SMSubstepped

    it "update one preference does not affect others" do
      let result = updateMaxParticles 5000 defaultPreferences
      result.targetFps `shouldEqual` 60
      result.backend `shouldEqual` RBWebGL2
      result.enableTrails `shouldEqual` false

-- ────────────────────────────────────────────────────────────────────────────
-- 4. Validation
-- ────────────────────────────────────────────────────────────────────────────

validationTests :: Spec Unit
validationTests = do
  describe "validation" do

    it "positive particle count is valid" do
      isValidMaxParticles 100 `shouldEqual` true

    it "zero particle count is invalid" do
      isValidMaxParticles 0 `shouldEqual` false

    it "negative particle count is invalid" do
      isValidMaxParticles (-1) `shouldEqual` false

    it "valid FPS range (1-240)" do
      isValidTargetFps 1 `shouldEqual` true
      isValidTargetFps 60 `shouldEqual` true
      isValidTargetFps 240 `shouldEqual` true

    it "invalid FPS (0 and >240)" do
      isValidTargetFps 0 `shouldEqual` false
      isValidTargetFps 241 `shouldEqual` false

    it "valid checkpoint interval" do
      isValidCheckpointInterval 1 `shouldEqual` true
      isValidCheckpointInterval 1000 `shouldEqual` true

    it "invalid checkpoint interval" do
      isValidCheckpointInterval 0 `shouldEqual` false
      isValidCheckpointInterval (-5) `shouldEqual` false

-- ────────────────────────────────────────────────────────────────────────────
-- 5. Invariants
-- ────────────────────────────────────────────────────────────────────────────

invariantTests :: Spec Unit
invariantTests = do
  describe "invariants" do

    it "all presets have positive maxParticles" do
      isValidMaxParticles defaultPreferences.maxParticles `shouldEqual` true
      isValidMaxParticles lowEndPreset.maxParticles `shouldEqual` true
      isValidMaxParticles highEndPreset.maxParticles `shouldEqual` true

    it "all presets have valid targetFps" do
      isValidTargetFps defaultPreferences.targetFps `shouldEqual` true
      isValidTargetFps lowEndPreset.targetFps `shouldEqual` true
      isValidTargetFps highEndPreset.targetFps `shouldEqual` true

    it "all presets have valid checkpointInterval" do
      isValidCheckpointInterval defaultPreferences.checkpointInterval `shouldEqual` true
      isValidCheckpointInterval lowEndPreset.checkpointInterval `shouldEqual` true
      isValidCheckpointInterval highEndPreset.checkpointInterval `shouldEqual` true

    it "backend descriptions are non-empty" do
      (backendDescription RBWebGL2 /= "") `shouldEqual` true
      (backendDescription RBWebGPU /= "") `shouldEqual` true
      (backendDescription RBCPUFallback /= "") `shouldEqual` true
