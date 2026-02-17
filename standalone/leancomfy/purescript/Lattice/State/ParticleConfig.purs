-- | Lattice.State.ParticleConfig - Pure particle preference operations
-- |
-- | Port of ui/src/stores/particlePreferences.ts (pure subset)
-- | Manages particle system rendering preferences as a pure data structure.

module Lattice.State.ParticleConfig
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
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- | Rendering backend options
data RenderingBackend = RBWebGL2 | RBWebGPU | RBCPUFallback

derive instance Eq RenderingBackend
derive instance Generic RenderingBackend _
instance Show RenderingBackend where show = genericShow

-- | Simulation execution mode
data SimulationMode = SMRealtime | SMStepBased | SMSubstepped

derive instance Eq SimulationMode
derive instance Generic SimulationMode _
instance Show SimulationMode where show = genericShow

-- | Particle system preferences
type ParticlePreferences =
  { maxParticles :: Int
  , targetFps :: Int
  , checkpointInterval :: Int
  , backend :: RenderingBackend
  , simulationMode :: SimulationMode
  , enableTrails :: Boolean
  , enableCollisions :: Boolean
  , qualityMultiplier :: Number
  }

-- | Default particle preferences
defaultPreferences :: ParticlePreferences
defaultPreferences =
  { maxParticles: 10000
  , targetFps: 60
  , checkpointInterval: 300
  , backend: RBWebGL2
  , simulationMode: SMRealtime
  , enableTrails: false
  , enableCollisions: false
  , qualityMultiplier: 1.0
  }

-- | Low-end device preset (reduced quality)
lowEndPreset :: ParticlePreferences
lowEndPreset =
  { maxParticles: 1000
  , targetFps: 30
  , checkpointInterval: 600
  , backend: RBCPUFallback
  , simulationMode: SMStepBased
  , enableTrails: false
  , enableCollisions: false
  , qualityMultiplier: 0.5
  }

-- | High-end device preset (maximum quality)
highEndPreset :: ParticlePreferences
highEndPreset =
  { maxParticles: 100000
  , targetFps: 120
  , checkpointInterval: 150
  , backend: RBWebGPU
  , simulationMode: SMSubstepped
  , enableTrails: true
  , enableCollisions: true
  , qualityMultiplier: 2.0
  }

-- | Validate max particle count (must be positive)
isValidMaxParticles :: Int -> Boolean
isValidMaxParticles n = n > 0

-- | Validate target FPS (must be positive, reasonable range)
isValidTargetFps :: Int -> Boolean
isValidTargetFps n = n > 0 && n <= 240

-- | Validate checkpoint interval (must be positive)
isValidCheckpointInterval :: Int -> Boolean
isValidCheckpointInterval n = n > 0

-- | Update max particles with validation
updateMaxParticles :: Int -> ParticlePreferences -> ParticlePreferences
updateMaxParticles n prefs =
  if isValidMaxParticles n
  then prefs { maxParticles = n }
  else prefs

-- | Update target FPS with validation
updateTargetFps :: Int -> ParticlePreferences -> ParticlePreferences
updateTargetFps n prefs =
  if isValidTargetFps n
  then prefs { targetFps = n }
  else prefs

-- | Update checkpoint interval with validation
updateCheckpointInterval :: Int -> ParticlePreferences -> ParticlePreferences
updateCheckpointInterval n prefs =
  if isValidCheckpointInterval n
  then prefs { checkpointInterval = n }
  else prefs

-- | Update rendering backend
updateBackend :: RenderingBackend -> ParticlePreferences -> ParticlePreferences
updateBackend b prefs = prefs { backend = b }

-- | Update simulation mode
updateSimulationMode :: SimulationMode -> ParticlePreferences -> ParticlePreferences
updateSimulationMode m prefs = prefs { simulationMode = m }

-- | Human-readable backend description
backendDescription :: RenderingBackend -> String
backendDescription RBWebGL2 = "WebGL 2.0 (GPU-accelerated)"
backendDescription RBWebGPU = "WebGPU (next-gen GPU)"
backendDescription RBCPUFallback = "CPU Fallback (compatibility)"
