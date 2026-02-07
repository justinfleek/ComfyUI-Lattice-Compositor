-- | Lattice.Schemas.Settings.ParticlePreferencesSchema - Particle preferences validation
-- |
-- | Validates particle preferences stored in localStorage.
-- |
-- | Source: ui/src/schemas/settings/particle-preferences-schema.ts

module Lattice.Schemas.Settings.ParticlePreferencesSchema
  ( -- Enums
    RenderingBackend(..)
  , renderingBackendFromString
  , renderingBackendToString
  , SimulationMode(..)
  , simulationModeFromString
  , simulationModeToString
    -- Constants
  , maxCheckpointInterval
  , maxCacheMemoryMB
  , maxParticlesPerLayer
  , maxTargetFPS
  , minTargetFPS
    -- Particle Preferences
  , ParticlePreferences
  , defaultParticlePreferences
  , validateParticlePreferences
  , safeValidateParticlePreferences
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError
  , validatePositiveInt
  )

--------------------------------------------------------------------------------
-- Enums
--------------------------------------------------------------------------------

-- | Rendering backend options
data RenderingBackend = BackendAuto | BackendWebGPU | BackendWebGL2 | BackendCPU

derive instance Eq RenderingBackend
derive instance Generic RenderingBackend _

instance Show RenderingBackend where
  show = genericShow

renderingBackendFromString :: String -> Maybe RenderingBackend
renderingBackendFromString = case _ of
  "auto" -> Just BackendAuto
  "webgpu" -> Just BackendWebGPU
  "webgl2" -> Just BackendWebGL2
  "cpu" -> Just BackendCPU
  _ -> Nothing

renderingBackendToString :: RenderingBackend -> String
renderingBackendToString = case _ of
  BackendAuto -> "auto"
  BackendWebGPU -> "webgpu"
  BackendWebGL2 -> "webgl2"
  BackendCPU -> "cpu"

-- | Simulation mode options
data SimulationMode = ModeRealtime | ModeCached | ModeBaked

derive instance Eq SimulationMode
derive instance Generic SimulationMode _

instance Show SimulationMode where
  show = genericShow

simulationModeFromString :: String -> Maybe SimulationMode
simulationModeFromString = case _ of
  "realtime" -> Just ModeRealtime
  "cached" -> Just ModeCached
  "baked" -> Just ModeBaked
  _ -> Nothing

simulationModeToString :: SimulationMode -> String
simulationModeToString = case _ of
  ModeRealtime -> "realtime"
  ModeCached -> "cached"
  ModeBaked -> "baked"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxCheckpointInterval :: Int
maxCheckpointInterval = 10000

maxCacheMemoryMB :: Int
maxCacheMemoryMB = 100000

maxParticlesPerLayer :: Int
maxParticlesPerLayer = 100000000

maxTargetFPS :: Int
maxTargetFPS = 120

minTargetFPS :: Int
minTargetFPS = 1

--------------------------------------------------------------------------------
-- Particle Preferences
--------------------------------------------------------------------------------

-- | Particle preferences structure
type ParticlePreferences =
  { renderingBackend :: RenderingBackend
  , simulationMode :: SimulationMode
  , cacheCheckpointInterval :: Int
  , maxCacheMemoryMB :: Int
  , maxParticlesPerLayer :: Int
  , enableGPUCompute :: Boolean
  , targetFPS :: Int
  , enableMotionBlur :: Boolean
  , enableSoftParticles :: Boolean
  , enableShadows :: Boolean
  , lodEnabled :: Boolean
  }

-- | Default particle preferences
defaultParticlePreferences :: ParticlePreferences
defaultParticlePreferences =
  { renderingBackend: BackendAuto
  , simulationMode: ModeRealtime
  , cacheCheckpointInterval: 100
  , maxCacheMemoryMB: 4096
  , maxParticlesPerLayer: 1000000
  , enableGPUCompute: true
  , targetFPS: 60
  , enableMotionBlur: false
  , enableSoftParticles: true
  , enableShadows: false
  , lodEnabled: true
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate ParticlePreferences
validateParticlePreferences :: ParticlePreferences -> Either ValidationError ParticlePreferences
validateParticlePreferences pp = do
  _ <- validatePositiveInt "cacheCheckpointInterval" maxCheckpointInterval pp.cacheCheckpointInterval
  _ <- validatePositiveInt "maxCacheMemoryMB" maxCacheMemoryMB pp.maxCacheMemoryMB
  _ <- validatePositiveInt "maxParticlesPerLayer" maxParticlesPerLayer pp.maxParticlesPerLayer
  if pp.targetFPS < minTargetFPS || pp.targetFPS > maxTargetFPS
    then Left $ mkError "targetFPS" $
           "must be between " <> show minTargetFPS <> " and " <> show maxTargetFPS
    else pure pp

-- | Safe validation
safeValidateParticlePreferences :: ParticlePreferences -> Maybe ParticlePreferences
safeValidateParticlePreferences pp =
  case validateParticlePreferences pp of
    Right p -> Just p
    Left _ -> Nothing
