{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Settings.ParticlePreferencesSchema
Description : Particle preferences validation
Copyright   : (c) Lattice, 2026
License     : MIT

Validates particle preferences stored in localStorage.

Source: ui/src/schemas/settings/particle-preferences-schema.ts
-}

module Lattice.Schemas.Settings.ParticlePreferencesSchema
  ( -- * Enums
    RenderingBackend(..)
  , renderingBackendFromText
  , renderingBackendToText
  , SimulationMode(..)
  , simulationModeFromText
  , simulationModeToText
    -- * Constants
  , maxCheckpointInterval
  , maxCacheMemoryMB
  , maxParticlesPerLayer
  , maxTargetFPS
  , minTargetFPS
    -- * Particle Preferences
  , ParticlePreferences(..)
  , defaultParticlePreferences
  , validateParticlePreferences
  , safeValidateParticlePreferences
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError
  , validatePositiveInt
  )

--------------------------------------------------------------------------------
-- Enums
--------------------------------------------------------------------------------

-- | Rendering backend options
data RenderingBackend = BackendAuto | BackendWebGPU | BackendWebGL2 | BackendCPU
  deriving stock (Eq, Show, Generic, Enum, Bounded)

renderingBackendFromText :: Text -> Maybe RenderingBackend
renderingBackendFromText "auto" = Just BackendAuto
renderingBackendFromText "webgpu" = Just BackendWebGPU
renderingBackendFromText "webgl2" = Just BackendWebGL2
renderingBackendFromText "cpu" = Just BackendCPU
renderingBackendFromText _ = Nothing

renderingBackendToText :: RenderingBackend -> Text
renderingBackendToText BackendAuto = "auto"
renderingBackendToText BackendWebGPU = "webgpu"
renderingBackendToText BackendWebGL2 = "webgl2"
renderingBackendToText BackendCPU = "cpu"

-- | Simulation mode options
data SimulationMode = ModeRealtime | ModeCached | ModeBaked
  deriving stock (Eq, Show, Generic, Enum, Bounded)

simulationModeFromText :: Text -> Maybe SimulationMode
simulationModeFromText "realtime" = Just ModeRealtime
simulationModeFromText "cached" = Just ModeCached
simulationModeFromText "baked" = Just ModeBaked
simulationModeFromText _ = Nothing

simulationModeToText :: SimulationMode -> Text
simulationModeToText ModeRealtime = "realtime"
simulationModeToText ModeCached = "cached"
simulationModeToText ModeBaked = "baked"

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
data ParticlePreferences = ParticlePreferences
  { ppRenderingBackend :: !RenderingBackend
  , ppSimulationMode :: !SimulationMode
  , ppCacheCheckpointInterval :: !Int
  , ppMaxCacheMemoryMB :: !Int
  , ppMaxParticlesPerLayer :: !Int
  , ppEnableGPUCompute :: !Bool
  , ppTargetFPS :: !Int
  , ppEnableMotionBlur :: !Bool
  , ppEnableSoftParticles :: !Bool
  , ppEnableShadows :: !Bool
  , ppLodEnabled :: !Bool
  }
  deriving stock (Eq, Show, Generic)

-- | Default particle preferences
defaultParticlePreferences :: ParticlePreferences
defaultParticlePreferences = ParticlePreferences
  { ppRenderingBackend = BackendAuto
  , ppSimulationMode = ModeRealtime
  , ppCacheCheckpointInterval = 100
  , ppMaxCacheMemoryMB = 4096
  , ppMaxParticlesPerLayer = 1000000
  , ppEnableGPUCompute = True
  , ppTargetFPS = 60
  , ppEnableMotionBlur = False
  , ppEnableSoftParticles = True
  , ppEnableShadows = False
  , ppLodEnabled = True
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate ParticlePreferences
validateParticlePreferences :: ParticlePreferences -> Either ValidationError ParticlePreferences
validateParticlePreferences pp = do
  _ <- validatePositiveInt "cacheCheckpointInterval" maxCheckpointInterval (ppCacheCheckpointInterval pp)
  _ <- validatePositiveInt "maxCacheMemoryMB" maxCacheMemoryMB (ppMaxCacheMemoryMB pp)
  _ <- validatePositiveInt "maxParticlesPerLayer" maxParticlesPerLayer (ppMaxParticlesPerLayer pp)
  if ppTargetFPS pp < minTargetFPS || ppTargetFPS pp > maxTargetFPS
    then Left $ mkError "targetFPS" $
           "must be between " <> show minTargetFPS <> " and " <> show maxTargetFPS
    else Right pp

-- | Safe validation
safeValidateParticlePreferences :: ParticlePreferences -> Maybe ParticlePreferences
safeValidateParticlePreferences pp =
  case validateParticlePreferences pp of
    Right p -> Just p
    Left _ -> Nothing
