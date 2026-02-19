-- |
-- Module      : Lattice.State.ParticlePreferences
-- Description : Pure state management functions for particle preferences store
-- 
-- Migrated from ui/src/stores/particlePreferences.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.ParticlePreferences
  ( -- Computed functions
    activeBackend
  , gpuComputeActive
  , backendDescription
  , supportsHighParticleCounts
  -- Validation functions
  , sanitizeMaxParticlesPerLayer
  , sanitizeCacheCheckpointInterval
  , sanitizeMaxCacheMemoryMB
  , sanitizeTargetFPS
  -- Types
  , RenderingBackend(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withText
  )
import Data.Maybe (Maybe)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Utils.NumericSafety (ensureFinite, isFinite)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // rendering // backend
-- ════════════════════════════════════════════════════════════════════════════

-- | Rendering backend preference
data RenderingBackend
  = RenderingBackendAuto
  | RenderingBackendWebGPU
  | RenderingBackendWebGL2
  | RenderingBackendCPU
  deriving (Eq, Show, Generic)

instance ToJSON RenderingBackend where
  toJSON RenderingBackendAuto = "auto"
  toJSON RenderingBackendWebGPU = "webgpu"
  toJSON RenderingBackendWebGL2 = "webgl2"
  toJSON RenderingBackendCPU = "cpu"

instance FromJSON RenderingBackend where
  parseJSON = withText "RenderingBackend" $ \t ->
    case t of
      "auto" -> return RenderingBackendAuto
      "webgpu" -> return RenderingBackendWebGPU
      "webgl2" -> return RenderingBackendWebGL2
      "cpu" -> return RenderingBackendCPU
      _ -> fail ("Invalid RenderingBackend: " ++ T.unpack t)

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // computed // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Calculate actual rendering backend to use based on preference and detected backend
-- Pure function: takes preference and detected backend, returns active backend
activeBackend :: RenderingBackend -> RenderingBackend -> Bool -> Bool -> RenderingBackend
activeBackend preference detectedBackend hasWebGPU hasWebGL2 =
  case preference of
    RenderingBackendAuto -> detectedBackend
    RenderingBackendWebGPU ->
      if hasWebGPU
      then RenderingBackendWebGPU
      else
        if hasWebGL2
        then RenderingBackendWebGL2
        else RenderingBackendCPU
    RenderingBackendWebGL2 ->
      if hasWebGL2
      then RenderingBackendWebGL2
      else RenderingBackendCPU
    RenderingBackendCPU -> RenderingBackendCPU

-- | Check if GPU compute is actually available and enabled
-- Pure function: takes enable flag and availability flag, returns Bool
gpuComputeActive :: Bool -> Bool -> Bool
gpuComputeActive enableGPUCompute hasWebGPU = enableGPUCompute && hasWebGPU

-- | Generate human-readable backend description
-- Pure function: takes backend and GPU name, returns description string
backendDescription :: RenderingBackend -> Text -> Text
backendDescription backend gpuName =
  case backend of
    RenderingBackendWebGPU -> T.append "WebGPU (" (T.append gpuName ")")
    RenderingBackendWebGL2 -> T.append "WebGL2 (" (T.append gpuName ")")
    RenderingBackendCPU -> "Software Rendering"
    RenderingBackendAuto -> "Unknown"

-- | Check if current setup supports high particle counts
-- Pure function: takes backend, returns Bool
supportsHighParticleCounts :: RenderingBackend -> Bool
supportsHighParticleCounts backend =
  case backend of
    RenderingBackendCPU -> False
    _ -> True

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate and sanitize max particles per layer
-- Pure function: takes value, returns sanitized value (between 1000 and 500000)
sanitizeMaxParticlesPerLayer :: Maybe Double -> Double
sanitizeMaxParticlesPerLayer mVal =
  case mVal of
    Nothing -> 100000.0 -- default
    Just val ->
      if not (isFinite val) || val <= 0
      then 100000.0 -- default
      else ensureFinite (fromIntegral (max 1000 (min 500000 (floor val)))) 100000.0

-- | Validate and sanitize cache checkpoint interval
-- Pure function: takes value, returns sanitized value (between 1 and 120)
sanitizeCacheCheckpointInterval :: Maybe Double -> Double
sanitizeCacheCheckpointInterval mVal =
  case mVal of
    Nothing -> 30.0 -- default
    Just val ->
      if not (isFinite val) || val <= 0
      then 30.0 -- default
      else ensureFinite (fromIntegral (max 1 (min 120 (floor val)))) 30.0

-- | Validate and sanitize max cache memory MB
-- Pure function: takes value, returns sanitized value (between 128 and 2048)
sanitizeMaxCacheMemoryMB :: Maybe Double -> Double
sanitizeMaxCacheMemoryMB mVal =
  case mVal of
    Nothing -> 512.0 -- default
    Just val ->
      if not (isFinite val) || val <= 0
      then 512.0 -- default
      else ensureFinite (fromIntegral (max 128 (min 2048 (floor val)))) 512.0

-- | Validate and sanitize target FPS
-- Pure function: takes value, returns sanitized value (30 or 60)
sanitizeTargetFPS :: Maybe Double -> Double
sanitizeTargetFPS mVal =
  case mVal of
    Nothing -> 60.0 -- default
    Just val ->
      if val == 30.0 || val == 60.0
      then ensureFinite val 30.0
      else
        -- Round to nearest valid value
        if val < 45.0
        then 30.0
        else 60.0
