-- |
-- Module      : Lattice.FFI.ParticlePreferencesState
-- Description : FFI bindings for particle preferences state management
-- 
-- Foreign function interface for Lattice.State.ParticlePreferences
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ParticlePreferencesState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
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

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // json // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Create success response JSON
successResponse :: ToJSON a => a -> BSL.ByteString
successResponse result = encode $ object ["status" .= ("success" :: T.Text), "result" .= result]

-- | Create error response JSON
errorResponse :: T.Text -> BSL.ByteString
errorResponse msg = encode $ object ["status" .= ("error" :: T.Text), "message" .= msg]

-- | Convert ByteString to CString
jsonToCString :: BSL.ByteString -> IO CString
jsonToCString = newCString . T.unpack . TE.decodeUtf8 . BSL.toStrict

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // computed // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Calculate active backend
foreign export ccall active_backend_ffi :: CString -> IO CString
active_backend_ffi :: CString -> IO CString
active_backend_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (RenderingBackend, RenderingBackend, Bool, Bool) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (preference, detectedBackend, hasWebGPU, hasWebGL2) -> do
      let result = activeBackend preference detectedBackend hasWebGPU hasWebGL2
      jsonToCString (successResponse result)

-- | FFI: Check if GPU compute is active
foreign export ccall gpu_compute_active_ffi :: CString -> IO CString
gpu_compute_active_ffi :: CString -> IO CString
gpu_compute_active_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Bool, Bool) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (enableGPUCompute, hasWebGPU) -> do
      let result = gpuComputeActive enableGPUCompute hasWebGPU
      jsonToCString (successResponse result)

-- | FFI: Get backend description
foreign export ccall backend_description_ffi :: CString -> IO CString
backend_description_ffi :: CString -> IO CString
backend_description_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (RenderingBackend, T.Text) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (backend, gpuName) -> do
      let result = backendDescription backend gpuName
      jsonToCString (successResponse result)

-- | FFI: Check if supports high particle counts
foreign export ccall supports_high_particle_counts_ffi :: CString -> IO CString
supports_high_particle_counts_ffi :: CString -> IO CString
supports_high_particle_counts_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String RenderingBackend of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right backend -> do
      let result = supportsHighParticleCounts backend
      jsonToCString (successResponse result)

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Sanitize max particles per layer
foreign export ccall sanitize_max_particles_per_layer_ffi :: CString -> IO CString
sanitize_max_particles_per_layer_ffi :: CString -> IO CString
sanitize_max_particles_per_layer_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mVal -> do
      let result = sanitizeMaxParticlesPerLayer mVal
      jsonToCString (successResponse result)

-- | FFI: Sanitize cache checkpoint interval
foreign export ccall sanitize_cache_checkpoint_interval_ffi :: CString -> IO CString
sanitize_cache_checkpoint_interval_ffi :: CString -> IO CString
sanitize_cache_checkpoint_interval_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mVal -> do
      let result = sanitizeCacheCheckpointInterval mVal
      jsonToCString (successResponse result)

-- | FFI: Sanitize max cache memory MB
foreign export ccall sanitize_max_cache_memory_mb_ffi :: CString -> IO CString
sanitize_max_cache_memory_mb_ffi :: CString -> IO CString
sanitize_max_cache_memory_mb_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mVal -> do
      let result = sanitizeMaxCacheMemoryMB mVal
      jsonToCString (successResponse result)

-- | FFI: Sanitize target FPS
foreign export ccall sanitize_target_fps_ffi :: CString -> IO CString
sanitize_target_fps_ffi :: CString -> IO CString
sanitize_target_fps_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mVal -> do
      let result = sanitizeTargetFPS mVal
      jsonToCString (successResponse result)
