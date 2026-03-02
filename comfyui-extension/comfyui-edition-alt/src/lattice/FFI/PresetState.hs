-- |
-- Module      : Lattice.FFI.PresetState
-- Description : FFI bindings for preset state management
-- 
-- Foreign function interface for Lattice.State.Preset
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.PresetState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.Preset
  ( allPresets
  , filterByCategory
  , filterParticlePresets
  , filterPathEffectPresets
  , filterCameraShakePresets
  , filterCameraTrajectoryPresets
  , filterTextStylePresets
  , filterAnimationPresets
  , searchPresets
  , filterUserPresets
  , getPresetById
  , createPresetCollection
  , PresetCategory(..)
  , Preset(..)
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
--                                                        // query // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Get all presets
foreign export ccall all_presets_ffi :: CString -> IO CString
all_presets_ffi :: CString -> IO CString
all_presets_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String ([Preset], [Preset], [Preset]) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (builtInParticle, builtInPathEffect, userPresets) -> do
      let result = allPresets builtInParticle builtInPathEffect userPresets
      jsonToCString (successResponse result)

-- | FFI: Filter presets by category
foreign export ccall filter_by_category_ffi :: CString -> IO CString
filter_by_category_ffi :: CString -> IO CString
filter_by_category_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (PresetCategory, [Preset]) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (category, presets) -> do
      let result = filterByCategory category presets
      jsonToCString (successResponse result)

-- | FFI: Filter particle presets
foreign export ccall filter_particle_presets_ffi :: CString -> IO CString
filter_particle_presets_ffi :: CString -> IO CString
filter_particle_presets_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [Preset] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right presets -> do
      let result = filterParticlePresets presets
      jsonToCString (successResponse result)

-- | FFI: Filter path effect presets
foreign export ccall filter_path_effect_presets_ffi :: CString -> IO CString
filter_path_effect_presets_ffi :: CString -> IO CString
filter_path_effect_presets_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [Preset] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right presets -> do
      let result = filterPathEffectPresets presets
      jsonToCString (successResponse result)

-- | FFI: Filter camera shake presets
foreign export ccall filter_camera_shake_presets_ffi :: CString -> IO CString
filter_camera_shake_presets_ffi :: CString -> IO CString
filter_camera_shake_presets_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [Preset] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right presets -> do
      let result = filterCameraShakePresets presets
      jsonToCString (successResponse result)

-- | FFI: Filter camera trajectory presets
foreign export ccall filter_camera_trajectory_presets_ffi :: CString -> IO CString
filter_camera_trajectory_presets_ffi :: CString -> IO CString
filter_camera_trajectory_presets_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [Preset] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right presets -> do
      let result = filterCameraTrajectoryPresets presets
      jsonToCString (successResponse result)

-- | FFI: Filter text style presets
foreign export ccall filter_text_style_presets_ffi :: CString -> IO CString
filter_text_style_presets_ffi :: CString -> IO CString
filter_text_style_presets_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [Preset] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right presets -> do
      let result = filterTextStylePresets presets
      jsonToCString (successResponse result)

-- | FFI: Filter animation presets
foreign export ccall filter_animation_presets_ffi :: CString -> IO CString
filter_animation_presets_ffi :: CString -> IO CString
filter_animation_presets_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [Preset] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right presets -> do
      let result = filterAnimationPresets presets
      jsonToCString (successResponse result)

-- | FFI: Search presets
foreign export ccall search_presets_ffi :: CString -> IO CString
search_presets_ffi :: CString -> IO CString
search_presets_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, Maybe PresetCategory, [Preset]) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (query, mCategory, presets) -> do
      let result = searchPresets query mCategory presets
      jsonToCString (successResponse result)

-- | FFI: Filter user presets
foreign export ccall filter_user_presets_ffi :: CString -> IO CString
filter_user_presets_ffi :: CString -> IO CString
filter_user_presets_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [Preset] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right presets -> do
      let result = filterUserPresets presets
      jsonToCString (successResponse result)

-- | FFI: Get preset by ID
foreign export ccall get_preset_by_id_ffi :: CString -> IO CString
get_preset_by_id_ffi :: CString -> IO CString
get_preset_by_id_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, [Preset]) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (id_, presets) -> do
      let result = getPresetById id_ presets
      jsonToCString (successResponse result)

-- | FFI: Create preset collection
foreign export ccall create_preset_collection_ffi :: CString -> IO CString
create_preset_collection_ffi :: CString -> IO CString
create_preset_collection_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Int, Maybe [T.Text], [Preset], Int) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (version, mPresetIds, allPresets_, exportedAt) -> do
      let result = createPresetCollection version mPresetIds allPresets_ exportedAt
      jsonToCString (successResponse result)
