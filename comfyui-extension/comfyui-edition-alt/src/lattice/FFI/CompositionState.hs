-- |
-- Module      : Lattice.FFI.CompositionState
-- Description : C FFI bindings for composition store pure functions
-- 
-- Exports pure functions from Lattice.State.Composition as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.CompositionState where

import Data.Aeson
  ( decode
  , encode
  , ToJSON(..)
  , Value(..)
  , object
  , (.=)
  )
import qualified Data.ByteString.Lazy as BSL
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String
  ( CString
  , peekCString
  , newCString
  )
import Lattice.State.Composition
  ( getComposition
  , calculateDuration
  , computeCompositionSettings
  )
import Lattice.Types.Project
  ( Composition(..)
  , CompositionSettings(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                 // json // r
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert JSON Value to CString
jsonToCString :: Value -> IO CString
jsonToCString resultJSON = do
  let resultBS = BSL.toStrict (encode resultJSON)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)

-- | Create error response JSON
errorResponse :: T.Text -> Value
errorResponse msg = object ["status" .= ("error" :: T.Text), "message" .= msg]

-- | Create success response JSON with result
successResponse :: ToJSON a => a -> Value
successResponse result = object ["status" .= ("success" :: T.Text), "result" .= result]

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // pure // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Get a composition by ID
foreign export ccall "get_composition"
  c_get_composition :: CString -> CString -> IO CString

c_get_composition :: CString -> CString -> IO CString
c_get_composition compositionsJson compIdJson = do
  compositionsStr <- peekCString compositionsJson
  compIdStr <- peekCString compIdJson
  
  let compositionsBS = TE.encodeUtf8 (T.pack compositionsStr)
  let compIdBS = TE.encodeUtf8 (T.pack compIdStr)
  
  case (decode (BSL.fromStrict compositionsBS) :: Maybe (HashMap Text Composition),
        decode (BSL.fromStrict compIdBS) :: Maybe Text) of
    (Just compositions, Just compId) -> do
      let result = getComposition compositions compId
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected HashMap Text Composition and Text")

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // pure // calculations
-- ════════════════════════════════════════════════════════════════════════════

-- | Calculate duration from frame count and fps
foreign export ccall "calculate_duration"
  c_calculate_duration :: CString -> CString -> IO CString

c_calculate_duration :: CString -> CString -> IO CString
c_calculate_duration frameCountJson fpsJson = do
  frameCountStr <- peekCString frameCountJson
  fpsStr <- peekCString fpsJson
  
  let frameCountBS = TE.encodeUtf8 (T.pack frameCountStr)
  let fpsBS = TE.encodeUtf8 (T.pack fpsStr)
  
  case (decode (BSL.fromStrict frameCountBS) :: Maybe Double,
        decode (BSL.fromStrict fpsBS) :: Maybe Double) of
    (Just frameCount, Just fps) -> do
      let result = calculateDuration frameCount (Just fps)
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Double and Double")

-- | Compute composition settings with validation and defaults
foreign export ccall "compute_composition_settings"
  c_compute_composition_settings :: CString -> CString -> IO CString

c_compute_composition_settings :: CString -> CString -> IO CString
c_compute_composition_settings partialSettingsJson activeSettingsJson = do
  partialSettingsStr <- peekCString partialSettingsJson
  activeSettingsStr <- peekCString activeSettingsJson
  
  let partialSettingsBS = TE.encodeUtf8 (T.pack partialSettingsStr)
  let activeSettingsBS = TE.encodeUtf8 (T.pack activeSettingsStr)
  
  case (decode (BSL.fromStrict partialSettingsBS) :: Maybe CompositionSettings,
        decode (BSL.fromStrict activeSettingsBS) :: Maybe CompositionSettings) of
    (mPartial, mActive) -> do
      let result = computeCompositionSettings mPartial mActive
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Maybe CompositionSettings and Maybe CompositionSettings")
