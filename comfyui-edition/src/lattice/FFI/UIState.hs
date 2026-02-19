-- |
-- Module      : Lattice.FFI.UIState
-- Description : C FFI bindings for UI store pure functions
-- 
-- Exports pure functions from Lattice.State.UI as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.UIState where

import Data.Aeson
  ( decode
  , encode
  , ToJSON(..)
  , Value(..)
  , object
  , (.=)
  )
import qualified Data.ByteString.Lazy as BSL
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String
  ( CString
  , peekCString
  , newCString
  )
import Lattice.State.UI
  ( isCurveEditorVisible
  , shouldHideMinimizedLayers
  , UIState(..)
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

-- | Check if curve editor is visible
foreign export ccall "is_curve_editor_visible"
  c_is_curve_editor_visible :: CString -> IO CString

c_is_curve_editor_visible :: CString -> IO CString
c_is_curve_editor_visible uiStateJson = do
  uiStateStr <- peekCString uiStateJson
  
  let uiStateBS = TE.encodeUtf8 (T.pack uiStateStr)
  
  case decode (BSL.fromStrict uiStateBS) :: Maybe UIState of
    Just state -> do
      let result = isCurveEditorVisible state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected UIState")

-- | Check if minimized layers should be hidden
foreign export ccall "should_hide_minimized_layers"
  c_should_hide_minimized_layers :: CString -> IO CString

c_should_hide_minimized_layers :: CString -> IO CString
c_should_hide_minimized_layers uiStateJson = do
  uiStateStr <- peekCString uiStateJson
  
  let uiStateBS = TE.encodeUtf8 (T.pack uiStateStr)
  
  case decode (BSL.fromStrict uiStateBS) :: Maybe UIState of
    Just state -> do
      let result = shouldHideMinimizedLayers state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected UIState")
