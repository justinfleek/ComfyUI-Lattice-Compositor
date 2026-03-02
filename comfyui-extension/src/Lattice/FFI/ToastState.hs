-- |
-- Module      : Lattice.FFI.ToastState
-- Description : FFI bindings for toast state management
-- 
-- Foreign function interface for Lattice.State.Toast
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ToastState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.Toast
  ( createToast
  , getToasts
  , findToastById
  , filterToastsByType
  , ToastType(..)
  , Toast(..)
  )

-- ============================================================================
-- JSON HELPERS
-- ============================================================================

-- | Create success response JSON
successResponse :: ToJSON a => a -> BSL.ByteString
successResponse result = encode $ object ["status" .= ("success" :: T.Text), "result" .= result]

-- | Create error response JSON
errorResponse :: T.Text -> BSL.ByteString
errorResponse msg = encode $ object ["status" .= ("error" :: T.Text), "message" .= msg]

-- | Convert ByteString to CString
jsonToCString :: BSL.ByteString -> IO CString
jsonToCString = newCString . T.unpack . TE.decodeUtf8 . BSL.toStrict

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | FFI: Create a toast notification
foreign export ccall create_toast_ffi :: CString -> IO CString
create_toast_ffi :: CString -> IO CString
create_toast_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, T.Text, ToastType, Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (id_, message, type_, duration) -> do
      let result = createToast id_ message type_ duration
      jsonToCString (successResponse result)

-- ============================================================================
-- QUERY FUNCTIONS
-- ============================================================================

-- | FFI: Get all toasts
foreign export ccall get_toasts_ffi :: CString -> IO CString
get_toasts_ffi :: CString -> IO CString
get_toasts_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String [Toast] of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right toasts -> do
      let result = getToasts toasts
      jsonToCString (successResponse result)

-- | FFI: Find toast by ID
foreign export ccall find_toast_by_id_ffi :: CString -> IO CString
find_toast_by_id_ffi :: CString -> IO CString
find_toast_by_id_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (T.Text, [Toast]) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (id_, toasts) -> do
      let result = findToastById id_ toasts
      jsonToCString (successResponse result)

-- | FFI: Filter toasts by type
foreign export ccall filter_toasts_by_type_ffi :: CString -> IO CString
filter_toasts_by_type_ffi :: CString -> IO CString
filter_toasts_by_type_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (ToastType, [Toast]) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (type_, toasts) -> do
      let result = filterToastsByType type_ toasts
      jsonToCString (successResponse result)
