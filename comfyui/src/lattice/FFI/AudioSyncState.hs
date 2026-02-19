-- |
-- Module      : Lattice.FFI.AudioSyncState
-- Description : FFI bindings for audio synchronization state management
-- 
-- Foreign function interface for Lattice.State.AudioSync
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.AudioSyncState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.AudioSync
  ( checkAudioStateSync
  , AudioState(..)
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
--                                                   // comparison // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Check if two audio states are in sync
foreign export ccall check_audio_state_sync_ffi :: CString -> IO CString
check_audio_state_sync_ffi :: CString -> IO CString
check_audio_state_sync_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (AudioState, AudioState) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (stateA, stateB) -> do
      let result = checkAudioStateSync stateA stateB
      jsonToCString (successResponse result)
