-- |
-- Module      : Lattice.FFI.AnimationState
-- Description : FFI bindings for animation state management
-- 
-- Foreign function interface for Lattice.State.Animation
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.AnimationState where

import Data.Aeson (encode, eitherDecode, object, (.=), ToJSON(..))
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, peekCString, newCString)
import Lattice.State.Animation
  ( hasWorkArea
  , effectiveStartFrame
  , getCurrentFrame
  , getFrameCount
  , getFps
  , getEffectiveEndFrame
  , getCurrentTimeFromFrameFps
  )
import Lattice.State.Animation.Types (AnimationState(..), defaultAnimationState)

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

-- | FFI: Check if work area is defined
foreign export ccall has_work_area_ffi :: CString -> IO CString
has_work_area_ffi :: CString -> IO CString
has_work_area_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Int, Maybe Int) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (mStart, mEnd) -> do
      let state = defaultAnimationState
            { animationStateWorkAreaStart = fromIntegral (fromMaybe 0 mStart)
            , animationStateWorkAreaStartSet = isJust mStart
            , animationStateWorkAreaEnd = fromIntegral (fromMaybe 0 mEnd)
            , animationStateWorkAreaEndSet = isJust mEnd
            }
      let result = hasWorkArea state
      jsonToCString (successResponse result)

-- | FFI: Get effective start frame
foreign export ccall effective_start_frame_ffi :: CString -> IO CString
effective_start_frame_ffi :: CString -> IO CString
effective_start_frame_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Int) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right mStart -> do
      let state = defaultAnimationState
            { animationStateWorkAreaStart = fromIntegral (fromMaybe 0 mStart)
            , animationStateWorkAreaStartSet = isJust mStart
            }
      let result = effectiveStartFrame state
      jsonToCString (successResponse result)

-- | FFI: Get current frame
foreign export ccall get_current_frame_ffi :: CString -> IO CString
get_current_frame_ffi :: CString -> IO CString
get_current_frame_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Int of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right currentFrame -> do
      let result = getCurrentFrame currentFrame
      jsonToCString (successResponse result)

-- | FFI: Get frame count
foreign export ccall get_frame_count_ffi :: CString -> IO CString
get_frame_count_ffi :: CString -> IO CString
get_frame_count_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Int of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right frameCount -> do
      let result = getFrameCount frameCount
      jsonToCString (successResponse result)

-- | FFI: Get FPS
foreign export ccall get_fps_ffi :: CString -> IO CString
get_fps_ffi :: CString -> IO CString
get_fps_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String Double of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right fps -> do
      let result = getFps fps
      jsonToCString (successResponse result)

-- | FFI: Get effective end frame
foreign export ccall get_effective_end_frame_ffi :: CString -> IO CString
get_effective_end_frame_ffi :: CString -> IO CString
get_effective_end_frame_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Maybe Int, Int) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (mEnd, frameCount) -> do
      let result = getEffectiveEndFrame mEnd frameCount
      jsonToCString (successResponse result)

-- | FFI: Get current time in seconds
foreign export ccall get_current_time_ffi :: CString -> IO CString
get_current_time_ffi :: CString -> IO CString
get_current_time_ffi inputCStr = do
  inputStr <- peekCString inputCStr
  case eitherDecode (BSL.fromStrict (TE.encodeUtf8 (T.pack inputStr))) :: Either String (Int, Double) of
    Left err -> jsonToCString (errorResponse (T.pack err))
    Right (currentFrame, fps) -> do
      let result = getCurrentTimeFromFrameFps currentFrame fps
      jsonToCString (successResponse result)
