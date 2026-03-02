-- |
-- Module      : Lattice.FFI.MarkerState
-- Description : C FFI bindings for marker store pure functions
-- 
-- Exports pure functions from Lattice.State.Marker as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.MarkerState where

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
import Lattice.State.Marker
  ( framesEqual
  , getMarkers
  , getMarker
  , getMarkerAtFrame
  , getMarkersInRange
  , getNextMarker
  , getPreviousMarker
  , Marker(..)
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
--                                               // pure // helper // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Compare two frame values safely
foreign export ccall "frames_equal"
  c_frames_equal :: CString -> CString -> IO CString

c_frames_equal :: CString -> CString -> IO CString
c_frames_equal frameAJson frameBJson = do
  frameAStr <- peekCString frameAJson
  frameBStr <- peekCString frameBJson
  
  let frameABS = TE.encodeUtf8 (T.pack frameAStr)
  let frameBBS = TE.encodeUtf8 (T.pack frameBStr)
  
  case (decode (BSL.fromStrict frameABS) :: Maybe Double,
        decode (BSL.fromStrict frameBBS) :: Maybe Double) of
    (Just frameA, Just frameB) -> do
      let result = framesEqual frameA frameB
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Double and Double")

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // pure // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Get all markers
foreign export ccall "get_markers"
  c_get_markers :: CString -> IO CString

c_get_markers :: CString -> IO CString
c_get_markers markersJson = do
  markersStr <- peekCString markersJson
  
  let markersBS = TE.encodeUtf8 (T.pack markersStr)
  
  case decode (BSL.fromStrict markersBS) :: Maybe [Marker] of
    Just markers -> do
      let result = getMarkers markers
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Marker]")

-- | Get marker by ID
foreign export ccall "get_marker"
  c_get_marker :: CString -> CString -> IO CString

c_get_marker :: CString -> CString -> IO CString
c_get_marker markersJson markerIdJson = do
  markersStr <- peekCString markersJson
  markerIdStr <- peekCString markerIdJson
  
  let markersBS = TE.encodeUtf8 (T.pack markersStr)
  let markerIdText = T.pack markerIdStr
  
  case decode (BSL.fromStrict markersBS) :: Maybe [Marker] of
    Just markers -> do
      let result = getMarker markers markerIdText
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Marker]")

-- | Get marker at frame
foreign export ccall "get_marker_at_frame"
  c_get_marker_at_frame :: CString -> CString -> IO CString

c_get_marker_at_frame :: CString -> CString -> IO CString
c_get_marker_at_frame markersJson frameJson = do
  markersStr <- peekCString markersJson
  frameStr <- peekCString frameJson
  
  let markersBS = TE.encodeUtf8 (T.pack markersStr)
  let frameBS = TE.encodeUtf8 (T.pack frameStr)
  
  case (decode (BSL.fromStrict markersBS) :: Maybe [Marker],
        decode (BSL.fromStrict frameBS) :: Maybe Double) of
    (Just markers, Just frame) -> do
      let result = getMarkerAtFrame markers frame
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Marker] and Double")

-- | Get markers in range
foreign export ccall "get_markers_in_range"
  c_get_markers_in_range :: CString -> CString -> CString -> IO CString

c_get_markers_in_range :: CString -> CString -> CString -> IO CString
c_get_markers_in_range markersJson startFrameJson endFrameJson = do
  markersStr <- peekCString markersJson
  startFrameStr <- peekCString startFrameJson
  endFrameStr <- peekCString endFrameJson
  
  let markersBS = TE.encodeUtf8 (T.pack markersStr)
  let startFrameBS = TE.encodeUtf8 (T.pack startFrameStr)
  let endFrameBS = TE.encodeUtf8 (T.pack endFrameStr)
  
  case (decode (BSL.fromStrict markersBS) :: Maybe [Marker],
        decode (BSL.fromStrict startFrameBS) :: Maybe Double,
        decode (BSL.fromStrict endFrameBS) :: Maybe Double) of
    (Just markers, Just startFrame, Just endFrame) -> do
      let result = getMarkersInRange markers startFrame endFrame
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Marker], Double, and Double")

-- | Get next marker
foreign export ccall "get_next_marker"
  c_get_next_marker :: CString -> CString -> IO CString

c_get_next_marker :: CString -> CString -> IO CString
c_get_next_marker markersJson frameJson = do
  markersStr <- peekCString markersJson
  frameStr <- peekCString frameJson
  
  let markersBS = TE.encodeUtf8 (T.pack markersStr)
  let frameBS = TE.encodeUtf8 (T.pack frameStr)
  
  case (decode (BSL.fromStrict markersBS) :: Maybe [Marker],
        decode (BSL.fromStrict frameBS) :: Maybe Double) of
    (Just markers, Just frame) -> do
      let result = getNextMarker markers frame
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Marker] and Double")

-- | Get previous marker
foreign export ccall "get_previous_marker"
  c_get_previous_marker :: CString -> CString -> IO CString

c_get_previous_marker :: CString -> CString -> IO CString
c_get_previous_marker markersJson frameJson = do
  markersStr <- peekCString markersJson
  frameStr <- peekCString frameJson
  
  let markersBS = TE.encodeUtf8 (T.pack markersStr)
  let frameBS = TE.encodeUtf8 (T.pack frameStr)
  
  case (decode (BSL.fromStrict markersBS) :: Maybe [Marker],
        decode (BSL.fromStrict frameBS) :: Maybe Double) of
    (Just markers, Just frame) -> do
      let result = getPreviousMarker markers frame
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Marker] and Double")
