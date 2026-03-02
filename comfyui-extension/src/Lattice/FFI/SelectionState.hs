-- |
-- Module      : Lattice.FFI.SelectionState
-- Description : C FFI bindings for selection store pure functions
-- 
-- Exports pure functions from Lattice.State.Selection as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.SelectionState where

import Data.Aeson
  ( decode
  , encode
  , ToJSON(..)
  , Value(..)
  , object
  , (.=)
  )
import qualified Data.ByteString.Lazy as BSL
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String
  ( CString
  , peekCString
  , newCString
  )
import Foreign.C.Types (CInt(..))
import Lattice.State.Selection
  ( hasSelection
  , hasMultipleSelected
  , hasKeyframeSelection
  , hasControlPointSelection
  , singleSelectedLayerId
  , selectedControlPointCount
  , isLayerSelected
  , isKeyframeSelected
  , isControlPointSelected
  , getSelectedControlPointsForLayer
  , computeRangeSelection
  , computeLayerAboveSelection
  , computeLayerBelowSelection
  , ControlPointSelection(..)
  )

-- ============================================================================
-- JSON Response Helpers
-- ============================================================================

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

-- ============================================================================
-- PURE QUERIES (GETTERS)
-- ============================================================================

-- | Check if any layers are selected
foreign export ccall "has_selection"
  c_has_selection :: CString -> IO CString

c_has_selection :: CString -> IO CString
c_has_selection selectedLayerIdsJson = do
  selectedLayerIdsStr <- peekCString selectedLayerIdsJson
  
  let selectedLayerIdsBS = TE.encodeUtf8 (T.pack selectedLayerIdsStr)
  
  case decode (BSL.fromStrict selectedLayerIdsBS) :: Maybe [Text] of
    Just ids -> do
      let selectedIdsSet = HS.fromList ids
      let result = hasSelection selectedIdsSet
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Text]")

-- | Check if multiple layers are selected
foreign export ccall "has_multiple_selected"
  c_has_multiple_selected :: CString -> IO CString

c_has_multiple_selected :: CString -> IO CString
c_has_multiple_selected selectedLayerIdsJson = do
  selectedLayerIdsStr <- peekCString selectedLayerIdsJson
  
  let selectedLayerIdsBS = TE.encodeUtf8 (T.pack selectedLayerIdsStr)
  
  case decode (BSL.fromStrict selectedLayerIdsBS) :: Maybe [Text] of
    Just ids -> do
      let selectedIdsSet = HS.fromList ids
      let result = hasMultipleSelected selectedIdsSet
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Text]")

-- | Check if any keyframes are selected
foreign export ccall "has_keyframe_selection"
  c_has_keyframe_selection :: CString -> IO CString

c_has_keyframe_selection :: CString -> IO CString
c_has_keyframe_selection selectedKeyframeIdsJson = do
  selectedKeyframeIdsStr <- peekCString selectedKeyframeIdsJson
  
  let selectedKeyframeIdsBS = TE.encodeUtf8 (T.pack selectedKeyframeIdsStr)
  
  case decode (BSL.fromStrict selectedKeyframeIdsBS) :: Maybe [Text] of
    Just ids -> do
      let selectedIdsSet = HS.fromList ids
      let result = hasKeyframeSelection selectedIdsSet
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Text]")

-- | Check if any control points are selected
foreign export ccall "has_control_point_selection"
  c_has_control_point_selection :: CString -> IO CString

c_has_control_point_selection :: CString -> IO CString
c_has_control_point_selection selectedControlPointsJson = do
  selectedControlPointsStr <- peekCString selectedControlPointsJson
  
  let selectedControlPointsBS = TE.encodeUtf8 (T.pack selectedControlPointsStr)
  
  case decode (BSL.fromStrict selectedControlPointsBS) :: Maybe [ControlPointSelection] of
    Just points -> do
      let result = hasControlPointSelection points
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [ControlPointSelection]")

-- | Get single selected layer ID
foreign export ccall "single_selected_layer_id"
  c_single_selected_layer_id :: CString -> IO CString

c_single_selected_layer_id :: CString -> IO CString
c_single_selected_layer_id selectedLayerIdsJson = do
  selectedLayerIdsStr <- peekCString selectedLayerIdsJson
  
  let selectedLayerIdsBS = TE.encodeUtf8 (T.pack selectedLayerIdsStr)
  
  case decode (BSL.fromStrict selectedLayerIdsBS) :: Maybe [Text] of
    Just ids -> do
      let selectedIdsSet = HS.fromList ids
      let result = singleSelectedLayerId selectedIdsSet
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Text]")

-- | Get count of selected control points
foreign export ccall "selected_control_point_count"
  c_selected_control_point_count :: CString -> IO CString

c_selected_control_point_count :: CString -> IO CString
c_selected_control_point_count selectedControlPointsJson = do
  selectedControlPointsStr <- peekCString selectedControlPointsJson
  
  let selectedControlPointsBS = TE.encodeUtf8 (T.pack selectedControlPointsStr)
  
  case decode (BSL.fromStrict selectedControlPointsBS) :: Maybe [ControlPointSelection] of
    Just points -> do
      let result = selectedControlPointCount points
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [ControlPointSelection]")

-- ============================================================================
-- PURE QUERY ACTIONS
-- ============================================================================

-- | Check if a layer is selected
foreign export ccall "is_layer_selected"
  c_is_layer_selected :: CString -> CString -> IO CString

c_is_layer_selected :: CString -> CString -> IO CString
c_is_layer_selected selectedLayerIdsJson layerIdJson = do
  selectedLayerIdsStr <- peekCString selectedLayerIdsJson
  layerIdStr <- peekCString layerIdJson
  
  let selectedLayerIdsBS = TE.encodeUtf8 (T.pack selectedLayerIdsStr)
  let layerIdBS = TE.encodeUtf8 (T.pack layerIdStr)
  
  case (decode (BSL.fromStrict selectedLayerIdsBS) :: Maybe [Text],
        decode (BSL.fromStrict layerIdBS) :: Maybe Text) of
    (Just ids, Just layerId) -> do
      let selectedIdsSet = HS.fromList ids
      let result = isLayerSelected selectedIdsSet layerId
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Text] and Text")

-- | Check if a keyframe is selected
foreign export ccall "is_keyframe_selected"
  c_is_keyframe_selected :: CString -> CString -> IO CString

c_is_keyframe_selected :: CString -> CString -> IO CString
c_is_keyframe_selected selectedKeyframeIdsJson keyframeIdJson = do
  selectedKeyframeIdsStr <- peekCString selectedKeyframeIdsJson
  keyframeIdStr <- peekCString keyframeIdJson
  
  let selectedKeyframeIdsBS = TE.encodeUtf8 (T.pack selectedKeyframeIdsStr)
  let keyframeIdBS = TE.encodeUtf8 (T.pack keyframeIdStr)
  
  case (decode (BSL.fromStrict selectedKeyframeIdsBS) :: Maybe [Text],
        decode (BSL.fromStrict keyframeIdBS) :: Maybe Text) of
    (Just ids, Just keyframeId) -> do
      let selectedIdsSet = HS.fromList ids
      let result = isKeyframeSelected selectedIdsSet keyframeId
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Text] and Text")

-- | Check if a control point is selected
foreign export ccall "is_control_point_selected"
  c_is_control_point_selected :: CString -> CString -> CInt -> IO CString

c_is_control_point_selected :: CString -> CString -> CInt -> IO CString
c_is_control_point_selected selectedControlPointsJson layerIdJson pointIndexInt = do
  selectedControlPointsStr <- peekCString selectedControlPointsJson
  layerIdStr <- peekCString layerIdJson
  let pointIndex = fromIntegral pointIndexInt
  
  let selectedControlPointsBS = TE.encodeUtf8 (T.pack selectedControlPointsStr)
  let layerIdBS = TE.encodeUtf8 (T.pack layerIdStr)
  
  case (decode (BSL.fromStrict selectedControlPointsBS) :: Maybe [ControlPointSelection],
        decode (BSL.fromStrict layerIdBS) :: Maybe Text) of
    (Just points, Just layerId) -> do
      let result = isControlPointSelected points layerId pointIndex
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [ControlPointSelection] and Text")

-- | Get selected control points for a specific layer
foreign export ccall "get_selected_control_points_for_layer"
  c_get_selected_control_points_for_layer :: CString -> CString -> IO CString

c_get_selected_control_points_for_layer :: CString -> CString -> IO CString
c_get_selected_control_points_for_layer selectedControlPointsJson layerIdJson = do
  selectedControlPointsStr <- peekCString selectedControlPointsJson
  layerIdStr <- peekCString layerIdJson
  
  let selectedControlPointsBS = TE.encodeUtf8 (T.pack selectedControlPointsStr)
  let layerIdBS = TE.encodeUtf8 (T.pack layerIdStr)
  
  case (decode (BSL.fromStrict selectedControlPointsBS) :: Maybe [ControlPointSelection],
        decode (BSL.fromStrict layerIdBS) :: Maybe Text) of
    (Just points, Just layerId) -> do
      let result = getSelectedControlPointsForLayer points layerId
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [ControlPointSelection] and Text")

-- ============================================================================
-- PURE CALCULATION HELPERS
-- ============================================================================

-- | Compute range selection between two layer IDs
foreign export ccall "compute_range_selection"
  c_compute_range_selection :: CString -> CString -> CString -> IO CString

c_compute_range_selection :: CString -> CString -> CString -> IO CString
c_compute_range_selection startLayerIdJson endLayerIdJson orderedLayerIdsJson = do
  startLayerIdStr <- peekCString startLayerIdJson
  endLayerIdStr <- peekCString endLayerIdJson
  orderedLayerIdsStr <- peekCString orderedLayerIdsJson
  
  let startLayerIdBS = TE.encodeUtf8 (T.pack startLayerIdStr)
  let endLayerIdBS = TE.encodeUtf8 (T.pack endLayerIdStr)
  let orderedLayerIdsBS = TE.encodeUtf8 (T.pack orderedLayerIdsStr)
  
  case (decode (BSL.fromStrict startLayerIdBS) :: Maybe Text,
        decode (BSL.fromStrict endLayerIdBS) :: Maybe Text,
        decode (BSL.fromStrict orderedLayerIdsBS) :: Maybe [Text]) of
    (Just startId, Just endId, Just orderedIds) -> do
      let result = computeRangeSelection startId endId orderedIds
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Text, Text, and [Text]")

-- | Compute layer above current selection
foreign export ccall "compute_layer_above_selection"
  c_compute_layer_above_selection :: CString -> CString -> IO CString

c_compute_layer_above_selection :: CString -> CString -> IO CString
c_compute_layer_above_selection selectedLayerIdsJson orderedLayerIdsJson = do
  selectedLayerIdsStr <- peekCString selectedLayerIdsJson
  orderedLayerIdsStr <- peekCString orderedLayerIdsJson
  
  let selectedLayerIdsBS = TE.encodeUtf8 (T.pack selectedLayerIdsStr)
  let orderedLayerIdsBS = TE.encodeUtf8 (T.pack orderedLayerIdsStr)
  
  case (decode (BSL.fromStrict selectedLayerIdsBS) :: Maybe [Text],
        decode (BSL.fromStrict orderedLayerIdsBS) :: Maybe [Text]) of
    (Just ids, Just orderedIds) -> do
      let selectedIdsSet = HS.fromList ids
      let result = computeLayerAboveSelection selectedIdsSet orderedIds
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Text] and [Text]")

-- | Compute layer below current selection
foreign export ccall "compute_layer_below_selection"
  c_compute_layer_below_selection :: CString -> CString -> IO CString

c_compute_layer_below_selection :: CString -> CString -> IO CString
c_compute_layer_below_selection selectedLayerIdsJson orderedLayerIdsJson = do
  selectedLayerIdsStr <- peekCString selectedLayerIdsJson
  orderedLayerIdsStr <- peekCString orderedLayerIdsJson
  
  let selectedLayerIdsBS = TE.encodeUtf8 (T.pack selectedLayerIdsStr)
  let orderedLayerIdsBS = TE.encodeUtf8 (T.pack orderedLayerIdsStr)
  
  case (decode (BSL.fromStrict selectedLayerIdsBS) :: Maybe [Text],
        decode (BSL.fromStrict orderedLayerIdsBS) :: Maybe [Text]) of
    (Just ids, Just orderedIds) -> do
      let selectedIdsSet = HS.fromList ids
      let result = computeLayerBelowSelection selectedIdsSet orderedIds
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Text] and [Text]")
