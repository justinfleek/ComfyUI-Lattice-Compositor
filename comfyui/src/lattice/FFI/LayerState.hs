-- |
-- Module      : Lattice.FFI.LayerState
-- Description : C FFI bindings for layer store pure functions
-- 
-- Exports pure functions from Lattice.State.Layer as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.LayerState where

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
import Foreign.C.Types (CInt)
import Lattice.State.Layer
  ( getLayerById
  , getLayerChildren
  , getLayerDescendants
  , getVisibleLayers
  , getDisplayedLayers
  , getRootLayers
  , getCameraLayers
  , getSelectedLayers
  , getSelectedLayer
  , isSplineAnimated
  , hasSplinePointKeyframes
  , samplePathPoints
  , approximateBezierLength
  , evaluateCubicBezier
  , evaluateCubicBezierDerivative
  )
import Lattice.Types.Layer
  ( Layer(..)
  )
import Lattice.Types.LayerDataSpline
  ( ControlPoint(..)
  )
import Lattice.Types.Primitives
  ( Vec2(..)
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
--                                                      // hierarchy // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Get a layer by ID
foreign export ccall "get_layer_by_id"
  c_get_layer_by_id :: CString -> CString -> IO CString
c_get_layer_by_id :: CString -> CString -> IO CString
c_get_layer_by_id layersJson layerIdJson = do
  layersStr <- peekCString layersJson
  layerIdStr <- peekCString layerIdJson
  
  let layersBS = TE.encodeUtf8 (T.pack layersStr)
  let layerIdBS = TE.encodeUtf8 (T.pack layerIdStr)
  
  case (decode (BSL.fromStrict layersBS) :: Maybe [Layer],
        decode (BSL.fromStrict layerIdBS) :: Maybe Text) of
    (Just layers, Just layerId) -> do
      let result = getLayerById layers layerId
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Layer] and Text")

-- | Get all children of a layer
foreign export ccall "get_layer_children"
  c_get_layer_children :: CString -> CString -> IO CString
c_get_layer_children :: CString -> CString -> IO CString
c_get_layer_children layersJson parentIdJson = do
  layersStr <- peekCString layersJson
  parentIdStr <- peekCString parentIdJson
  
  let layersBS = TE.encodeUtf8 (T.pack layersStr)
  let parentIdBS = TE.encodeUtf8 (T.pack parentIdStr)
  
  case (decode (BSL.fromStrict layersBS) :: Maybe [Layer],
        decode (BSL.fromStrict parentIdBS) :: Maybe Text) of
    (Just layers, Just parentId) -> do
      let result = getLayerChildren layers parentId
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Layer] and Text")

-- | Get all descendants of a layer (recursive)
foreign export ccall "get_layer_descendants"
  c_get_layer_descendants :: CString -> CString -> IO CString
c_get_layer_descendants :: CString -> CString -> IO CString
c_get_layer_descendants layersJson ancestorIdJson = do
  layersStr <- peekCString layersJson
  ancestorIdStr <- peekCString ancestorIdJson
  
  let layersBS = TE.encodeUtf8 (T.pack layersStr)
  let ancestorIdBS = TE.encodeUtf8 (T.pack ancestorIdStr)
  
  case (decode (BSL.fromStrict layersBS) :: Maybe [Layer],
        decode (BSL.fromStrict ancestorIdBS) :: Maybe Text) of
    (Just layers, Just ancestorId) -> do
      let result = getLayerDescendants layers ancestorId
      jsonToCString (successResponse (encode result))
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Layer] and Text")

-- | Get all visible layers
foreign export ccall "get_visible_layers"
  c_get_visible_layers :: CString -> IO CString
c_get_visible_layers :: CString -> IO CString
c_get_visible_layers layersJson = do
  layersStr <- peekCString layersJson
  
  let layersBS = TE.encodeUtf8 (T.pack layersStr)
  
  case decode (BSL.fromStrict layersBS) :: Maybe [Layer] of
    Just layers -> do
      let result = getVisibleLayers layers
      jsonToCString (successResponse (encode result))
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Layer]")

-- | Get layers displayed in timeline
foreign export ccall "get_displayed_layers"
  c_get_displayed_layers :: CString -> CInt -> IO CString
c_get_displayed_layers :: CString -> CInt -> IO CString
c_get_displayed_layers layersJson hideMinimizedInt = do
  layersStr <- peekCString layersJson
  let hideMinimized = hideMinimizedInt /= 0
  
  let layersBS = TE.encodeUtf8 (T.pack layersStr)
  
  case decode (BSL.fromStrict layersBS) :: Maybe [Layer] of
    Just layers -> do
      let result = getDisplayedLayers layers hideMinimized
      jsonToCString (successResponse (encode result))
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Layer]")

-- | Get root layers (layers with no parent)
foreign export ccall "get_root_layers"
  c_get_root_layers :: CString -> IO CString
c_get_root_layers :: CString -> IO CString
c_get_root_layers layersJson = do
  layersStr <- peekCString layersJson
  
  let layersBS = TE.encodeUtf8 (T.pack layersStr)
  
  case decode (BSL.fromStrict layersBS) :: Maybe [Layer] of
    Just layers -> do
      let result = getRootLayers layers
      jsonToCString (successResponse (encode result))
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Layer]")

-- | Get all camera layers
foreign export ccall "get_camera_layers"
  c_get_camera_layers :: CString -> IO CString
c_get_camera_layers :: CString -> IO CString
c_get_camera_layers layersJson = do
  layersStr <- peekCString layersJson
  
  let layersBS = TE.encodeUtf8 (T.pack layersStr)
  
  case decode (BSL.fromStrict layersBS) :: Maybe [Layer] of
    Just layers -> do
      let result = getCameraLayers layers
      jsonToCString (successResponse (encode result))
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [Layer]")

-- | Get all selected layers
foreign export ccall "get_selected_layers"
  c_get_selected_layers :: CString -> CString -> IO CString
c_get_selected_layers :: CString -> CString -> IO CString
c_get_selected_layers layersJson selectedIdsJson = do
  layersStr <- peekCString layersJson
  selectedIdsStr <- peekCString selectedIdsJson
  
  let layersBS = TE.encodeUtf8 (T.pack layersStr)
  let selectedIdsBS = TE.encodeUtf8 (T.pack selectedIdsStr)
  
  case (decode (BSL.fromStrict layersBS) :: Maybe [Layer],
        decode (BSL.fromStrict selectedIdsBS) :: Maybe [Text]) of
    (Just layers, Just selectedIds) -> do
      let selectedIdsSet = HS.fromList selectedIds
      let result = getSelectedLayers layers selectedIdsSet
      jsonToCString (successResponse (encode result))
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Layer] and [Text]")

-- | Get the single selected layer
foreign export ccall "get_selected_layer"
  c_get_selected_layer :: CString -> CString -> IO CString
c_get_selected_layer :: CString -> CString -> IO CString
c_get_selected_layer layersJson selectedIdsJson = do
  layersStr <- peekCString layersJson
  selectedIdsStr <- peekCString selectedIdsJson
  
  let layersBS = TE.encodeUtf8 (T.pack layersStr)
  let selectedIdsBS = TE.encodeUtf8 (T.pack selectedIdsStr)
  
  case (decode (BSL.fromStrict layersBS) :: Maybe [Layer],
        decode (BSL.fromStrict selectedIdsBS) :: Maybe [Text]) of
    (Just layers, Just selectedIds) -> do
      let selectedIdsSet = HS.fromList selectedIds
      let result = getSelectedLayer layers selectedIdsSet
      jsonToCString (successResponse (encode result))
    _ -> jsonToCString (errorResponse "Invalid JSON: expected [Layer] and [Text]")

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // spline // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if a spline layer has animation enabled
foreign export ccall "is_spline_animated"
  c_is_spline_animated :: CString -> IO CString
c_is_spline_animated :: CString -> IO CString
c_is_spline_animated layerJson = do
  layerStr <- peekCString layerJson
  
  let layerBS = TE.encodeUtf8 (T.pack layerStr)
  
  case decode (BSL.fromStrict layerBS) :: Maybe Layer of
    Just layer -> do
      let result = isSplineAnimated layer
      jsonToCString (successResponse (encode result))
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected Layer")

-- | Check if a control point has any keyframes
foreign export ccall "has_spline_point_keyframes"
  c_has_spline_point_keyframes :: CString -> CString -> IO CString
c_has_spline_point_keyframes :: CString -> CString -> IO CString
c_has_spline_point_keyframes layerJson pointIdJson = do
  layerStr <- peekCString layerJson
  pointIdStr <- peekCString pointIdJson
  
  let layerBS = TE.encodeUtf8 (T.pack layerStr)
  let pointIdBS = TE.encodeUtf8 (T.pack pointIdStr)
  
  case (decode (BSL.fromStrict layerBS) :: Maybe Layer,
        decode (BSL.fromStrict pointIdBS) :: Maybe Text) of
    (Just layer, Just pointId) -> do
      let result = hasSplinePointKeyframes layer pointId
      jsonToCString (successResponse (encode result))
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Layer and Text")

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // path // calculations
-- ════════════════════════════════════════════════════════════════════════════

-- | Sample points along a path
foreign export ccall "sample_path_points"
  c_sample_path_points :: CString -> CInt -> CInt -> IO CString
c_sample_path_points :: CString -> CInt -> CInt -> IO CString
c_sample_path_points controlPointsJson countInt closedInt = do
  controlPointsStr <- peekCString controlPointsJson
  let count = fromIntegral countInt
  let closed = closedInt /= 0
  
  let controlPointsBS = TE.encodeUtf8 (T.pack controlPointsStr)
  
  case decode (BSL.fromStrict controlPointsBS) :: Maybe [ControlPoint] of
    Just controlPoints -> do
      let result = samplePathPoints controlPoints count closed
      jsonToCString (successResponse (encode result))
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected [ControlPoint]")

-- | Approximate the length of a cubic bezier curve
foreign export ccall "approximate_bezier_length"
  c_approximate_bezier_length :: CString -> CString -> CString -> CString -> CInt -> IO CString
c_approximate_bezier_length :: CString -> CString -> CString -> CString -> CInt -> IO CString
c_approximate_bezier_length p0Json p1Json p2Json p3Json samplesInt = do
  p0Str <- peekCString p0Json
  p1Str <- peekCString p1Json
  p2Str <- peekCString p2Json
  p3Str <- peekCString p3Json
  let samples = fromIntegral samplesInt
  
  let p0BS = TE.encodeUtf8 (T.pack p0Str)
  let p1BS = TE.encodeUtf8 (T.pack p1Str)
  let p2BS = TE.encodeUtf8 (T.pack p2Str)
  let p3BS = TE.encodeUtf8 (T.pack p3Str)
  
  case (decode (BSL.fromStrict p0BS) :: Maybe Vec2,
        decode (BSL.fromStrict p1BS) :: Maybe Vec2,
        decode (BSL.fromStrict p2BS) :: Maybe Vec2,
        decode (BSL.fromStrict p3BS) :: Maybe Vec2) of
    (Just p0, Just p1, Just p2, Just p3) -> do
      let result = approximateBezierLength p0 p1 p2 p3 samples
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Vec2, Vec2, Vec2, Vec2")

-- | Evaluate a cubic bezier curve at parameter t
foreign export ccall "evaluate_cubic_bezier"
  c_evaluate_cubic_bezier :: CString -> CString -> CString -> CString -> CString -> IO CString
c_evaluate_cubic_bezier :: CString -> CString -> CString -> CString -> CString -> IO CString
c_evaluate_cubic_bezier p0Json p1Json p2Json p3Json tJson = do
  p0Str <- peekCString p0Json
  p1Str <- peekCString p1Json
  p2Str <- peekCString p2Json
  p3Str <- peekCString p3Json
  tStr <- peekCString tJson
  
  let p0BS = TE.encodeUtf8 (T.pack p0Str)
  let p1BS = TE.encodeUtf8 (T.pack p1Str)
  let p2BS = TE.encodeUtf8 (T.pack p2Str)
  let p3BS = TE.encodeUtf8 (T.pack p3Str)
  let tBS = TE.encodeUtf8 (T.pack tStr)
  
  case (decode (BSL.fromStrict p0BS) :: Maybe Vec2,
        decode (BSL.fromStrict p1BS) :: Maybe Vec2,
        decode (BSL.fromStrict p2BS) :: Maybe Vec2,
        decode (BSL.fromStrict p3BS) :: Maybe Vec2,
        decode (BSL.fromStrict tBS) :: Maybe Double) of
    (Just p0, Just p1, Just p2, Just p3, Just t) -> do
      let result = evaluateCubicBezier p0 p1 p2 p3 t
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Vec2, Vec2, Vec2, Vec2, Double")

-- | Evaluate the derivative of a cubic bezier curve at parameter t
foreign export ccall "evaluate_cubic_bezier_derivative"
  c_evaluate_cubic_bezier_derivative :: CString -> CString -> CString -> CString -> CString -> IO CString
c_evaluate_cubic_bezier_derivative :: CString -> CString -> CString -> CString -> CString -> IO CString
c_evaluate_cubic_bezier_derivative p0Json p1Json p2Json p3Json tJson = do
  p0Str <- peekCString p0Json
  p1Str <- peekCString p1Json
  p2Str <- peekCString p2Json
  p3Str <- peekCString p3Json
  tStr <- peekCString tJson
  
  let p0BS = TE.encodeUtf8 (T.pack p0Str)
  let p1BS = TE.encodeUtf8 (T.pack p1Str)
  let p2BS = TE.encodeUtf8 (T.pack p2Str)
  let p3BS = TE.encodeUtf8 (T.pack p3Str)
  let tBS = TE.encodeUtf8 (T.pack tStr)
  
  case (decode (BSL.fromStrict p0BS) :: Maybe Vec2,
        decode (BSL.fromStrict p1BS) :: Maybe Vec2,
        decode (BSL.fromStrict p2BS) :: Maybe Vec2,
        decode (BSL.fromStrict p3BS) :: Maybe Vec2,
        decode (BSL.fromStrict tBS) :: Maybe Double) of
    (Just p0, Just p1, Just p2, Just p3, Just t) -> do
      let result = evaluateCubicBezierDerivative p0 p1 p2 p3 t
      jsonToCString (successResponse result)
    _ -> jsonToCString (errorResponse "Invalid JSON: expected Vec2, Vec2, Vec2, Vec2, Double")
