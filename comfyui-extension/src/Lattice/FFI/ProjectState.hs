-- |
-- Module      : Lattice.FFI.ProjectState
-- Description : C FFI exports for Project State management functions
-- 
-- Exports Haskell pure state functions as C-compatible functions for TypeScript/Python interop
-- All functions use JSON for input/output since they work with LatticeProject types
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ProjectState where

import Foreign.C.Types (CInt(..), CDouble(..))
import Foreign.C.String (CString, peekCString, newCString)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson
  ( Value(..)
  , object
  , (.=)
  , decode
  , encode
  , ToJSON(..)
  , FromJSON(..)
  )
import qualified Data.HashSet as HS

import Lattice.State.Project
  ( getOpenCompositions
  , getBreadcrumbPath
  , getActiveComposition
  , getActiveCompositionLayers
  , getWidth
  , getHeight
  , getFrameCount
  , getFps
  , getDuration
  , getBackgroundColor
  , getCurrentTime
  , hasProject
  , findUsedAssetIds
  , getExtensionForAsset
  , createDefaultProject
  )
import Lattice.Types.Project
  ( LatticeProject(..)
  , Composition(..)
  , AssetReference(..)
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
-- COMPOSITION GETTERS
-- ============================================================================

-- | Export getOpenCompositions as C function
-- C signature: char* get_open_compositions(char* project_json, char* open_ids_json)
-- Returns: JSON array of compositions
foreign export ccall "get_open_compositions"
  c_get_open_compositions :: CString -> CString -> IO CString

c_get_open_compositions :: CString -> CString -> IO CString
c_get_open_compositions projectJsonPtr openIdsJsonPtr = do
  projectStr <- peekCString projectJsonPtr
  openIdsStr <- peekCString openIdsJsonPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  let openIdsBS = TE.encodeUtf8 (T.pack openIdsStr)
  
  case (decode (BSL.fromStrict projectBS) :: Maybe LatticeProject, decode (BSL.fromStrict openIdsBS) :: Maybe [T.Text]) of
    (Nothing, _) -> jsonToCString (errorResponse "Invalid project JSON")
    (_, Nothing) -> jsonToCString (errorResponse "Invalid open IDs JSON")
    (Just project, Just openIds) -> do
      let compositions = getOpenCompositions project openIds
      jsonToCString (successResponse compositions)

-- | Export getBreadcrumbPath as C function
-- C signature: char* get_breadcrumb_path(char* project_json, char* breadcrumbs_json)
-- Returns: JSON array of {id, name} objects
foreign export ccall "get_breadcrumb_path"
  c_get_breadcrumb_path :: CString -> CString -> IO CString

c_get_breadcrumb_path :: CString -> CString -> IO CString
c_get_breadcrumb_path projectJsonPtr breadcrumbsJsonPtr = do
  projectStr <- peekCString projectJsonPtr
  breadcrumbsStr <- peekCString breadcrumbsJsonPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  let breadcrumbsBS = TE.encodeUtf8 (T.pack breadcrumbsStr)
  
  case (decode (BSL.fromStrict projectBS) :: Maybe LatticeProject, decode (BSL.fromStrict breadcrumbsBS) :: Maybe [T.Text]) of
    (Nothing, _) -> jsonToCString (errorResponse "Invalid project JSON")
    (_, Nothing) -> jsonToCString (errorResponse "Invalid breadcrumbs JSON")
    (Just project, Just breadcrumbs) -> do
      let path = getBreadcrumbPath project breadcrumbs
      -- Convert (Text, Text) pairs to JSON objects
      let pathObjects = map (\(id_, name) -> object ["id" .= id_, "name" .= name]) path
      jsonToCString (successResponse pathObjects)

-- | Export getActiveComposition as C function
-- C signature: char* get_active_composition(char* project_json, char* active_id)
-- Returns: JSON composition or null
foreign export ccall "get_active_composition"
  c_get_active_composition :: CString -> CString -> IO CString

c_get_active_composition :: CString -> CString -> IO CString
c_get_active_composition projectJsonPtr activeIdPtr = do
  projectStr <- peekCString projectJsonPtr
  activeIdStr <- peekCString activeIdPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let mComp = getActiveComposition project (T.pack activeIdStr)
      jsonToCString (successResponse mComp)

-- | Export getActiveCompositionLayers as C function
-- C signature: char* get_active_composition_layers(char* project_json, char* active_id)
-- Returns: JSON array of layers
foreign export ccall "get_active_composition_layers"
  c_get_active_composition_layers :: CString -> CString -> IO CString

c_get_active_composition_layers :: CString -> CString -> IO CString
c_get_active_composition_layers projectJsonPtr activeIdPtr = do
  projectStr <- peekCString projectJsonPtr
  activeIdStr <- peekCString activeIdPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let layers = getActiveCompositionLayers project (T.pack activeIdStr)
      jsonToCString (successResponse layers)

-- ============================================================================
-- COMPOSITION PROPERTY GETTERS
-- ============================================================================

-- | Export getWidth as C function
-- C signature: char* get_width(char* project_json, char* active_id)
-- Returns: JSON with width (double)
foreign export ccall "get_width"
  c_get_width :: CString -> CString -> IO CString

c_get_width :: CString -> CString -> IO CString
c_get_width projectJsonPtr activeIdPtr = do
  projectStr <- peekCString projectJsonPtr
  activeIdStr <- peekCString activeIdPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let width = getWidth project (T.pack activeIdStr)
      jsonToCString (successResponse width)

-- | Export getHeight as C function
foreign export ccall "get_height"
  c_get_height :: CString -> CString -> IO CString

c_get_height :: CString -> CString -> IO CString
c_get_height projectJsonPtr activeIdPtr = do
  projectStr <- peekCString projectJsonPtr
  activeIdStr <- peekCString activeIdPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let height = getHeight project (T.pack activeIdStr)
      jsonToCString (successResponse height)

-- | Export getFrameCount as C function
foreign export ccall "get_frame_count"
  c_get_frame_count :: CString -> CString -> IO CString

c_get_frame_count :: CString -> CString -> IO CString
c_get_frame_count projectJsonPtr activeIdPtr = do
  projectStr <- peekCString projectJsonPtr
  activeIdStr <- peekCString activeIdPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let frameCount = getFrameCount project (T.pack activeIdStr)
      jsonToCString (successResponse frameCount)

-- | Export getFps as C function
foreign export ccall "get_fps"
  c_get_fps :: CString -> CString -> IO CString

c_get_fps :: CString -> CString -> IO CString
c_get_fps projectJsonPtr activeIdPtr = do
  projectStr <- peekCString projectJsonPtr
  activeIdStr <- peekCString activeIdPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let fps = getFps project (T.pack activeIdStr)
      jsonToCString (successResponse fps)

-- | Export getDuration as C function
foreign export ccall "get_duration"
  c_get_duration :: CString -> CString -> IO CString

c_get_duration :: CString -> CString -> IO CString
c_get_duration projectJsonPtr activeIdPtr = do
  projectStr <- peekCString projectJsonPtr
  activeIdStr <- peekCString activeIdPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let duration = getDuration project (T.pack activeIdStr)
      jsonToCString (successResponse duration)

-- | Export getBackgroundColor as C function
foreign export ccall "get_background_color"
  c_get_background_color :: CString -> CString -> IO CString

c_get_background_color :: CString -> CString -> IO CString
c_get_background_color projectJsonPtr activeIdPtr = do
  projectStr <- peekCString projectJsonPtr
  activeIdStr <- peekCString activeIdPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let bgColor = getBackgroundColor project (T.pack activeIdStr)
      jsonToCString (successResponse bgColor)

-- | Export getCurrentTime as C function
foreign export ccall "get_current_time"
  c_get_current_time :: CString -> CString -> IO CString

c_get_current_time :: CString -> CString -> IO CString
c_get_current_time projectJsonPtr activeIdPtr = do
  projectStr <- peekCString projectJsonPtr
  activeIdStr <- peekCString activeIdPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let currentTime = getCurrentTime project (T.pack activeIdStr)
      jsonToCString (successResponse currentTime)

-- ============================================================================
-- PROJECT STATE QUERIES
-- ============================================================================

-- | Export hasProject as C function
-- C signature: char* has_project(char* source_image_json)
-- Returns: JSON with boolean result
foreign export ccall "has_project"
  c_has_project :: CString -> IO CString

c_has_project :: CString -> IO CString
c_has_project sourceImageJsonPtr = do
  sourceImageStr <- peekCString sourceImageJsonPtr
  
  let sourceImageBS = TE.encodeUtf8 (T.pack sourceImageStr)
  
  case decode (BSL.fromStrict sourceImageBS) :: Maybe (Maybe T.Text) of
    Nothing -> jsonToCString (errorResponse "Invalid source image JSON")
    Just mSourceImage -> do
      let result = hasProject mSourceImage
      jsonToCString (successResponse result)

-- ============================================================================
-- ASSET UTILITIES
-- ============================================================================

-- | Export findUsedAssetIds as C function
-- C signature: char* find_used_asset_ids(char* project_json)
-- Returns: JSON array of asset IDs (strings)
foreign export ccall "find_used_asset_ids"
  c_find_used_asset_ids :: CString -> IO CString

c_find_used_asset_ids :: CString -> IO CString
c_find_used_asset_ids projectJsonPtr = do
  projectStr <- peekCString projectJsonPtr
  
  let projectBS = TE.encodeUtf8 (T.pack projectStr)
  
  case decode (BSL.fromStrict projectBS) :: Maybe LatticeProject of
    Nothing -> jsonToCString (errorResponse "Invalid project JSON")
    Just project -> do
      let assetIds = HS.toList (findUsedAssetIds project)
      jsonToCString (successResponse assetIds)

-- | Export getExtensionForAsset as C function
-- C signature: char* get_extension_for_asset(char* asset_json)
-- Returns: JSON with extension string
foreign export ccall "get_extension_for_asset"
  c_get_extension_for_asset :: CString -> IO CString

c_get_extension_for_asset :: CString -> IO CString
c_get_extension_for_asset assetJsonPtr = do
  assetStr <- peekCString assetJsonPtr
  
  let assetBS = TE.encodeUtf8 (T.pack assetStr)
  
  case decode (BSL.fromStrict assetBS) :: Maybe AssetReference of
    Nothing -> jsonToCString (errorResponse "Invalid asset JSON")
    Just asset -> do
      let extension = getExtensionForAsset asset
      jsonToCString (successResponse extension)

-- ============================================================================
-- PROJECT CREATION
-- ============================================================================

-- | Export createDefaultProject as C function
-- C signature: char* create_default_project(char* main_comp_id)
-- Returns: JSON with default project
foreign export ccall "create_default_project"
  c_create_default_project :: CString -> IO CString

c_create_default_project :: CString -> IO CString
c_create_default_project mainCompIdPtr = do
  mainCompIdStr <- peekCString mainCompIdPtr
  
  let project = createDefaultProject (T.pack mainCompIdStr)
  jsonToCString (successResponse project)
