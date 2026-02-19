-- |
-- Module      : Lattice.FFI.AssetState
-- Description : C FFI bindings for asset store pure functions
-- 
-- Exports pure functions from Lattice.State.Asset as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.AssetState where

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
import Lattice.State.Asset
  ( materialList
  , selectedMaterial
  , svgDocumentList
  , selectedSvgDocument
  , meshParticleList
  , selectedMeshParticle
  , spriteSheetList
  , selectedSpriteSheet
  , isLoading
  , createDefaultMaterialConfig
  , AssetState(..)
  , PBRMaterialConfig(..)
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

-- | Get material list
foreign export ccall "material_list"
  c_material_list :: CString -> IO CString

c_material_list :: CString -> IO CString
c_material_list assetStateJson = do
  assetStateStr <- peekCString assetStateJson
  
  let assetStateBS = TE.encodeUtf8 (T.pack assetStateStr)
  
  case decode (BSL.fromStrict assetStateBS) :: Maybe AssetState of
    Just state -> do
      let result = materialList state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AssetState")

-- | Get selected material
foreign export ccall "selected_material"
  c_selected_material :: CString -> IO CString

c_selected_material :: CString -> IO CString
c_selected_material assetStateJson = do
  assetStateStr <- peekCString assetStateJson
  
  let assetStateBS = TE.encodeUtf8 (T.pack assetStateStr)
  
  case decode (BSL.fromStrict assetStateBS) :: Maybe AssetState of
    Just state -> do
      let result = selectedMaterial state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AssetState")

-- | Get SVG document list
foreign export ccall "svg_document_list"
  c_svg_document_list :: CString -> IO CString

c_svg_document_list :: CString -> IO CString
c_svg_document_list assetStateJson = do
  assetStateStr <- peekCString assetStateJson
  
  let assetStateBS = TE.encodeUtf8 (T.pack assetStateStr)
  
  case decode (BSL.fromStrict assetStateBS) :: Maybe AssetState of
    Just state -> do
      let result = svgDocumentList state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AssetState")

-- | Get selected SVG document
foreign export ccall "selected_svg_document"
  c_selected_svg_document :: CString -> IO CString

c_selected_svg_document :: CString -> IO CString
c_selected_svg_document assetStateJson = do
  assetStateStr <- peekCString assetStateJson
  
  let assetStateBS = TE.encodeUtf8 (T.pack assetStateStr)
  
  case decode (BSL.fromStrict assetStateBS) :: Maybe AssetState of
    Just state -> do
      let result = selectedSvgDocument state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AssetState")

-- | Get mesh particle list
foreign export ccall "mesh_particle_list"
  c_mesh_particle_list :: CString -> IO CString

c_mesh_particle_list :: CString -> IO CString
c_mesh_particle_list assetStateJson = do
  assetStateStr <- peekCString assetStateJson
  
  let assetStateBS = TE.encodeUtf8 (T.pack assetStateStr)
  
  case decode (BSL.fromStrict assetStateBS) :: Maybe AssetState of
    Just state -> do
      let result = meshParticleList state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AssetState")

-- | Get selected mesh particle
foreign export ccall "selected_mesh_particle"
  c_selected_mesh_particle :: CString -> IO CString

c_selected_mesh_particle :: CString -> IO CString
c_selected_mesh_particle assetStateJson = do
  assetStateStr <- peekCString assetStateJson
  
  let assetStateBS = TE.encodeUtf8 (T.pack assetStateStr)
  
  case decode (BSL.fromStrict assetStateBS) :: Maybe AssetState of
    Just state -> do
      let result = selectedMeshParticle state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AssetState")

-- | Get sprite sheet list
foreign export ccall "sprite_sheet_list"
  c_sprite_sheet_list :: CString -> IO CString

c_sprite_sheet_list :: CString -> IO CString
c_sprite_sheet_list assetStateJson = do
  assetStateStr <- peekCString assetStateJson
  
  let assetStateBS = TE.encodeUtf8 (T.pack assetStateStr)
  
  case decode (BSL.fromStrict assetStateBS) :: Maybe AssetState of
    Just state -> do
      let result = spriteSheetList state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AssetState")

-- | Get selected sprite sheet
foreign export ccall "selected_sprite_sheet"
  c_selected_sprite_sheet :: CString -> IO CString

c_selected_sprite_sheet :: CString -> IO CString
c_selected_sprite_sheet assetStateJson = do
  assetStateStr <- peekCString assetStateJson
  
  let assetStateBS = TE.encodeUtf8 (T.pack assetStateStr)
  
  case decode (BSL.fromStrict assetStateBS) :: Maybe AssetState of
    Just state -> do
      let result = selectedSpriteSheet state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AssetState")

-- | Check if any asset is loading
foreign export ccall "is_loading"
  c_is_loading :: CString -> IO CString

c_is_loading :: CString -> IO CString
c_is_loading assetStateJson = do
  assetStateStr <- peekCString assetStateJson
  
  let assetStateBS = TE.encodeUtf8 (T.pack assetStateStr)
  
  case decode (BSL.fromStrict assetStateBS) :: Maybe AssetState of
    Just state -> do
      let result = isLoading state
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected AssetState")

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // pure // calculations
-- ════════════════════════════════════════════════════════════════════════════

-- | Create default material config
foreign export ccall "create_default_material_config"
  c_create_default_material_config :: CString -> CString -> IO CString

c_create_default_material_config :: CString -> CString -> IO CString
c_create_default_material_config idJson nameJson = do
  idStr <- peekCString idJson
  nameStr <- peekCString nameJson
  
  let idText = T.pack idStr
  let nameText = T.pack nameStr
  
  let result = createDefaultMaterialConfig idText nameText
  jsonToCString (successResponse result)
