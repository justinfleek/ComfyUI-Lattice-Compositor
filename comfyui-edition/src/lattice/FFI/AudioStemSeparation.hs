-- |
-- Module      : Lattice.FFI.AudioStemSeparation
-- Description : C FFI exports for AudioStemSeparation service
-- 
-- Exports Haskell functions as C-compatible functions for Python interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.AudioStemSeparation where

import Foreign.C.Types (CDouble(..))
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.Ptr (Ptr)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson (Value(..), object, (.=), (.:), (.:?), decode, encode, withObject, FromJSON(..))
import Data.Aeson.Key (fromText)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Lattice.Services.AudioStemSeparation
  ( getModelConfig
  , getAvailableModels
  , getAttributionInfo
  , validateStemSeparationParams
  , StemSeparationParams(..)
  , DemucsModel(..)
  , Attribution(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // model // configuration
-- ════════════════════════════════════════════════════════════════════════════

-- | Export getModelConfig as C function
-- C signature: char* get_model_config(char* model_name)
-- Returns: JSON string with model config or null
-- Memory: Caller must free the returned CString using free()
foreign export ccall "get_model_config"
  c_get_model_config :: CString -> IO CString

c_get_model_config :: CString -> IO CString
c_get_model_config modelNamePtr = do
  modelNameStr <- peekCString modelNamePtr
  let modelName = T.pack modelNameStr
  
  case getModelConfig modelName of
    Nothing -> do
      let result = object [fromText "status" .= (T.pack "not_found")]
      let resultBS = BSL.toStrict (encode result)
      let resultText = TE.decodeUtf8 resultBS
      newCString (T.unpack resultText)
    Just model -> do
      let result = object
            [ fromText "status" .= (T.pack "success")
            , fromText "model" .= object
                [ fromText "id" .= modelId model
                , fromText "displayName" .= modelDisplayName model
                , fromText "description" .= modelDescription model
                , fromText "stems" .= modelStems model
                , fromText "sampleRate" .= modelSampleRate model
                , fromText "recommended" .= modelRecommended model
                ]
            ]
      let resultBS = BSL.toStrict (encode result)
      let resultText = TE.decodeUtf8 resultBS
      newCString (T.unpack resultText)

-- | Export getAvailableModels as C function
-- C signature: char* get_available_models()
-- Returns: JSON array of all available models
-- Memory: Caller must free the returned CString using free()
foreign export ccall "get_available_models"
  c_get_available_models :: IO CString

c_get_available_models :: IO CString
c_get_available_models = do
  let models = getAvailableModels
  let modelsJSON = map (\m -> object
        [ fromText "id" .= modelId m
        , fromText "displayName" .= modelDisplayName m
        , fromText "description" .= modelDescription m
        , fromText "stems" .= modelStems m
        , fromText "sampleRate" .= modelSampleRate m
        , fromText "recommended" .= modelRecommended m
        ]) models
  let result = object [fromText "status" .= (T.pack "success"), fromText "models" .= modelsJSON]
  let resultBS = BSL.toStrict (encode result)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)

-- | Export getAttributionInfo as C function
-- C signature: char* get_attribution_info()
-- Returns: JSON object with attribution information
-- Memory: Caller must free the returned CString using free()
foreign export ccall "get_attribution_info"
  c_get_attribution_info :: IO CString

c_get_attribution_info :: IO CString
c_get_attribution_info = do
  let attrib = getAttributionInfo
  let attribJSON = Map.mapWithKey (\_k v -> object
        [ fromText "id" .= attributionId v
        , fromText "name" .= attributionName v
        , fromText "repo" .= attributionRepo v
        , fromText "author" .= attributionAuthor v
        , fromText "license" .= attributionLicense v
        , fromText "note" .= attributionNote v
        ]) attrib
  let result = object [fromText "status" .= (T.pack "success"), fromText "attribution" .= attribJSON]
  let resultBS = BSL.toStrict (encode result)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // parameter // validation
-- ════════════════════════════════════════════════════════════════════════════

-- | Input JSON structure for validateStemSeparationParams
-- Expected format: {"modelName": "htdemucs", "segmentLength": 10.0, "overlap": 0.1, "stems": null}
data StemSeparationParamsInput = StemSeparationParamsInput
  { inputModelName :: Text
  , inputSegmentLength :: Double
  , inputOverlap :: Double
  , inputStems :: Maybe [Text]
  } deriving (Eq, Show)

instance FromJSON StemSeparationParamsInput where
  parseJSON = withObject "StemSeparationParamsInput" $ \o -> do
    modelName <- o .: fromText "modelName"
    segmentLength <- o .: fromText "segmentLength"
    overlap <- o .: fromText "overlap"
    mStems <- o .:? fromText "stems"
    return $ StemSeparationParamsInput modelName segmentLength overlap mStems

-- | Output JSON structure (either error or success)
encodeStemSeparationResult :: Either Text StemSeparationParams -> Value
encodeStemSeparationResult (Left err) = object
  [ fromText "status" .= (T.pack "error")
  , fromText "message" .= err
  ]
encodeStemSeparationResult (Right params) = object
  [ fromText "status" .= (T.pack "success")
  , fromText "params" .= object
      [ fromText "modelName" .= paramsModelName params
      , fromText "segmentLength" .= paramsSegmentLength params
      , fromText "overlap" .= paramsOverlap params
      , fromText "stems" .= paramsStemsToReturn params
      ]
  ]

-- | Export validateStemSeparationParams as C function
-- C signature: char* validate_stem_separation_params(char* json_input)
-- Returns: JSON string with either error or validated params
-- Memory: Caller must free the returned CString using free()
foreign export ccall "validate_stem_separation_params"
  c_validate_stem_separation_params :: CString -> IO CString

c_validate_stem_separation_params :: CString -> IO CString
c_validate_stem_separation_params jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  -- Parse JSON input
  case decode (BSL.fromStrict inputBS) :: Maybe StemSeparationParamsInput of
    Nothing -> do
      let errorResult = encodeStemSeparationResult (Left (T.pack "Invalid JSON input"))
      let resultJSON = BSL.toStrict (encode errorResult)
      let resultText = TE.decodeUtf8 resultJSON
      newCString (T.unpack resultText)
    Just input -> do
      let result = validateStemSeparationParams
            (inputModelName input)
            (inputSegmentLength input)
            (inputOverlap input)
            (inputStems input)
      
      let resultJSON = encodeStemSeparationResult result
      let resultBS = BSL.toStrict (encode resultJSON)
      let resultText = TE.decodeUtf8 resultBS
      newCString (T.unpack resultText)
