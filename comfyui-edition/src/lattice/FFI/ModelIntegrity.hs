-- |
-- Module      : Lattice.FFI.ModelIntegrity
-- Description : C FFI exports for ModelIntegrity service
-- 
-- Exports Haskell functions as C-compatible functions for Python interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ModelIntegrity where

import Foreign.C.Types (CInt(..))
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.Ptr (Ptr, castPtr)
import Foreign.Marshal.Array (peekArray)
import Data.Word (Word8)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson (Value(..), object, (.=), (.:), (.:?), decode, encode, withObject, FromJSON(..))
import Data.Aeson.Key (fromText)

import Lattice.Services.ModelIntegrity
  ( computeHash
  , verifyHash
  , validateDecompositionParams
  , DecompositionParams(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hash // computation
-- ════════════════════════════════════════════════════════════════════════════

-- | Export computeHash as C function
-- C signature: char* compute_hash(char* bytes, int length)
-- Returns: Hex digest as CString (caller must free)
-- Note: Input is raw bytes, not base64 encoded
foreign export ccall "compute_hash"
  c_compute_hash :: CString -> CInt -> IO CString

c_compute_hash :: CString -> CInt -> IO CString
c_compute_hash bytesPtr (CInt len) = do
  -- Read raw bytes from memory (treating CString as byte array)
  -- Note: CString is char* which is byte array for binary data
  bytesArray <- peekArray (fromIntegral len) (castPtr bytesPtr)
  let bytes = BS.pack bytesArray
  -- Compute hash
  let hashText = computeHash bytes
  -- Convert to CString
  newCString (T.unpack hashText)

-- | Export verifyHash as C function
-- C signature: int verify_hash(char* computed, char* expected)
-- Returns: 1 if hashes match, 0 otherwise
foreign export ccall "verify_hash"
  c_verify_hash :: CString -> CString -> IO CInt

c_verify_hash :: CString -> CString -> IO CInt
c_verify_hash computedPtr expectedPtr = do
  computedStr <- peekCString computedPtr
  expectedStr <- peekCString expectedPtr
  if verifyHash (T.pack computedStr) (T.pack expectedStr)
    then return (CInt 1)
    else return (CInt 0)

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // parameter // validation
-- ════════════════════════════════════════════════════════════════════════════

-- | Input JSON structure for validateDecompositionParams
-- Expected format: {"numLayers": 5, "cfgScale": 4.0, "steps": 50, "resolution": 640, "seed": null}
data DecompositionParamsInput = DecompositionParamsInput
  { inputNumLayers :: Int
  , inputCfgScale :: Double
  , inputSteps :: Int
  , inputResolution :: Int
  , inputSeed :: Maybe Int
  } deriving (Eq, Show)

instance FromJSON DecompositionParamsInput where
  parseJSON = withObject "DecompositionParamsInput" $ \o -> do
    numLayers <- o .: fromText "numLayers"
    cfgScale <- o .: fromText "cfgScale"
    steps <- o .: fromText "steps"
    resolution <- o .: fromText "resolution"
    mSeed <- o .:? fromText "seed"
    return $ DecompositionParamsInput numLayers cfgScale steps resolution mSeed

-- | Output JSON structure (either error or success)
encodeDecompositionResult :: Either Text DecompositionParams -> Value
encodeDecompositionResult (Left err) = object
  [ "status" .= ("error" :: Text)
  , "message" .= err
  ]
encodeDecompositionResult (Right params) = object
  [ "status" .= ("success" :: Text)
  , "params" .= object
      [ "numLayers" .= paramsNumLayers params
      , "cfgScale" .= paramsTrueCfgScale params
      , "steps" .= paramsNumInferenceSteps params
      , "resolution" .= paramsResolution params
      , "seed" .= paramsSeed params
      ]
  ]

-- | Export validateDecompositionParams as C function
-- C signature: char* validate_decomposition_params(char* json_input)
-- Returns: JSON string with either error or validated params
-- Memory: Caller must free the returned CString using free()
foreign export ccall "validate_decomposition_params"
  c_validate_decomposition_params :: CString -> IO CString

c_validate_decomposition_params :: CString -> IO CString
c_validate_decomposition_params jsonInput = do
  inputStr <- peekCString jsonInput
  let inputBS = TE.encodeUtf8 (T.pack inputStr)
  
  -- Parse JSON input
  case decode (BSL.fromStrict inputBS) :: Maybe DecompositionParamsInput of
    Nothing -> do
      let errorResult = encodeDecompositionResult (Left (T.pack "Invalid JSON input"))
      let resultJSON = BSL.toStrict (encode errorResult)
      let resultText = TE.decodeUtf8 resultJSON
      newCString (T.unpack resultText)
    Just input -> do
      let result = validateDecompositionParams
            (inputNumLayers input)
            (inputCfgScale input)
            (inputSteps input)
            (inputResolution input)
            (inputSeed input)
      
      let resultJSON = encodeDecompositionResult result
      let resultBS = BSL.toStrict (encode resultJSON)
      let resultText = TE.decodeUtf8 resultBS
      newCString (T.unpack resultText)
