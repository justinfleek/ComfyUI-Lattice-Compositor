-- |
-- Module      : Lattice.Services.ModelIntegrity
-- Description : Pure model integrity and validation functions
-- 
-- Migrated from src/lattice/nodes/lattice_layer_decomposition.py
-- Pure functions for hash computation, hash verification, and parameter validation
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.ModelIntegrity
  ( -- Hash computation
    computeHash
  , verifyHash
  -- Parameter validation
  , DecompositionParams(..)
  , validateDecompositionParams
  ) where

import Crypto.Hash.SHA256 (hash)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.Utils.NumericSafety
  ( validateFinite
  )

-- ============================================================================
-- HASH COMPUTATION
-- ============================================================================

-- | Compute SHA256 hash of bytes, returning hex digest
-- Pure function: deterministic, no IO
-- @param bytes - Input bytes to hash
-- @returns Hex digest as Text (lowercase hex)
-- Note: Digest SHA256 has Show instance that produces hex string
computeHash :: ByteString -> Text
computeHash bytes = T.pack (show (hash bytes))

-- | Verify hash matches expected value
-- Pure function: simple equality check
-- @param computed - Computed hash (hex digest)
-- @param expected - Expected hash (hex digest)
-- @returns True if hashes match
verifyHash :: Text -> Text -> Bool
verifyHash computed expected = computed == expected

-- ============================================================================
-- PARAMETER VALIDATION
-- ============================================================================

-- | Validated decomposition parameters
data DecompositionParams = DecompositionParams
  { paramsNumLayers :: Int  -- 3-8
  , paramsTrueCfgScale :: Double  -- > 0
  , paramsNumInferenceSteps :: Int  -- > 0
  , paramsResolution :: Int  -- 640 or 1024
  , paramsSeed :: Maybe Int  -- Non-negative
  } deriving (Eq, Show)

-- | Validate decomposition parameters
-- Pure function: deterministic validation
-- @param numLayers - Number of layers (3-8)
-- @param cfgScale - CFG scale (> 0)
-- @param steps - Inference steps (> 0)
-- @param resolution - Resolution (640 or 1024)
-- @param mSeed - Optional seed (non-negative)
-- @returns Either error message or validated parameters
validateDecompositionParams
  :: Int
  -> Double
  -> Int
  -> Int
  -> Maybe Int
  -> Either Text DecompositionParams
validateDecompositionParams numLayers cfgScale steps resolution mSeed
  | numLayers < 3 || numLayers > 8 =
      Left "num_layers must be between 3 and 8"
  | not (validateFinite cfgScale) || cfgScale <= 0 =
      Left "true_cfg_scale must be positive and finite"
  | steps <= 0 =
      Left "num_inference_steps must be positive"
  | resolution /= 640 && resolution /= 1024 =
      Left "resolution must be 640 or 1024"
  | maybe False (< 0) mSeed =
      Left "seed must be non-negative"
  | otherwise =
      Right $ DecompositionParams numLayers cfgScale steps resolution mSeed
