-- |
-- Module      : Lattice.State.Cache
-- Description : Pure state management functions for cache store
-- 
-- Migrated from ui/src/stores/cacheStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Cache
  ( -- Helper functions
    computeProjectHash
  -- State type
  , CacheState(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , Value(..)
  , encode
  )
import qualified Data.ByteString.Lazy as BSL
import Data.HashMap.Strict (HashMap)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Bits ((.&.))
import GHC.Generics (Generic)

-- ============================================================================
-- CACHE STATE
-- ============================================================================

-- | Cache store state
data CacheState = CacheState
  { cacheStateFrameCacheEnabled :: Bool
  , cacheStateProjectStateHash :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON CacheState where
  toJSON (CacheState enabled hash) =
    object
      [ "frameCacheEnabled" .= enabled
      , "projectStateHash" .= hash
      ]

instance FromJSON CacheState where
  parseJSON = withObject "CacheState" $ \o -> do
    enabled <- o .: "frameCacheEnabled"
    hash <- o .: "projectStateHash"
    return (CacheState enabled hash)

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Compute hash of project state for cache invalidation
-- Pure function: takes composition ID, modified timestamp, layer count, layer IDs, settings, returns hash
-- 
-- Algorithm: Creates fingerprint object, stringifies it, computes hash using simple hash algorithm
-- Equivalent to TypeScript: hash = hash * 31 + char
computeProjectHash ::
  Text -> -- compositionId (for context, not used in hash)
  Text -> -- modified timestamp
  Int -> -- layer count
  [Text] -> -- layer IDs
  Value -> -- settings (JSON object)
  Text
computeProjectHash _compId modified layerCount layerIds settings =
  let
    -- Create fingerprint object
    layerIdsStr = T.intercalate "," layerIds
    
    -- Try to stringify fingerprint (with settings)
    fingerprintStr = case encodeFingerprint modified layerCount layerIdsStr settings of
      Just str -> str
      Nothing ->
        let
          layerCountStr = T.pack (show layerCount)
          cacheKey = layerCountStr <> ":" <> layerIdsStr <> ":" <> modified
        in cacheKey
    
    -- Compute hash using simple algorithm: hash = hash * 31 + char
    hash = T.foldl' computeHashChar 0 fingerprintStr
  in
    -- Convert to hex string
    T.pack (showHex hash "")

-- | Encode fingerprint as JSON string
encodeFingerprint :: Text -> Int -> Text -> Value -> Maybe Text
encodeFingerprint modified layerCount layerIds settings =
  let
    fingerprint = object
      [ "layerCount" .= layerCount
      , "layerIds" .= layerIds
      , "modified" .= modified
      , "settings" .= settings
      ]
    jsonBytes = encode fingerprint
    jsonText = TE.decodeUtf8 (BSL.toStrict jsonBytes)
  in
    Just jsonText

-- | Compute hash character by character
-- Algorithm: hash = hash * 31 + char (equivalent to (hash << 5) - hash + char)
computeHashChar :: Int -> Char -> Int
computeHashChar hash char =
  let
    charCode = fromEnum char
    -- hash * 31 + char (31 = 32 - 1 = (1 << 5) - 1)
    newHash = hash * 31 + charCode
  in
    -- Mask to 32-bit integer (equivalent to hash & hash in JavaScript)
    newHash .&. 0xFFFFFFFF

-- | Convert Int to hex string (handles negative by converting to unsigned)
showHex :: Int -> String -> String
showHex n acc =
  let
    -- Convert to unsigned 32-bit integer
    unsigned = n .&. 0xFFFFFFFF
  in
    showHexUnsigned unsigned acc

-- | Convert unsigned Int to hex string
showHexUnsigned :: Int -> String -> String
showHexUnsigned n acc
  | n == 0 = if null acc then "0" else acc
  | otherwise =
      let
        remainder = n `mod` 16
        digit = if remainder < 10
          then toEnum (fromEnum '0' + remainder)
          else toEnum (fromEnum 'a' + remainder - 10)
      in
        showHexUnsigned (n `div` 16) (digit : acc)
