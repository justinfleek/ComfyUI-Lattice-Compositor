-- |
-- Module      : Lattice.FFI.HaskellToPureScript
-- Description : Convert Haskell types to PureScript types via JSON
-- 
-- Pure functions for converting between Haskell and PureScript types.
-- All conversions use JSON serialization for type safety.
--
--                                                                  // critical
-- round-trip theorems. No proof, no conversion.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.HaskellToPureScript where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , encode
  , decode
  )
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // conversion // protocol
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert Haskell type to PureScript type via JSON
-- 
-- Pure function: no IO, no side effects
-- Returns: Either error message or converted value
hsToPs :: (ToJSON a, FromJSON b) => a -> Either String b
hsToPs hsValue = 
  case decode (encode hsValue) of
    Just psValue -> Right psValue
    Nothing -> Left "Failed to convert Haskell to PureScript: JSON decode failed"

-- | Convert PureScript type to Haskell type via JSON
-- 
-- Pure function: no IO, no side effects
-- Returns: Either error message or converted value
psToHs :: (ToJSON a, FromJSON b) => a -> Either String b
psToHs psValue = 
  case decode (encode psValue) of
    Just hsValue -> Right hsValue
    Nothing -> Left "Failed to convert PureScript to Haskell: JSON decode failed"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                      // type
-- ════════════════════════════════════════════════════════════════════════════

--                                                                      // note
-- instances. For now, this module provides the generic conversion protocol.
--
-- Example generated converters:
--
-- hsToPsPoint3 :: Point3 -> Either String PureScript.Point3
-- hsToPsPoint3 = hsToPs
--
-- psToHsPoint3 :: PureScript.Point3 -> Either String Point3
-- psToHsPoint3 = psToHs
