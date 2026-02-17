-- |
-- Module      : Lattice.FFI.PureScriptToTypeScript
-- Description : Convert PureScript types to TypeScript types via JSON
-- 
-- Pure functions for converting between PureScript and TypeScript types.
-- All conversions use JSON serialization for type safety.
--
-- CRITICAL: All types must have Extractable instances in Lean4 with proven
-- round-trip theorems. No proof, no conversion.
--

module Lattice.FFI.PureScriptToTypeScript where

import Prelude
import Data.Argonaut
  ( class EncodeJson
  , class DecodeJson
  , encodeJson
  , decodeJson
  , jsonParser
  )
import Data.Either (Either(..))
import Data.String (String)

-- ============================================================================
-- CONVERSION PROTOCOL
-- ============================================================================

-- | Convert PureScript type to TypeScript type via JSON string
-- 
-- Pure function: no Effect, no side effects
-- Returns: JSON string that TypeScript can parse
psToTs :: forall a. EncodeJson a => a -> String
psToTs psValue = stringify (encodeJson psValue)

-- | Convert TypeScript type to PureScript type via JSON string
-- 
-- Pure function: no Effect, no side effects
-- Returns: Either error message or converted value
tsToPs :: forall a. DecodeJson a => String -> Either String a
tsToPs jsonStr = 
  case jsonParser jsonStr >>= decodeJson of
    Right psValue -> Right psValue
    Left err -> Left $ "Failed to convert TypeScript to PureScript: " <> err

-- ============================================================================
-- JSON STRING HELPERS
-- ============================================================================

-- | Stringify JSON value to string
-- 
-- This is a placeholder - actual implementation depends on Argonaut API
foreign import stringify :: forall a. a -> String

-- ============================================================================
-- TYPE-SPECIFIC CONVERTERS
-- ============================================================================

-- NOTE: Type-specific converters will be generated from Lean4 Extractable
-- instances. For now, this module provides the generic conversion protocol.
--
-- Example generated converters:
--
-- psToTsPoint3 :: Point3 -> String
-- psToTsPoint3 = psToTs
--
-- tsToPsPoint3 :: String -> Either String Point3
-- tsToPsPoint3 = tsToPs
