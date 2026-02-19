-- | Lattice.Utils.Uuid5.Core - UUID5 generation
-- |
-- | @module Lattice.Utils.Uuid5.Core
-- | @description UUID5 generation using SHA-1 hashing.
-- |
-- | RFC 4122 compliant UUID5 implementation.
-- |
-- | Source: lattice-core/lean/Lattice/Utils/Uuid5.lean

module Lattice.Utils.Uuid5.Core
  ( -- * Namespaces
    uUID5_NAMESPACE_DNS
  , uUID5_NAMESPACE_URL
  , uUID5_NAMESPACE_OID
  , uUID5_NAMESPACE_X500
  , lATTICE_NAMESPACE
    -- * UUID5 Generation
  , uuid5
  , uuid5Default
  , generateId
    -- * UUID Parsing
  , uuidToBytes
  , bytesToUuid
  ) where

import Prelude
import Data.Array as Array
import Data.Int (hexadecimal, toStringAs)
import Data.Int.Bits (and, or)
import Data.Maybe (fromMaybe)
import Data.String as String
import Data.Char (toCharCode)
import Data.String.CodeUnits as CodeUnits

import Lattice.Utils.Uuid5.SHA1 (sha1, ByteArray)
import Lattice.Utils.Uuid5.EntityType (EntityType, entityTypeToPrefix)

-- ────────────────────────────────────────────────────────────────────────────
-- Namespaces
-- ────────────────────────────────────────────────────────────────────────────

-- | Standard UUID5 namespaces (RFC 4122)
uUID5_NAMESPACE_DNS :: String
uUID5_NAMESPACE_DNS = "6ba7b810-9dad-11d1-80b4-00c04fd430c8"

uUID5_NAMESPACE_URL :: String
uUID5_NAMESPACE_URL = "6ba7b811-9dad-11d1-80b4-00c04fd430c8"

uUID5_NAMESPACE_OID :: String
uUID5_NAMESPACE_OID = "6ba7b812-9dad-11d1-80b4-00c04fd430c8"

uUID5_NAMESPACE_X500 :: String
uUID5_NAMESPACE_X500 = "6ba7b814-9dad-11d1-80b4-00c04fd430c8"

-- | Lattice-specific namespace for layer/keyframe IDs
lATTICE_NAMESPACE :: String
lATTICE_NAMESPACE = "a1b2c3d4-e5f6-4789-a012-3456789abcde"

-- ────────────────────────────────────────────────────────────────────────────
--                                                                 // uuid // p
-- ────────────────────────────────────────────────────────────────────────────

-- | Parse a hex character
hexCharToInt :: Char -> Int
hexCharToInt c
  | c >= '0' && c <= '9' = toCharCode c - toCharCode '0'
  | c >= 'a' && c <= 'f' = toCharCode c - toCharCode 'a' + 10
  | c >= 'A' && c <= 'F' = toCharCode c - toCharCode 'A' + 10
  | otherwise = 0

-- | Parse UUID string to bytes
-- |
-- | @param uuid UUID string (with or without dashes)
-- | @returns 16-byte array
uuidToBytes :: String -> ByteArray
uuidToBytes uuid =
  let hex = String.replaceAll (String.Pattern "-") (String.Replacement "") uuid
      chars = CodeUnits.toCharArray hex
      pairs = Array.range 0 15
      toByte i =
        let c1 = fromMaybe '0' (Array.index chars (i * 2))
            c2 = fromMaybe '0' (Array.index chars (i * 2 + 1))
        in hexCharToInt c1 * 16 + hexCharToInt c2
  in map toByte pairs

-- | Convert a byte to 2-char hex string
byteToHex :: Int -> String
byteToHex b =
  let hex = toStringAs hexadecimal b
  in if String.length hex == 1 then "0" <> hex else hex

-- | Convert bytes to UUID string
-- |
-- | @param bytes 16-byte array
-- | @returns UUID string with dashes
bytesToUuid :: ByteArray -> String
bytesToUuid bytes =
  let hex = String.joinWith "" (map byteToHex bytes)
  in String.take 8 hex <> "-" <>
     String.take 4 (String.drop 8 hex) <> "-" <>
     String.take 4 (String.drop 12 hex) <> "-" <>
     String.take 4 (String.drop 16 hex) <> "-" <>
     String.drop 20 hex

-- ────────────────────────────────────────────────────────────────────────────
-- String to Bytes
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert string to UTF-8 bytes (simplified ASCII)
stringToBytes :: String -> ByteArray
stringToBytes s = map toCharCode (CodeUnits.toCharArray s)

-- | Get byte from array with default 0
getByte :: ByteArray -> Int -> Int
getByte arr idx = fromMaybe 0 (Array.index arr idx)

-- ────────────────────────────────────────────────────────────────────────────
--                                                                // uuid5 // g
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate UUID5 (deterministic name-based UUID)
-- |
-- | @param name Name to hash
-- | @param namespace Namespace UUID string
-- | @returns UUID5 string
-- |
-- | @example
-- | ```purescript
-- | let id = uuid5 "layer:main:0" lATTICE_NAMESPACE
-- | -- Always produces the same UUID for the same inputs
-- | ```
uuid5 :: String -> String -> String
uuid5 name namespace =
  let namespaceBytes = uuidToBytes namespace
      nameBytes = stringToBytes name
      combined = namespaceBytes <> nameBytes
      hash = sha1 combined
      -- Take first 16 bytes
      uuidBytes = Array.take 16 hash
      -- Set version (5) and variant bits
      byte6 = ((getByte uuidBytes 6) `and` 0x0F) `or` 0x50
      byte8 = ((getByte uuidBytes 8) `and` 0x3F) `or` 0x80
      uuidBytes' = Array.take 6 uuidBytes <>
                   [byte6] <>
                   [getByte uuidBytes 7] <>
                   [byte8] <>
                   Array.drop 9 uuidBytes
  in bytesToUuid uuidBytes'

-- | Generate UUID5 with default Lattice namespace
-- |
-- | @param name Name to hash
-- | @returns UUID5 string using Lattice namespace
uuid5Default :: String -> String
uuid5Default name = uuid5 name lATTICE_NAMESPACE

-- | Generate a typed ID for an entity
-- |
-- | @param entityType Type of entity
-- | @param parts Additional identifying parts
-- | @returns Deterministic UUID5 for this entity
-- |
-- | @example
-- | ```purescript
-- | let layerId = generateId EntityLayer ["main", "0"]
-- | -- Produces: uuid5 "layer:main:0" lATTICE_NAMESPACE
-- | ```
generateId :: EntityType -> Array String -> String
generateId entityType parts =
  let name = String.joinWith ":" ([entityTypeToPrefix entityType] <> parts)
  in uuid5 name lATTICE_NAMESPACE
