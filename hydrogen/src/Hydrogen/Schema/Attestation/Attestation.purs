-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // attestation // attestation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Attestation — Cryptographic proof of content at a point in time.
-- |
-- | An Attestation is a composition of:
-- | - UUID5: Deterministic identifier derived from content
-- | - Timestamp: When the attestation was created
-- | - ContentHash: SHA-256 hash of the attested content
-- |
-- | This is the core primitive for the Attestation pillar. It composes with
-- | any serializable content to provide cryptographic verification.
-- |
-- | ## Why Attestation?
-- |
-- | At billion-agent scale, agents need:
-- | - Proof that content existed at a specific time
-- | - Deterministic identity for deduplication
-- | - Tamper detection via content hashing
-- | - Foundation for digital signatures (x402, EIP-712)
-- |
-- | ## Design Principles
-- |
-- | 1. **Composable**: Attestation is a separate type that wraps content
-- | 2. **Deterministic**: Same content + timestamp = same attestation
-- | 3. **Verifiable**: Anyone can recompute the hash and check
-- | 4. **Pure**: No side effects, no FFI

module Hydrogen.Schema.Attestation.Attestation
  ( Attestation
  , ContentHash
  , attestation
  , attestationFromBytes
  , verify
  , verifyBytes
  , getId
  , getTimestamp
  , getContentHash
  , getContentHashHex
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (-)
  , (*)
  , (/)
  , (==)
  )

import Data.Array (foldl, snoc) as Array
import Data.Int (floor) as Int
import Data.Int.Bits (shr, and) as Bits
import Data.Number (floor) as Number
import Data.String.CodeUnits (toCharArray) as String
import Data.Char (toCharCode)

import Hydrogen.Schema.Attestation.Timestamp (Timestamp)
import Hydrogen.Schema.Attestation.Timestamp (toNumber) as Timestamp
import Hydrogen.Schema.Attestation.UUID5 (UUID5, uuid5Bytes, nsAttestation)
import Hydrogen.Schema.Attestation.SHA256 (SHA256Hash, sha256Bytes)
import Hydrogen.Schema.Attestation.SHA256 (toHex, toBytes) as SHA256

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // content hash
-- ═════════════════════════════════════════════════════════════════════════════

-- | SHA-256 hash of content being attested.
-- |
-- | This is the cryptographic commitment to the content.
-- | If the content changes, the hash changes.
newtype ContentHash = ContentHash SHA256Hash

derive instance eqContentHash :: Eq ContentHash
derive instance ordContentHash :: Ord ContentHash

instance showContentHash :: Show ContentHash where
  show (ContentHash hash) = SHA256.toHex hash

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // attestation
-- ═════════════════════════════════════════════════════════════════════════════

-- | An attestation binding content to a point in time.
-- |
-- | Components:
-- | - id: UUID5 derived from (namespace, contentHash || timestamp)
-- | - timestamp: When this attestation was created
-- | - contentHash: SHA-256 of the original content
type Attestation =
  { id :: UUID5
  , timestamp :: Timestamp
  , contentHash :: ContentHash
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an attestation for string content at a given timestamp.
-- |
-- | The content is hashed with SHA-256, and a deterministic UUID is
-- | generated from the hash combined with the timestamp.
attestation :: String -> Timestamp -> Attestation
attestation content ts =
  let
    chars = String.toCharArray content
    bytes = Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars
  in
    attestationFromBytes bytes ts

-- | Create an attestation for byte content at a given timestamp.
-- |
-- | This is the primary creation function when content is already
-- | serialized to bytes.
attestationFromBytes :: Array Int -> Timestamp -> Attestation
attestationFromBytes contentBytes ts =
  let
    -- Hash the content
    hash = sha256Bytes contentBytes
    hashBytes = SHA256.toBytes hash
    
    -- Generate UUID from hash + timestamp representation
    -- This makes the UUID deterministic for same content + time
    tsBytes = timestampToBytes ts
    combinedBytes = hashBytes <> tsBytes
    id = uuid5Bytes nsAttestation combinedBytes
  in
    { id: id
    , timestamp: ts
    , contentHash: ContentHash hash
    }

-- | Convert timestamp to bytes for hashing
-- |
-- | We use 8 bytes (64 bits) to represent milliseconds since epoch.
-- | Big-endian byte order for consistent hashing across platforms.
timestampToBytes :: Timestamp -> Array Int
timestampToBytes ts =
  let
    ms = Timestamp.toNumber ts
  in
    numberToBytes ms

-- | Convert Number (milliseconds) to 8 bytes (big-endian)
-- |
-- | For timestamps, we need to handle large numbers (up to 2^53).
-- | We split into high 32 bits and low 32 bits, then convert each to bytes.
numberToBytes :: Number -> Array Int
numberToBytes n =
  let
    -- Split into high and low 32-bit parts
    -- high = floor(n / 2^32)
    -- low = n mod 2^32
    divisor = 4294967296.0  -- 2^32
    highNum = Number.floor (n / divisor)
    lowNum = n - (highNum * divisor)
    
    -- Convert each 32-bit part to Int
    -- Data.Int.floor handles the Number -> Int conversion
    highInt = Int.floor highNum
    lowInt = Int.floor lowNum
  in
    int32ToBytes highInt <> int32ToBytes lowInt

-- | Convert 32-bit Int to 4 bytes (big-endian)
int32ToBytes :: Int -> Array Int
int32ToBytes n =
  [ Bits.and (Bits.shr n 24) 0xFF
  , Bits.and (Bits.shr n 16) 0xFF
  , Bits.and (Bits.shr n 8) 0xFF
  , Bits.and n 0xFF
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // verification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Verify that content matches the attestation's hash.
-- |
-- | Returns true if SHA-256(content) == attestation.contentHash
verify :: Attestation -> String -> Boolean
verify att content =
  let
    chars = String.toCharArray content
    bytes = Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars
  in
    verifyBytes att bytes

-- | Verify that byte content matches the attestation's hash.
verifyBytes :: Attestation -> Array Int -> Boolean
verifyBytes att contentBytes =
  let
    computedHash = sha256Bytes contentBytes
    ContentHash storedHash = att.contentHash
  in
    SHA256.toHex computedHash == SHA256.toHex storedHash

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the attestation's unique identifier
getId :: Attestation -> UUID5
getId att = att.id

-- | Get the attestation's timestamp
getTimestamp :: Attestation -> Timestamp
getTimestamp att = att.timestamp

-- | Get the attestation's content hash
getContentHash :: Attestation -> ContentHash
getContentHash att = att.contentHash

-- | Get the content hash as hex string
getContentHashHex :: Attestation -> String
getContentHashHex att = show att.contentHash
