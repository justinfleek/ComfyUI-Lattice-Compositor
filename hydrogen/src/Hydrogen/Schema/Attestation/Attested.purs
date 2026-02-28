-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // attestation // attested
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Attested — A wrapper that pairs any content with its attestation.
-- |
-- | This is the primary composition mechanism for the Attestation pillar.
-- | Any serializable content can be wrapped in Attested to gain:
-- | - Deterministic UUID identity
-- | - Timestamp proof
-- | - Content hash for integrity verification
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Attest an event
-- | attestedEvent :: Attested Event
-- | attestedEvent = attest myEvent currentTimestamp serialize
-- |
-- | -- Verify the event hasn't been tampered with
-- | isValid = verifyAttested attestedEvent serialize
-- | ```
-- |
-- | ## Type Parameters
-- |
-- | The `a` type parameter represents the content being attested.
-- | The content must be serializable to bytes for hashing.

module Hydrogen.Schema.Attestation.Attested
  ( Attested
  , attest
  , attestWithSerializer
  , getContent
  , getAttestation
  , verifyAttested
  , mapContent
  ) where

import Data.Array (foldl, snoc) as Array
import Data.String.CodeUnits (toCharArray) as String
import Data.Char (toCharCode)

import Hydrogen.Schema.Attestation.Timestamp (Timestamp)
import Hydrogen.Schema.Attestation.Attestation 
  ( Attestation
  , attestationFromBytes
  , verifyBytes
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // attested
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content paired with its attestation.
-- |
-- | The attestation proves that the content existed at a specific time
-- | and provides a deterministic identifier derived from the content.
type Attested a =
  { content :: a
  , attestation :: Attestation
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Attest content using a string serializer.
-- |
-- | This is the simplest API when your content can be converted to a string.
-- | The string is then hashed to create the attestation.
attest :: forall a. a -> Timestamp -> (a -> String) -> Attested a
attest content ts serialize =
  let
    serialized = serialize content
    chars = String.toCharArray serialized
    bytes = Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars
    att = attestationFromBytes bytes ts
  in
    { content: content
    , attestation: att
    }

-- | Attest content using a byte serializer.
-- |
-- | Use this when you need precise control over serialization,
-- | such as for binary protocols or specific encoding requirements.
attestWithSerializer :: forall a. a -> Timestamp -> (a -> Array Int) -> Attested a
attestWithSerializer content ts serialize =
  let
    bytes = serialize content
    att = attestationFromBytes bytes ts
  in
    { content: content
    , attestation: att
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the content from an Attested wrapper.
getContent :: forall a. Attested a -> a
getContent att = att.content

-- | Extract the attestation from an Attested wrapper.
getAttestation :: forall a. Attested a -> Attestation
getAttestation att = att.attestation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // verification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Verify that the content matches the attestation.
-- |
-- | This re-serializes the content and checks that the hash matches.
-- | Returns true if the content has not been modified.
-- |
-- | The serializer must produce the same bytes as when the attestation
-- | was created. Using a different serializer will cause verification
-- | to fail even for unchanged content.
verifyAttested :: forall a. Attested a -> (a -> Array Int) -> Boolean
verifyAttested attested serialize =
  let
    bytes = serialize attested.content
  in
    verifyBytes attested.attestation bytes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // transformation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a function over attested content.
-- |
-- | WARNING: This changes the content without updating the attestation!
-- | The resulting Attested value will fail verification.
-- |
-- | This is useful only for:
-- | 1. Read-only transformations where you don't need to verify
-- | 2. Temporary projections for display purposes
-- |
-- | For modifications that need to maintain validity, create a new
-- | attestation with `attest` or `attestWithSerializer`.
mapContent :: forall a b. (a -> b) -> Attested a -> Attested b
mapContent f attested =
  { content: f attested.content
  , attestation: attested.attestation
  }
