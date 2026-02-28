-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // attestation // signed-data
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SignedData — Pure data structure for signed payloads.
-- |
-- | ## Design Philosophy
-- |
-- | SignedData is a molecule that wraps any serializable content with:
-- | - Content hash (SHA-256 of the payload)
-- | - Signer identifier (who signed)
-- | - Signature bytes (the cryptographic signature)
-- | - Timestamp (when it was signed)
-- |
-- | This module does NOT perform actual cryptographic signing — that happens
-- | at the runtime boundary. This module defines the pure data structure
-- | that represents signed data.
-- |
-- | ## Why SignedData?
-- |
-- | At billion-agent scale, agents need:
-- | - Verifiable authorship of data
-- | - Non-repudiation (signer can't deny signing)
-- | - Foundation for x402 payments and EIP-712 signatures
-- | - Pure representation without FFI
-- |
-- | ## Signature Schemes (represented, not implemented)
-- |
-- | The signature bytes can represent:
-- | - ECDSA (secp256k1 for Ethereum, secp256r1 for WebAuthn)
-- | - EdDSA (Ed25519)
-- | - RSA-PSS
-- | - HMAC (symmetric, for trusted contexts)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Attestation.SHA256 (content hashing)
-- | - Hydrogen.Schema.Attestation.Timestamp
-- |
-- | ## Dependents
-- |
-- | - x402 payment flows
-- | - EIP-712 typed data signing
-- | - Document attestation

module Hydrogen.Schema.Attestation.SignedData
  ( -- * SignedData Type
    SignedData
  , SignatureScheme(..)
  , SignerId
  
  -- * Construction
  , signedData
  , signedDataFromBytes
  
  -- * Accessors
  , getContentHash
  , getContentHashHex
  , getSigner
  , getSignature
  , getTimestamp
  , getScheme
  
  -- * Verification Helpers
  , signatureMessage
  , signatureMessageHex
  , contentMatches
  , contentMatchesBytes
  
  -- * SignerId Operations
  , signerId
  , signerIdHex
  , signerIdFromBytes
  , signerIdBytes
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  )

import Data.Array (foldl, snoc) as Array
import Data.String.CodeUnits (toCharArray) as String
import Data.Char (toCharCode)

import Hydrogen.Schema.Attestation.SHA256 
  ( SHA256Hash
  , sha256Bytes
  , sha256
  , toHex
  , toBytes
  )
import Hydrogen.Schema.Attestation.Timestamp (Timestamp)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // signature schemes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Supported signature schemes.
-- |
-- | This enumerates the algorithms that can produce the signature bytes.
-- | The actual implementation lives at the runtime boundary.
data SignatureScheme
  = ECDSA_secp256k1   -- ^ Ethereum-style signatures
  | ECDSA_secp256r1   -- ^ WebAuthn/FIDO2, Apple/Google
  | Ed25519           -- ^ Modern EdDSA, used by Solana
  | RSA_PSS           -- ^ RSA with probabilistic padding
  | HMAC_SHA256       -- ^ Symmetric (trusted contexts only)
  | Unknown           -- ^ For future schemes

derive instance eqSignatureScheme :: Eq SignatureScheme
derive instance ordSignatureScheme :: Ord SignatureScheme

instance showSignatureScheme :: Show SignatureScheme where
  show ECDSA_secp256k1 = "ECDSA_secp256k1"
  show ECDSA_secp256r1 = "ECDSA_secp256r1"
  show Ed25519 = "Ed25519"
  show RSA_PSS = "RSA_PSS"
  show HMAC_SHA256 = "HMAC_SHA256"
  show Unknown = "Unknown"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // signer id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identifier for the signer.
-- |
-- | This is typically:
-- | - An Ethereum address (20 bytes)
-- | - A public key hash
-- | - A DID (stored as hash of DID string)
-- | - Any unique identifier for the signing entity
newtype SignerId = SignerId SHA256Hash

derive instance eqSignerId :: Eq SignerId
derive instance ordSignerId :: Ord SignerId

instance showSignerId :: Show SignerId where
  show (SignerId h) = "(SignerId " <> toHex h <> ")"

-- | Create a signer ID from a string identifier.
signerId :: String -> SignerId
signerId s = SignerId (sha256 s)

-- | Get signer ID as hex string.
signerIdHex :: SignerId -> String
signerIdHex (SignerId h) = toHex h

-- | Create signer ID from raw bytes (e.g., public key).
signerIdFromBytes :: Array Int -> SignerId
signerIdFromBytes bytes = SignerId (sha256Bytes bytes)

-- | Get signer ID as bytes.
signerIdBytes :: SignerId -> Array Int
signerIdBytes (SignerId h) = toBytes h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // signed data type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signed data molecule.
-- |
-- | Wraps content with cryptographic signature metadata.
-- | The actual signature verification happens at runtime.
type SignedData =
  { contentHash :: SHA256Hash      -- ^ Hash of the signed content
  , signer :: SignerId             -- ^ Who signed it
  , signature :: Array Int         -- ^ The signature bytes
  , timestamp :: Timestamp         -- ^ When it was signed
  , scheme :: SignatureScheme      -- ^ Which algorithm was used
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create signed data from string content.
-- |
-- | Note: This creates the data structure; actual signing happens at runtime.
signedData 
  :: String 
  -> SignerId 
  -> Array Int 
  -> Timestamp 
  -> SignatureScheme 
  -> SignedData
signedData content signer sig ts scheme =
  let
    chars = String.toCharArray content
    bytes = Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars
  in
    signedDataFromBytes bytes signer sig ts scheme

-- | Create signed data from byte content.
signedDataFromBytes 
  :: Array Int 
  -> SignerId 
  -> Array Int 
  -> Timestamp 
  -> SignatureScheme 
  -> SignedData
signedDataFromBytes contentBytes signer sig ts scheme =
  { contentHash: sha256Bytes contentBytes
  , signer: signer
  , signature: sig
  , timestamp: ts
  , scheme: scheme
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the content hash.
getContentHash :: SignedData -> SHA256Hash
getContentHash sd = sd.contentHash

-- | Get the content hash as hex string.
getContentHashHex :: SignedData -> String
getContentHashHex sd = toHex sd.contentHash

-- | Get the signer identifier.
getSigner :: SignedData -> SignerId
getSigner sd = sd.signer

-- | Get the signature bytes.
getSignature :: SignedData -> Array Int
getSignature sd = sd.signature

-- | Get the timestamp.
getTimestamp :: SignedData -> Timestamp
getTimestamp sd = sd.timestamp

-- | Get the signature scheme.
getScheme :: SignedData -> SignatureScheme
getScheme sd = sd.scheme

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // verification helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the message that was signed.
-- |
-- | This is typically the content hash, which is what gets signed.
-- | Returns the hash bytes for use in verification.
signatureMessage :: SignedData -> Array Int
signatureMessage sd = toBytes sd.contentHash

-- | Get the signature message as hex string.
signatureMessageHex :: SignedData -> String
signatureMessageHex sd = toHex sd.contentHash

-- | Check if content matches the stored hash.
-- |
-- | This verifies content integrity (but not the signature).
contentMatches :: SignedData -> String -> Boolean
contentMatches sd content =
  let
    chars = String.toCharArray content
    bytes = Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars
  in
    contentMatchesBytes sd bytes

-- | Check if byte content matches the stored hash.
contentMatchesBytes :: SignedData -> Array Int -> Boolean
contentMatchesBytes sd bytes =
  let computed = sha256Bytes bytes
  in toHex computed == toHex sd.contentHash
