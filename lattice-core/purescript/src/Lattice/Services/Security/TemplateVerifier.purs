-- | Lattice.Services.Security.TemplateVerifier - Template signature verification
-- |
-- | Verifies Ed25519 signatures on .lattice.json template files.
-- | Official templates are signed by Lattice's private key.
-- |
-- | SECURITY:
-- | - Only OFFICIAL_PUBLIC_KEY should sign official templates
-- | - Unsigned templates show warning to user
-- | - Signature covers: templateConfig, layers, compositions (not metadata like name)
-- | - Third-party templates are allowed but marked as unverified
-- |
-- | NOTE: Cryptographic operations are delegated to the Haskell backend via Bridge.
-- | This module provides pure types and request/response structures.
-- |
-- | Source: ui/src/services/security/templateVerifier.ts

module Lattice.Services.Security.TemplateVerifier
  ( -- * Types
    TemplateSignature
  , VerificationResult
  , VerificationStatus(..)
  , VerificationBadge
  , BadgeColor(..)
  , TemplateDataForSigning
  , SignedTemplate
    -- * Verification Requests
  , VerifySignatureRequest(..)
  , SignTemplateRequest(..)
    -- * Pure Verification Functions
  , mkUnsignedResult
  , mkInvalidResult
  , mkOfficialResult
  , mkThirdPartyResult
  , isOfficialKey
  , getVerificationBadge
    -- * Loading
  , shouldWarnBeforeLoading
  , getLoadingWarning
  , parseSignature
  , createCanonicalJson
    -- * Constants
  , officialPublicKey
  , supportedVersions
  ) where

import Prelude
import Data.Argonaut.Core (Json, stringify, toObject, toString)
import Data.Array (elem, sort)
import Data.Foldable as Data.Foldable
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Foreign.Object (Object)
import Foreign.Object as Obj
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- | Signature structure in template files
type TemplateSignature =
  { algorithm :: String       -- Always "Ed25519"
  , publicKey :: String       -- Base64-encoded public key
  , signature :: String       -- Base64-encoded signature
  , signedAt :: String        -- ISO timestamp
  , version :: String         -- Signature format version
  }

-- | Verification status enum
data VerificationStatus
  = VsOfficial            -- Signed by official Lattice key
  | VsThirdPartyValid     -- Valid third-party signature
  | VsThirdPartyInvalid   -- Invalid signature
  | VsUnsigned            -- No signature present

derive instance Eq VerificationStatus
derive instance Generic VerificationStatus _
instance Show VerificationStatus where show = genericShow

-- | Verification result
type VerificationResult =
  { isSigned :: Boolean
  , isValid :: Boolean
  , isOfficial :: Boolean
  , status :: VerificationStatus
  , message :: String
  , signerPublicKey :: Maybe String
  , signedAt :: Maybe String
  }

-- | Badge color for UI display
data BadgeColor = ColorGreen | ColorYellow | ColorRed | ColorGray

derive instance Eq BadgeColor
derive instance Generic BadgeColor _
instance Show BadgeColor where show = genericShow

-- | Verification badge for UI
type VerificationBadge =
  { label :: String
  , color :: BadgeColor
  , icon :: String
  }

-- | Template data for signing (excludes _signature)
type TemplateDataForSigning = Object Json

-- | Signed template structure
type SignedTemplate =
  { dat :: TemplateDataForSigning   -- Template data
  , signature :: Maybe TemplateSignature
  }

-- | Request to verify an Ed25519 signature
-- |
-- | Send this to the Haskell backend via Bridge.
-- | Backend returns Boolean indicating if signature is valid.
data VerifySignatureRequest = VerifySignatureRequest
  { message :: String      -- Canonical JSON to verify
  , signature :: String    -- Base64-encoded signature
  , publicKey :: String    -- Base64-encoded public key
  }

derive instance Eq VerifySignatureRequest
derive instance Generic VerifySignatureRequest _
instance Show VerifySignatureRequest where show = genericShow

-- | Request to sign template data
-- |
-- | Send this to the Haskell backend via Bridge (build-time only).
-- | Backend returns the signature string.
data SignTemplateRequest = SignTemplateRequest
  { canonicalJson :: String    -- Canonical JSON to sign
  , privateKey :: String       -- Base64-encoded private key
  }

derive instance Eq SignTemplateRequest
derive instance Generic SignTemplateRequest _
instance Show SignTemplateRequest where show = genericShow

-- | Official Lattice public key for template signing
-- |
-- | SECURITY: This key should ONLY exist in this file.
-- | The corresponding private key is kept offline and never committed.
officialPublicKey :: String
officialPublicKey = "xmCWXfRKw7DQLuyQdqQIJlAb+r0arpUu2oVjTdJgv/k="

-- | Supported signature versions
supportedVersions :: Array String
supportedVersions = ["1.0"]

-- | Check if a public key is the official Lattice key
isOfficialKey :: String -> Boolean
isOfficialKey key = key == officialPublicKey

-- | Create unsigned result
mkUnsignedResult :: String -> VerificationResult
mkUnsignedResult message =
  { isSigned: false
  , isValid: false
  , isOfficial: false
  , status: VsUnsigned
  , message
  , signerPublicKey: Nothing
  , signedAt: Nothing
  }

-- | Create invalid result
mkInvalidResult :: String -> Maybe String -> Maybe String -> VerificationResult
mkInvalidResult message signerKey signedTime =
  { isSigned: true
  , isValid: false
  , isOfficial: false
  , status: VsThirdPartyInvalid
  , message
  , signerPublicKey: signerKey
  , signedAt: signedTime
  }

-- | Create official verification result
mkOfficialResult :: String -> String -> VerificationResult
mkOfficialResult publicKey signedAt =
  { isSigned: true
  , isValid: true
  , isOfficial: true
  , status: VsOfficial
  , message: "Verified official Lattice template."
  , signerPublicKey: Just publicKey
  , signedAt: Just signedAt
  }

-- | Create third-party valid result
mkThirdPartyResult :: String -> String -> VerificationResult
mkThirdPartyResult publicKey signedAt =
  { isSigned: true
  , isValid: true
  , isOfficial: false
  , status: VsThirdPartyValid
  , message: "Template is signed by a third party. Verify you trust the source."
  , signerPublicKey: Just publicKey
  , signedAt: Just signedAt
  }

-- | Get verification badge for UI display
getVerificationBadge :: VerificationResult -> VerificationBadge
getVerificationBadge result = case result.status of
  VsOfficial ->
    { label: "Verified by Lattice"
    , color: ColorGreen
    , icon: "check"
    }
  VsThirdPartyValid ->
    { label: "Third-party (valid signature)"
    , color: ColorYellow
    , icon: "warning"
    }
  VsThirdPartyInvalid ->
    { label: "Invalid signature"
    , color: ColorRed
    , icon: "x"
    }
  VsUnsigned ->
    { label: "Unsigned template"
    , color: ColorGray
    , icon: "question"
    }

-- | Check if a template should show a warning before loading
shouldWarnBeforeLoading :: VerificationResult -> Boolean
shouldWarnBeforeLoading result = result.status /= VsOfficial

-- | Get warning message for non-official templates
getLoadingWarning :: VerificationResult -> Either String String
getLoadingWarning result = case result.status of
  VsOfficial ->
    Left "No loading warning for official templates"
  VsThirdPartyValid ->
    Right "This template is signed by a third party. Only load templates from sources you trust."
  VsThirdPartyInvalid ->
    Right "WARNING: This template has an invalid signature. It may have been tampered with. Do not load unless you trust the source."
  VsUnsigned ->
    Right "This template is unsigned. Only load templates from sources you trust."

-- | Parse signature from JSON
parseSignature :: Json -> Maybe TemplateSignature
parseSignature json = do
  obj <- toObject json
  algorithm <- Obj.lookup "algorithm" obj >>= toString
  publicKey <- Obj.lookup "publicKey" obj >>= toString
  signature <- Obj.lookup "signature" obj >>= toString
  signedAt <- Obj.lookup "signedAt" obj >>= toString
  version <- Obj.lookup "version" obj >>= toString

  -- Validate algorithm
  if algorithm /= "Ed25519"
    then Nothing
    else Just { algorithm, publicKey, signature, signedAt, version }

-- | Create canonical JSON (sorted keys for deterministic output)
createCanonicalJson :: TemplateDataForSigning -> String
createCanonicalJson obj =
  let sortedKeys = sort (Obj.keys obj)
      pairs = map (\k -> "\"" <> k <> "\":" <>
        case Obj.lookup k obj of
          Just v -> stringify v
          Nothing -> "null"
      ) sortedKeys
      content = joinWith "," pairs
  in "{" <> content <> "}"

-- | Join array with separator
joinWith :: String -> Array String -> String
joinWith sep arr = case arr of
  [] -> ""
  [x] -> x
  _ -> Data.Foldable.foldl (\acc x -> if acc == "" then x else acc <> sep <> x) "" arr
