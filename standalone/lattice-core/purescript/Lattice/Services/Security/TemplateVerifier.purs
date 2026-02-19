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
    -- * Verification
  , verifyTemplate
  , isOfficialTemplate
  , getVerificationBadge
    -- * Signing (build-time only)
  , signTemplate
    -- * Loading
  , loadAndVerifyTemplate
  , shouldWarnBeforeLoading
  , getLoadingWarning
    -- * Constants
  , officialPublicKey
  , supportedVersions
  ) where

import Prelude
import Effect.Aff (Aff, attempt, throwError)
import Effect.Exception (Error, error)
import Data.Argonaut.Core (Json, stringify, toObject, toString)
import Data.Argonaut.Parser (jsonParser)
import Data.Array (elem, sort)
import Data.Foldable as Data.Foldable
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), contains)
import Data.Tuple (Tuple(..))
import Foreign.Object (Object)
import Foreign.Object as Obj
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

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

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Official Lattice public key for template signing
-- |
-- | SECURITY: This key should ONLY exist in this file.
-- | The corresponding private key is kept offline and never committed.
officialPublicKey :: String
officialPublicKey = "xmCWXfRKw7DQLuyQdqQIJlAb+r0arpUu2oVjTdJgv/k="

-- | Supported signature versions
supportedVersions :: Array String
supportedVersions = ["1.0"]

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // ffi
-- ────────────────────────────────────────────────────────────────────────────

-- | Verify Ed25519 signature (async FFI)
foreign import verifyEd25519Signature :: String -> String -> String -> Aff Boolean

-- | Sign with Ed25519 private key (async FFI)
foreign import signEd25519 :: String -> String -> Aff String

-- | Get current ISO timestamp
foreign import getCurrentISOTimestamp :: Aff String

-- | Extract public key from private key (last 32 bytes)
foreign import extractPublicKeyFromPrivate :: String -> String

-- ────────────────────────────────────────────────────────────────────────────
-- Verification Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Verify a template file
verifyTemplate :: Json -> Aff VerificationResult
verifyTemplate templateJson = do
  case toObject templateJson of
    Nothing ->
      pure (mkUnsignedResult "Invalid template format")

    Just templateObj -> do
      -- Check for _signature field
      case Obj.lookup "_signature" templateObj of
        Nothing ->
          pure (mkUnsignedResult "Template is not signed. Exercise caution with untrusted templates.")

        Just sigJson -> do
          case parseSignature sigJson of
            Nothing ->
              pure (mkInvalidResult "Template has invalid signature format." Nothing Nothing)

            Just sig -> do
              -- Check version
              if not (sig.version `elem` supportedVersions)
                then pure (mkInvalidResult ("Unsupported signature version: " <> sig.version) (Just sig.publicKey) (Just sig.signedAt))
                else do
                  -- Extract template data (without _signature)
                  let templateData = Obj.delete "_signature" templateObj

                  -- Verify signature
                  verifyResult <- attempt (verifySignatureInternal templateData sig)
                  case verifyResult of
                    Left err ->
                      pure (mkInvalidResult ("Signature verification failed: " <> show err) (Just sig.publicKey) (Just sig.signedAt))

                    Right isValid ->
                      if not isValid
                        then pure (mkInvalidResult "Template signature is invalid. The template may have been tampered with." (Just sig.publicKey) (Just sig.signedAt))
                        else do
                          -- Check if official key
                          let isOfficial = sig.publicKey == officialPublicKey
                          if isOfficial
                            then pure
                              { isSigned: true
                              , isValid: true
                              , isOfficial: true
                              , status: VsOfficial
                              , message: "Verified official Lattice template."
                              , signerPublicKey: Just sig.publicKey
                              , signedAt: Just sig.signedAt
                              }
                            else pure
                              { isSigned: true
                              , isValid: true
                              , isOfficial: false
                              , status: VsThirdPartyValid
                              , message: "Template is signed by a third party. Verify you trust the source."
                              , signerPublicKey: Just sig.publicKey
                              , signedAt: Just sig.signedAt
                              }

-- | Quick check if template is officially signed
isOfficialTemplate :: Json -> Aff Boolean
isOfficialTemplate template = do
  result <- verifyTemplate template
  pure result.isOfficial

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

-- ────────────────────────────────────────────────────────────────────────────
-- Signing Functions (build-time only)
-- ────────────────────────────────────────────────────────────────────────────

-- | Sign a template with a private key
-- |
-- | SECURITY: This should only be used in build scripts, not at runtime.
-- | The private key should never be in the browser.
signTemplate :: TemplateDataForSigning -> String -> Aff SignedTemplate
signTemplate templateData privateKeyBase64 = do
  -- Create canonical JSON
  let canonical = createCanonicalJson templateData

  -- Sign the data
  signatureBase64 <- signEd25519 canonical privateKeyBase64

  -- Extract public key from private key
  let publicKeyBase64 = extractPublicKeyFromPrivate privateKeyBase64

  -- Get timestamp
  timestamp <- getCurrentISOTimestamp

  let sig =
        { algorithm: "Ed25519"
        , publicKey: publicKeyBase64
        , signature: signatureBase64
        , signedAt: timestamp
        , version: "1.0"
        }

  pure { dat: templateData, signature: Just sig }

-- ────────────────────────────────────────────────────────────────────────────
-- Loading Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Load and verify a template from JSON string
loadAndVerifyTemplate :: String -> Aff { template :: TemplateDataForSigning, verification :: VerificationResult }
loadAndVerifyTemplate jsonStr = do
  case jsonParser jsonStr of
    Left parseErr ->
      pure
        { template: Obj.empty
        , verification: mkUnsignedResult ("Failed to parse template: " <> parseErr)
        }
    Right parsed -> do
      verification <- verifyTemplate parsed
      case toObject parsed of
        Nothing ->
          pure { template: Obj.empty, verification }
        Just obj ->
          -- Remove signature from returned data
          pure { template: Obj.delete "_signature" obj, verification }

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

-- ────────────────────────────────────────────────────────────────────────────
-- Internal Functions
-- ────────────────────────────────────────────────────────────────────────────

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

-- | Verify signature internally
verifySignatureInternal :: TemplateDataForSigning -> TemplateSignature -> Aff Boolean
verifySignatureInternal templateData sig = do
  let canonical = createCanonicalJson templateData
  verifyEd25519Signature canonical sig.signature sig.publicKey

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
