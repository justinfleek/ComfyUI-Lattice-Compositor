-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // attestation // did
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | W3C Decentralized Identifiers (DID) specification.
-- |
-- | DIDs are a new type of identifier that enables verifiable,
-- | self-sovereign digital identity.
-- |
-- | Format: did:method:method-specific-id
-- | Example: did:key:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK

module Hydrogen.Schema.Attestation.DID
  ( -- * DID
    DID
  , did
  , didMethod
  , didIdentifier
  , didString
  , parseDID
  , sameDID
  , showDID
  
  -- * DID Methods
  , DIDMethod(..)
  , didMethodLabel
  
  -- * DID Document
  , DIDDocument
  , didDocument
  , didDocumentId
  , didDocumentController
  , didDocumentVerificationMethods
  , didDocumentAuthentication
  , didDocumentAssertionMethod
  , sameDocument
  , showDocument
  
  -- * Verification Method
  , VerificationMethod
  , verificationMethod
  , verificationMethodId
  , verificationMethodType
  , verificationMethodController
  , verificationMethodPublicKey
  , sameVerificationMethod
  , showVerificationMethod
  
  -- * Verification Method Type
  , VerificationMethodType(..)
  , verificationMethodTypeLabel
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (>=)
  , (<>)
  )

import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split, joinWith)
import Data.Array (length, (!!), drop)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // did method
-- ═════════════════════════════════════════════════════════════════════════════

-- | DIDMethod - supported DID methods.
data DIDMethod
  = MethodKey       -- ^ did:key - self-generated cryptographic keys
  | MethodWeb       -- ^ did:web - DNS-based resolution
  | MethodEthr      -- ^ did:ethr - Ethereum addresses
  | MethodIon       -- ^ did:ion - Bitcoin-anchored (Microsoft)
  | MethodPkh       -- ^ did:pkh - Public Key Hash
  | MethodOther String -- ^ Other method

derive instance eqDIDMethod :: Eq DIDMethod
derive instance ordDIDMethod :: Ord DIDMethod

instance showDIDMethod :: Show DIDMethod where
  show = didMethodLabel

-- | Get string label for DID method.
didMethodLabel :: DIDMethod -> String
didMethodLabel MethodKey = "key"
didMethodLabel MethodWeb = "web"
didMethodLabel MethodEthr = "ethr"
didMethodLabel MethodIon = "ion"
didMethodLabel MethodPkh = "pkh"
didMethodLabel (MethodOther m) = m

-- | Parse string to DID method.
parseDIDMethod :: String -> DIDMethod
parseDIDMethod "key" = MethodKey
parseDIDMethod "web" = MethodWeb
parseDIDMethod "ethr" = MethodEthr
parseDIDMethod "ion" = MethodIon
parseDIDMethod "pkh" = MethodPkh
parseDIDMethod other = MethodOther other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // did
-- ═════════════════════════════════════════════════════════════════════════════

-- | DID - Decentralized Identifier.
type DID =
  { method :: DIDMethod
  , identifier :: String  -- Method-specific identifier
  }

-- | Construct a DID.
did :: DIDMethod -> String -> DID
did m i = { method: m, identifier: i }

-- | Get DID method.
didMethod :: DID -> DIDMethod
didMethod d = d.method

-- | Get method-specific identifier.
didIdentifier :: DID -> String
didIdentifier d = d.identifier

-- | Format DID as string.
didString :: DID -> String
didString d = "did:" <> didMethodLabel d.method <> ":" <> d.identifier

-- | Check if two DIDs are equal.
sameDID :: DID -> DID -> Boolean
sameDID d1 d2 = d1.method == d2.method && d1.identifier == d2.identifier

-- | Show DID for debug output.
showDID :: DID -> String
showDID d = "(DID " <> didString d <> ")"

-- | Parse DID from string.
parseDID :: String -> Maybe DID
parseDID s =
  let parts = split (Pattern ":") s
  in if length parts >= 3
     then case parts !! 0 of
            Just "did" -> case parts !! 1 of
              Just methodStr -> case parts !! 2 of
                Just _ ->
                  -- Join remaining parts in case identifier contains colons
                  let remainingParts = dropFirst 2 parts
                      identifier = joinWith ":" remainingParts
                  in Just { method: parseDIDMethod methodStr, identifier: identifier }
                Nothing -> Nothing
              Nothing -> Nothing
            _ -> Nothing
     else Nothing

-- | Drop first n elements.
dropFirst :: forall a. Int -> Array a -> Array a
dropFirst = drop

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // verification method type
-- ═════════════════════════════════════════════════════════════════════════════

-- | VerificationMethodType - cryptographic key types.
data VerificationMethodType
  = Ed25519VerificationKey2020
  | EcdsaSecp256k1VerificationKey2019
  | JsonWebKey2020
  | X25519KeyAgreementKey2020
  | Bls12381G1Key2020
  | Bls12381G2Key2020

derive instance eqVerificationMethodType :: Eq VerificationMethodType
derive instance ordVerificationMethodType :: Ord VerificationMethodType

instance showVerificationMethodType :: Show VerificationMethodType where
  show = verificationMethodTypeLabel

-- | Get label for verification method type.
verificationMethodTypeLabel :: VerificationMethodType -> String
verificationMethodTypeLabel Ed25519VerificationKey2020 = "Ed25519VerificationKey2020"
verificationMethodTypeLabel EcdsaSecp256k1VerificationKey2019 = "EcdsaSecp256k1VerificationKey2019"
verificationMethodTypeLabel JsonWebKey2020 = "JsonWebKey2020"
verificationMethodTypeLabel X25519KeyAgreementKey2020 = "X25519KeyAgreementKey2020"
verificationMethodTypeLabel Bls12381G1Key2020 = "Bls12381G1Key2020"
verificationMethodTypeLabel Bls12381G2Key2020 = "Bls12381G2Key2020"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // verification method
-- ═════════════════════════════════════════════════════════════════════════════

-- | VerificationMethod - public key associated with a DID.
type VerificationMethod =
  { id :: String              -- Full ID (e.g., "did:key:z6Mk...#keys-1")
  , methodType :: VerificationMethodType
  , controller :: String      -- DID that controls this key
  , publicKeyMultibase :: String  -- Multibase-encoded public key
  }

-- | Construct a verification method.
verificationMethod :: String -> VerificationMethodType -> String -> String -> VerificationMethod
verificationMethod i t c pk =
  { id: i
  , methodType: t
  , controller: c
  , publicKeyMultibase: pk
  }

-- | Get verification method ID.
verificationMethodId :: VerificationMethod -> String
verificationMethodId v = v.id

-- | Get verification method type.
verificationMethodType :: VerificationMethod -> VerificationMethodType
verificationMethodType v = v.methodType

-- | Get controller DID.
verificationMethodController :: VerificationMethod -> String
verificationMethodController v = v.controller

-- | Get public key (multibase).
verificationMethodPublicKey :: VerificationMethod -> String
verificationMethodPublicKey v = v.publicKeyMultibase

-- | Check if two verification methods are equal.
sameVerificationMethod :: VerificationMethod -> VerificationMethod -> Boolean
sameVerificationMethod v1 v2 =
  v1.id == v2.id &&
  v1.methodType == v2.methodType &&
  v1.controller == v2.controller &&
  v1.publicKeyMultibase == v2.publicKeyMultibase

-- | Show verification method for debug output.
showVerificationMethod :: VerificationMethod -> String
showVerificationMethod v =
  "(VerificationMethod " <> v.id <> " " <> show v.methodType <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // did document
-- ═════════════════════════════════════════════════════════════════════════════

-- | DIDDocument - DID resolution result containing verification methods.
type DIDDocument =
  { id :: String                          -- The DID itself
  , controller :: Maybe String            -- Optional controlling DID
  , verificationMethod :: Array VerificationMethod
  , authentication :: Array String        -- IDs of methods for authentication
  , assertionMethod :: Array String       -- IDs of methods for assertions
  }

-- | Construct a DID document.
didDocument :: String 
            -> Maybe String 
            -> Array VerificationMethod 
            -> Array String 
            -> Array String 
            -> DIDDocument
didDocument i ctrl vms auth assert =
  { id: i
  , controller: ctrl
  , verificationMethod: vms
  , authentication: auth
  , assertionMethod: assert
  }

-- | Get DID document ID.
didDocumentId :: DIDDocument -> String
didDocumentId d = d.id

-- | Get controller.
didDocumentController :: DIDDocument -> Maybe String
didDocumentController d = d.controller

-- | Get verification methods.
didDocumentVerificationMethods :: DIDDocument -> Array VerificationMethod
didDocumentVerificationMethods d = d.verificationMethod

-- | Get authentication method IDs.
didDocumentAuthentication :: DIDDocument -> Array String
didDocumentAuthentication d = d.authentication

-- | Get assertion method IDs.
didDocumentAssertionMethod :: DIDDocument -> Array String
didDocumentAssertionMethod d = d.assertionMethod

-- | Check if two DID documents have the same ID.
sameDocument :: DIDDocument -> DIDDocument -> Boolean
sameDocument d1 d2 = d1.id == d2.id

-- | Show DID document for debug output.
showDocument :: DIDDocument -> String
showDocument d = "(DIDDocument " <> d.id <> ")"
