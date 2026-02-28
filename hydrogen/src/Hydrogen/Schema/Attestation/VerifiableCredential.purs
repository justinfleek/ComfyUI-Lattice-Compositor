-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // attestation // verifiable credential
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | W3C Verifiable Credentials specification.
-- |
-- | Verifiable Credentials (VCs) are tamper-evident credentials
-- | that can be cryptographically verified.
-- |
-- | A VC contains:
-- | - Issuer: who created/signed the credential
-- | - Subject: who the credential is about
-- | - Claims: the actual credential data
-- | - Proof: cryptographic signature

module Hydrogen.Schema.Attestation.VerifiableCredential
  ( -- * Credential Types
    CredentialType(..)
  , credentialTypeLabel
  
  -- * Credential Status
  , CredentialStatus(..)
  , credentialStatusLabel
  
  -- * Proof Type
  , ProofType(..)
  , proofTypeLabel
  
  -- * Proof
  , Proof
  , proof
  , proofType
  , proofCreated
  , proofVerificationMethod
  , proofProofPurpose
  , proofProofValue
  
  -- * Verifiable Credential
  , VerifiableCredential
  , verifiableCredential
  , vcId
  , vcType
  , vcIssuer
  , vcIssuanceDate
  , vcExpirationDate
  , vcCredentialSubject
  , vcProof
  , vcStatus
  
  -- * Credential Subject
  , CredentialSubject
  , credentialSubject
  , subjectId
  , subjectClaims
  
  -- * Verifiable Presentation
  , VerifiablePresentation
  , verifiablePresentation
  , vpId
  , vpHolder
  , vpVerifiableCredential
  , vpProof
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // credential type
-- ═════════════════════════════════════════════════════════════════════════════

-- | CredentialType - common credential types.
data CredentialType
  = VerifiableCredentialType        -- ^ Base type
  | IdentityCredential              -- ^ Identity/KYC
  | UniversityDegreeCredential      -- ^ Educational
  | EmploymentCredential            -- ^ Employment verification
  | MembershipCredential            -- ^ Organization membership
  | AgeVerificationCredential       -- ^ Age verification
  | AddressCredential               -- ^ Address proof
  | HealthCredential                -- ^ Health/vaccination
  | LicenseCredential               -- ^ Professional license
  | CustomCredential String         -- ^ Custom type

derive instance eqCredentialType :: Eq CredentialType
derive instance ordCredentialType :: Ord CredentialType

instance showCredentialType :: Show CredentialType where
  show = credentialTypeLabel

-- | Get label for credential type.
credentialTypeLabel :: CredentialType -> String
credentialTypeLabel VerifiableCredentialType = "VerifiableCredential"
credentialTypeLabel IdentityCredential = "IdentityCredential"
credentialTypeLabel UniversityDegreeCredential = "UniversityDegreeCredential"
credentialTypeLabel EmploymentCredential = "EmploymentCredential"
credentialTypeLabel MembershipCredential = "MembershipCredential"
credentialTypeLabel AgeVerificationCredential = "AgeVerificationCredential"
credentialTypeLabel AddressCredential = "AddressCredential"
credentialTypeLabel HealthCredential = "HealthCredential"
credentialTypeLabel LicenseCredential = "LicenseCredential"
credentialTypeLabel (CustomCredential t) = t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // credential status
-- ═════════════════════════════════════════════════════════════════════════════

-- | CredentialStatus - revocation status.
data CredentialStatus
  = StatusActive
  | StatusRevoked
  | StatusSuspended
  | StatusExpired

derive instance eqCredentialStatus :: Eq CredentialStatus
derive instance ordCredentialStatus :: Ord CredentialStatus

instance showCredentialStatus :: Show CredentialStatus where
  show = credentialStatusLabel

-- | Get label for credential status.
credentialStatusLabel :: CredentialStatus -> String
credentialStatusLabel StatusActive = "active"
credentialStatusLabel StatusRevoked = "revoked"
credentialStatusLabel StatusSuspended = "suspended"
credentialStatusLabel StatusExpired = "expired"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // proof type
-- ═════════════════════════════════════════════════════════════════════════════

-- | ProofType - cryptographic proof types.
data ProofType
  = Ed25519Signature2020
  | EcdsaSecp256k1Signature2019
  | JsonWebSignature2020
  | BbsBlsSignature2020
  | BbsBlsSignatureProof2020

derive instance eqProofType :: Eq ProofType
derive instance ordProofType :: Ord ProofType

instance showProofType :: Show ProofType where
  show = proofTypeLabel

-- | Get label for proof type.
proofTypeLabel :: ProofType -> String
proofTypeLabel Ed25519Signature2020 = "Ed25519Signature2020"
proofTypeLabel EcdsaSecp256k1Signature2019 = "EcdsaSecp256k1Signature2019"
proofTypeLabel JsonWebSignature2020 = "JsonWebSignature2020"
proofTypeLabel BbsBlsSignature2020 = "BbsBlsSignature2020"
proofTypeLabel BbsBlsSignatureProof2020 = "BbsBlsSignatureProof2020"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // proof
-- ═════════════════════════════════════════════════════════════════════════════

-- | Proof - cryptographic proof for credential.
type Proof =
  { proofType :: ProofType
  , created :: String             -- ISO8601 timestamp
  , verificationMethod :: String  -- DID URL of key used
  , proofPurpose :: String        -- e.g., "assertionMethod"
  , proofValue :: String          -- Base64/multibase signature
  }

-- | Construct a proof.
proof :: ProofType -> String -> String -> String -> String -> Proof
proof pt created vm purpose value =
  { proofType: pt
  , created: created
  , verificationMethod: vm
  , proofPurpose: purpose
  , proofValue: value
  }

-- | Get proof type.
proofType :: Proof -> ProofType
proofType p = p.proofType

-- | Get creation timestamp.
proofCreated :: Proof -> String
proofCreated p = p.created

-- | Get verification method.
proofVerificationMethod :: Proof -> String
proofVerificationMethod p = p.verificationMethod

-- | Get proof purpose.
proofProofPurpose :: Proof -> String
proofProofPurpose p = p.proofPurpose

-- | Get proof value (signature).
proofProofValue :: Proof -> String
proofProofValue p = p.proofValue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // credential subject
-- ═════════════════════════════════════════════════════════════════════════════

-- | CredentialSubject - who the credential is about.
type CredentialSubject =
  { id :: Maybe String            -- Optional DID of subject
  , claims :: Array { key :: String, value :: String }
  }

-- | Construct a credential subject.
credentialSubject :: Maybe String -> Array { key :: String, value :: String } -> CredentialSubject
credentialSubject i c = { id: i, claims: c }

-- | Get subject ID.
subjectId :: CredentialSubject -> Maybe String
subjectId s = s.id

-- | Get claims.
subjectClaims :: CredentialSubject -> Array { key :: String, value :: String }
subjectClaims s = s.claims

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // verifiable credential
-- ═════════════════════════════════════════════════════════════════════════════

-- | VerifiableCredential - W3C VC 1.1 compliant credential.
type VerifiableCredential =
  { id :: Maybe String            -- Optional credential ID
  , vcType :: Array CredentialType
  , issuer :: String              -- DID of issuer
  , issuanceDate :: String        -- ISO8601
  , expirationDate :: Maybe String
  , credentialSubject :: CredentialSubject
  , proof :: Proof
  , credentialStatus :: Maybe CredentialStatus
  }

-- | Construct a verifiable credential.
verifiableCredential :: Maybe String
                     -> Array CredentialType
                     -> String
                     -> String
                     -> Maybe String
                     -> CredentialSubject
                     -> Proof
                     -> Maybe CredentialStatus
                     -> VerifiableCredential
verifiableCredential i types issuer issued expires subj prf status =
  { id: i
  , vcType: types
  , issuer: issuer
  , issuanceDate: issued
  , expirationDate: expires
  , credentialSubject: subj
  , proof: prf
  , credentialStatus: status
  }

-- | Get credential ID.
vcId :: VerifiableCredential -> Maybe String
vcId vc = vc.id

-- | Get credential types.
vcType :: VerifiableCredential -> Array CredentialType
vcType vc = vc.vcType

-- | Get issuer DID.
vcIssuer :: VerifiableCredential -> String
vcIssuer vc = vc.issuer

-- | Get issuance date.
vcIssuanceDate :: VerifiableCredential -> String
vcIssuanceDate vc = vc.issuanceDate

-- | Get expiration date.
vcExpirationDate :: VerifiableCredential -> Maybe String
vcExpirationDate vc = vc.expirationDate

-- | Get credential subject.
vcCredentialSubject :: VerifiableCredential -> CredentialSubject
vcCredentialSubject vc = vc.credentialSubject

-- | Get proof.
vcProof :: VerifiableCredential -> Proof
vcProof vc = vc.proof

-- | Get status.
vcStatus :: VerifiableCredential -> Maybe CredentialStatus
vcStatus vc = vc.credentialStatus

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // verifiable presentation
-- ═════════════════════════════════════════════════════════════════════════════

-- | VerifiablePresentation - collection of credentials presented together.
type VerifiablePresentation =
  { id :: Maybe String
  , holder :: String              -- DID of presenter
  , verifiableCredential :: Array VerifiableCredential
  , proof :: Proof
  }

-- | Construct a verifiable presentation.
verifiablePresentation :: Maybe String
                       -> String
                       -> Array VerifiableCredential
                       -> Proof
                       -> VerifiablePresentation
verifiablePresentation i holder creds prf =
  { id: i
  , holder: holder
  , verifiableCredential: creds
  , proof: prf
  }

-- | Get presentation ID.
vpId :: VerifiablePresentation -> Maybe String
vpId vp = vp.id

-- | Get holder DID.
vpHolder :: VerifiablePresentation -> String
vpHolder vp = vp.holder

-- | Get credentials.
vpVerifiableCredential :: VerifiablePresentation -> Array VerifiableCredential
vpVerifiableCredential vp = vp.verifiableCredential

-- | Get proof.
vpProof :: VerifiablePresentation -> Proof
vpProof vp = vp.proof
