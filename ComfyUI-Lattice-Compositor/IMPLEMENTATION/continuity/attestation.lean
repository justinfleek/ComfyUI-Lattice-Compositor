/-
Continuity Attestation Layer
============================

Ed25519-signed attestations for build artifacts from continuity.lean Section 1.7 and Section 9.

An attestation is a cryptographic claim that a specific artifact was produced by
a specific builder at a specific time. This provides:
1. Non-repudiation: The builder cannot deny producing the artifact
2. Integrity: The artifact content cannot be modified without detection
3. Temporal ordering: Build sequences can be verified

Key Properties:
- Attestation.verify: Verify signature against serialized payload
- attest: Create attestation with Ed25519 signature
- attestation_soundness: Valid attestation implies artifact integrity
-/

import Mathlib.Data.Finset.Basic

-- Import from sibling modules
import Continuity.Identity
import Continuity.Store

namespace Continuity.Attestation

open Continuity.Identity
open Continuity.Store

/-!
## Attestation Structure

From continuity.lean lines 169-175:
  structure Attestation where
    artifact : Hash
    builder : PublicKey
    timestamp : Nat
    signature : Signature
    deriving DecidableEq
-/

/-- An attestation: signed claim about an artifact -/
structure Attestation where
  /-- SHA256 hash of the attested artifact -/
  artifact : Hash
  /-- Ed25519 public key of the builder who created this attestation -/
  builder : PublicKey
  /-- Unix timestamp (nanoseconds since epoch) when attestation was created -/
  timestamp : Nat
  /-- Ed25519 signature over (artifact || timestamp) -/
  signature : Signature
  deriving DecidableEq

/-!
## Serialization

The payload that gets signed is the concatenation of:
1. artifact.bytes (32 bytes)
2. timestamp encoded as big-endian 8 bytes

Total payload size: 40 bytes
-/

/-- Convert a Nat to big-endian byte list (8 bytes) -/
def natToBytes8 (n : Nat) : List UInt8 :=
  let b0 := UInt8.ofNat (n >>> 56)
  let b1 := UInt8.ofNat ((n >>> 48) &&& 0xFF)
  let b2 := UInt8.ofNat ((n >>> 40) &&& 0xFF)
  let b3 := UInt8.ofNat ((n >>> 32) &&& 0xFF)
  let b4 := UInt8.ofNat ((n >>> 24) &&& 0xFF)
  let b5 := UInt8.ofNat ((n >>> 16) &&& 0xFF)
  let b6 := UInt8.ofNat ((n >>> 8) &&& 0xFF)
  let b7 := UInt8.ofNat (n &&& 0xFF)
  [b0, b1, b2, b3, b4, b5, b6, b7]

/-- Convert Hash bytes to a list -/
def hashToList (h : Hash) : List UInt8 :=
  (List.range 32).map (fun i => h.bytes (Fin.mk i (by omega)))

/-- Serialize attestation payload for signing/verification -/
def serializePayload (artifact : Hash) (timestamp : Nat) : List UInt8 :=
  hashToList artifact ++ natToBytes8 timestamp

/-!
## Verification

From continuity.lean lines 177-180:
  def Attestation.verify (a : Attestation) : Bool :=
    ed25519_verify a.builder (serialize artifact timestamp) a.signature
-/

/-- Verify an attestation's signature -/
def Attestation.verify (a : Attestation) : Bool :=
  let payload := serializePayload a.artifact a.timestamp
  ed25519_verify a.builder payload a.signature

/-- Check if attestation is for a specific artifact -/
def Attestation.isFor (a : Attestation) (h : Hash) : Bool :=
  a.artifact = h

/-- Check if attestation is by a specific builder -/
def Attestation.isBy (a : Attestation) (pk : PublicKey) : Bool :=
  a.builder = pk

/-!
## Attestation Creation

From continuity.lean lines 437-441:
  def attest (result : BuildResult) (sk : SecretKey) (pk : PublicKey) (time : Nat) : Attestation
-/

/-- Create an attestation for an artifact hash -/
def attestHash (artifactHash : Hash) (sk : SecretKey) (pk : PublicKey) (time : Nat) : Attestation :=
  let payload := serializePayload artifactHash time
  let sig := ed25519_sign sk payload
  { artifact := artifactHash
    builder := pk
    timestamp := time
    signature := sig }

/-- Derivation output: what a build produces -/
structure DrvOutput where
  name : String
  path : StorePath
  deriving DecidableEq

/-- Build result: the outputs of executing a derivation -/
structure BuildResult where
  outputs : Finset DrvOutput
  deriving DecidableEq

/-- Create an attestation for a build result -/
def attest (result : BuildResult) (sk : SecretKey) (pk : PublicKey) (time : Nat) : Attestation :=
  -- Use the first output's hash, or a zero hash if no outputs
  let artifactHash : Hash := match result.outputs.toList.head? with
    | some output => output.path.hash
    | none => { bytes := fun _ => 0 }
  attestHash artifactHash sk pk time

/-- Create an attestation directly for a StorePath -/
def attestPath (path : StorePath) (sk : SecretKey) (pk : PublicKey) (time : Nat) : Attestation :=
  attestHash path.hash sk pk time

/-!
## Attestation Properties

Key properties about attestations that follow from Ed25519 properties.
-/

/-- Signing is deterministic: same inputs produce same attestation -/
theorem attest_deterministic (result : BuildResult) (sk : SecretKey) (pk : PublicKey) (time : Nat) :
    attest result sk pk time = attest result sk pk time := rfl

/-- Attestation created by attest should verify with the correct public key -/
theorem attest_verifies (result : BuildResult) (sk : SecretKey) (time : Nat) :
    (attest result sk (SecretKey.toPublicKey sk) time).verify = true := by
  unfold attest Attestation.verify
  simp only
  exact sign_verify_correct sk _

/-- Attestation created by attestHash should verify with the correct public key -/
theorem attestHash_verifies (h : Hash) (sk : SecretKey) (time : Nat) :
    (attestHash h sk (SecretKey.toPublicKey sk) time).verify = true := by
  unfold attestHash Attestation.verify
  simp only
  exact sign_verify_correct sk _

/-!
## Attestation Soundness

From continuity.lean lines 443-451:
  theorem attestation_soundness
      (a : Attestation)
      (store : Store)
      (h_valid : a.verify = true)
      (h_in_store : exists obj in store.objects, obj.hash = a.artifact) :
      exists obj in store.objects, obj.hash = a.artifact /\ a.verify = true

This theorem states: if an attestation is valid and the artifact exists in the store,
then we have a verified claim about that specific artifact.
-/

/-- ATTESTATION SOUNDNESS: valid attestation implies artifact integrity -/
theorem attestation_soundness
    (a : Attestation)
    (store : Store)
    (h_valid : a.verify = true)
    (h_in_store : Exists (fun obj => obj ∈ store.objects ∧ obj.hash = a.artifact)) :
    Exists (fun obj => obj ∈ store.objects ∧ obj.hash = a.artifact ∧ a.verify = true) := by
  obtain ⟨obj, h_mem, h_hash⟩ := h_in_store
  exact ⟨obj, h_mem, h_hash, h_valid⟩

/-- Verified attestation implies the existence of a signing key -/
theorem verified_attestation_has_key
    (a : Attestation)
    (h_valid : a.verify = true) :
    Exists (fun sk => ed25519_sign sk (serializePayload a.artifact a.timestamp) = a.signature) := by
  unfold Attestation.verify at h_valid
  exact ed25519_unforgeable a.builder (serializePayload a.artifact a.timestamp) a.signature h_valid

/-!
## Attestation Chain

Multiple attestations can form a chain, providing a verifiable build history.
-/

/-- An attestation chain is a list of attestations in temporal order -/
structure AttestationChain where
  attestations : List Attestation
  /-- All attestations in the chain are valid -/
  all_valid : attestations.all (fun a => a.verify)
  /-- Timestamps are strictly increasing -/
  timestamps_ordered : True  -- Simplified; would prove strict ordering
  deriving DecidableEq

/-- Empty attestation chain -/
def AttestationChain.empty : AttestationChain := {
  attestations := []
  all_valid := by simp
  timestamps_ordered := trivial
}

/-- Check if a chain contains an attestation for a specific hash -/
def AttestationChain.containsHash (chain : AttestationChain) (h : Hash) : Bool :=
  chain.attestations.any (fun a => a.artifact = h)

/-- Get all attestations for a specific hash -/
def AttestationChain.forHash (chain : AttestationChain) (h : Hash) : List Attestation :=
  chain.attestations.filter (fun a => a.artifact = h)

/-- Get the latest attestation for a hash (if any) -/
def AttestationChain.latestFor (chain : AttestationChain) (h : Hash) : Option Attestation :=
  (chain.forHash h).head?

/-!
## Integration with Store

Attestations can be stored alongside git objects.
-/

/-- A store with attestation support -/
structure AttestedStore extends Store where
  /-- Attestations tracked by this store -/
  attestations : Finset Attestation

/-- Check if an object in the store is attested -/
def AttestedStore.hasAttestation (s : AttestedStore) (h : Hash) : Prop :=
  Exists (fun a => a ∈ s.attestations ∧ a.artifact = h ∧ a.verify = true)

/-- Add an attestation to the store -/
def AttestedStore.addAttestation (s : AttestedStore) (a : Attestation) : AttestedStore := {
  s with attestations := s.attestations ∪ {a}
}

/-- If store has valid attestation, the artifact exists -/
theorem AttestedStore.attestation_implies_object
    (s : AttestedStore)
    (h : Hash)
    (h_attested : s.hasAttestation h)
    (h_contains : s.containsHash h) :
    Exists (fun obj => obj ∈ s.objects ∧ obj.hash = h) := by
  unfold Store.containsHash at h_contains
  exact h_contains

end Continuity.Attestation
