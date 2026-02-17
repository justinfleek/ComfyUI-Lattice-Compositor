/-
Continuity Identity Layer
=========================

Ed25519 cryptographic identity from continuity.lean section 1.6.

This module provides the type-level representation of Ed25519 cryptographic
primitives. The actual cryptographic operations are implemented in Python
using the `cryptography` library, with these Lean types providing formal
specification and verification.

Key Properties:
1. PublicKey: 32 bytes (compressed Edwards point)
2. SecretKey: 64 bytes (32 seed + 32 public key in Ed25519 format)
3. Signature: 64 bytes (R || S components)
4. Signing is deterministic (RFC 8032)
5. Signatures are unforgeable under EUF-CMA
-/

namespace Continuity.Identity

/-!
## Ed25519 Public Key

A 32-byte compressed Edwards curve point.
-/
structure PublicKey where
  bytes : Fin 32 -> UInt8
  deriving DecidableEq

/-!
## Ed25519 Secret Key

A 64-byte secret key consisting of:
- bytes[0..31]: The 32-byte seed (private scalar)
- bytes[32..63]: The corresponding 32-byte public key

This matches the standard Ed25519 "expanded" format used by most libraries.
-/
structure SecretKey where
  bytes : Fin 64 -> UInt8

/-!
## Ed25519 Signature

A 64-byte signature consisting of:
- bytes[0..31]: R (compressed Edwards point)
- bytes[32..63]: S (scalar)
-/
structure Signature where
  bytes : Fin 64 -> UInt8
  deriving DecidableEq

/-!
## Cryptographic Operations (Abstract)

These axioms define the interface. Implementations must satisfy these properties.
-/

/-- Sign a message with a secret key. Deterministic per RFC 8032. -/
axiom ed25519_sign : SecretKey -> List UInt8 -> Signature

/-- Verify a signature against a public key and message. -/
axiom ed25519_verify : PublicKey -> List UInt8 -> Signature -> Bool

/--
Unforgeability: If verification succeeds, there exists a corresponding secret key.

This is the EUF-CMA (Existential Unforgeability under Chosen Message Attack) property.
In practice, this means:
- Without the secret key, an attacker cannot produce a valid signature
- Even with access to signatures of other messages, forgery is computationally infeasible
-/
axiom ed25519_unforgeable :
  forall pk msg sig, ed25519_verify pk msg sig = true ->
    Exists (fun sk => ed25519_sign sk msg = sig)

/-!
## Key Derivation

The public key can be derived from the secret key deterministically.
-/

/-- Extract the public key from a secret key (last 32 bytes). -/
def SecretKey.toPublicKey (sk : SecretKey) : PublicKey :=
  { bytes := fun i => sk.bytes (Fin.mk (32 + i.val) (by omega)) }

/-!
## Utility Functions
-/

/-- Check if a public key is the identity element (all zeros). -/
def PublicKey.isIdentity (pk : PublicKey) : Bool :=
  (List.range 32).all (fun i => pk.bytes (Fin.mk i (by omega)) == 0)

/-- Check if a signature is all zeros (invalid). -/
def Signature.isZero (sig : Signature) : Bool :=
  (List.range 64).all (fun i => sig.bytes (Fin.mk i (by omega)) == 0)

/-!
## Properties
-/

/-- Signing with the same key and message produces the same signature. -/
theorem sign_deterministic (sk : SecretKey) (msg : List UInt8) :
    ed25519_sign sk msg = ed25519_sign sk msg := rfl

/-- A signature created by sign should verify with the corresponding public key. -/
axiom sign_verify_correct :
  forall sk msg,
    ed25519_verify (SecretKey.toPublicKey sk) msg (ed25519_sign sk msg) = true

/-!
## Message Types for Signing
-/

/-- A typed message wrapper for signing context. -/
structure SignedMessage where
  payload : List UInt8
  signature : Signature
  signer : PublicKey
  deriving DecidableEq

/-- Verify a signed message. -/
def SignedMessage.verify (msg : SignedMessage) : Bool :=
  ed25519_verify msg.signer msg.payload msg.signature

/-- Create a signed message. -/
def sign_message (sk : SecretKey) (payload : List UInt8) : SignedMessage :=
  { payload := payload
    signature := ed25519_sign sk payload
    signer := SecretKey.toPublicKey sk }

/-- Signed messages created by sign_message always verify. -/
theorem sign_message_verifies (sk : SecretKey) (payload : List UInt8) :
    (sign_message sk payload).verify = true := by
  unfold sign_message SignedMessage.verify
  simp only
  exact sign_verify_correct sk payload

end Continuity.Identity
