/**
 * Template Signature Verification Service
 *
 * Verifies Ed25519 signatures on .lattice.json template files.
 * Official templates are signed by Lattice's private key.
 *
 * SECURITY:
 * - Only OFFICIAL_PUBLIC_KEY should sign official templates
 * - Unsigned templates show warning to user
 * - Signature covers: templateConfig, layers, compositions (not metadata like name)
 * - Third-party templates are allowed but marked as unverified
 *
 * Signature format in .lattice.json:
 * {
 *   "templateConfig": { ... },
 *   "layers": [ ... ],
 *   "_signature": {
 *     "algorithm": "Ed25519",
 *     "publicKey": "base64-encoded-public-key",
 *     "signature": "base64-encoded-signature",
 *     "signedAt": "ISO-timestamp",
 *     "version": "1.0"
 *   }
 * }
 *
 * @see AUDIT/SECURITY_ARCHITECTURE.md
 */

import { logSecurityWarning } from "./auditLog";

// TweetNaCl type interface (library is optional, loaded dynamically)
interface NaClSignDetached {
  (message: Uint8Array, secretKey: Uint8Array): Uint8Array;
  verify(
    message: Uint8Array,
    signature: Uint8Array,
    publicKey: Uint8Array,
  ): boolean;
}

interface TweetNaCl {
  sign: {
    keyPair(): { publicKey: Uint8Array; secretKey: Uint8Array };
    detached: NaClSignDetached;
  };
}

/**
 * Dynamically import tweetnacl.
 * Returns null if not installed (signing/verification will fail gracefully).
 */
async function loadNaCl(): Promise<TweetNaCl | null> {
  try {
    return await import("tweetnacl");
  } catch {
    console.warn(
      "[SECURITY] tweetnacl not installed - template signing unavailable",
    );
    return null;
  }
}

// ============================================================================
// Types
// ============================================================================

export interface TemplateSignature {
  /** Signature algorithm (always "Ed25519") */
  algorithm: "Ed25519";
  /** Base64-encoded public key that created this signature */
  publicKey: string;
  /** Base64-encoded signature */
  signature: string;
  /** When the template was signed */
  signedAt: string;
  /** Signature format version */
  version: string;
}

export interface VerificationResult {
  /** Whether the template has a signature at all */
  isSigned: boolean;
  /** Whether the signature is valid */
  isValid: boolean;
  /** Whether it's signed by the official Lattice key */
  isOfficial: boolean;
  /** Verification status for UI display */
  status: "official" | "third-party-valid" | "third-party-invalid" | "unsigned";
  /** Human-readable message */
  message: string;
  /** Signer public key (if signed) */
  signerPublicKey?: string;
  /** When it was signed (if signed) */
  signedAt?: string;
}

export interface SignedTemplate {
  /** Template data (everything except _signature) */
  data: Record<string, unknown>;
  /** Signature block */
  _signature?: TemplateSignature;
}

// ============================================================================
// Constants
// ============================================================================

/**
 * Official Lattice public key for template signing.
 *
 * SECURITY: This key should ONLY exist in this file.
 * The corresponding private key is kept offline and never committed.
 *
 * To generate a new keypair (Node.js):
 * ```
 * const nacl = require('tweetnacl');
 * const keypair = nacl.sign.keyPair();
 * console.log('Public:', Buffer.from(keypair.publicKey).toString('base64'));
 * console.log('Private:', Buffer.from(keypair.secretKey).toString('base64'));
 * ```
 */
const OFFICIAL_PUBLIC_KEY = "xmCWXfRKw7DQLuyQdqQIJlAb+r0arpUu2oVjTdJgv/k=";

/**
 * Signature version we understand.
 */
const SUPPORTED_VERSIONS = ["1.0"];

// ============================================================================
// Verification Functions
// ============================================================================

/**
 * Verify a template file.
 *
 * @param template - Parsed .lattice.json content
 * @returns Verification result
 */
export async function verifyTemplate(
  template: unknown,
): Promise<VerificationResult> {
  // Type check
  if (!template || typeof template !== "object") {
    return {
      isSigned: false,
      isValid: false,
      isOfficial: false,
      status: "unsigned",
      message: "Invalid template format",
    };
  }

  const signedTemplate = template as SignedTemplate;
  const signature = signedTemplate._signature;

  // Check if signed at all
  if (!signature) {
    return {
      isSigned: false,
      isValid: false,
      isOfficial: false,
      status: "unsigned",
      message:
        "Template is not signed. Exercise caution with untrusted templates.",
    };
  }

  // Validate signature structure
  if (!isValidSignatureStructure(signature)) {
    await logSecurityWarning("Invalid template signature structure", {
      signature,
    });
    return {
      isSigned: true,
      isValid: false,
      isOfficial: false,
      status: "third-party-invalid",
      message: "Template has invalid signature format.",
    };
  }

  // Check version
  if (!SUPPORTED_VERSIONS.includes(signature.version)) {
    return {
      isSigned: true,
      isValid: false,
      isOfficial: false,
      status: "third-party-invalid",
      message: `Unsupported signature version: ${signature.version}`,
    };
  }

  // Verify the signature
  try {
    // Extract template data (everything except _signature) for verification
    const { _signature: _, ...templateData } = template as Record<
      string,
      unknown
    >;
    const isValid = await verifySignature(templateData, signature);

    if (!isValid) {
      await logSecurityWarning("Template signature verification failed", {
        publicKey: signature.publicKey,
        signedAt: signature.signedAt,
      });
      return {
        isSigned: true,
        isValid: false,
        isOfficial: false,
        status: "third-party-invalid",
        message:
          "Template signature is invalid. The template may have been tampered with.",
        signerPublicKey: signature.publicKey,
        signedAt: signature.signedAt,
      };
    }

    // Check if it's the official key
    const isOfficial = signature.publicKey === OFFICIAL_PUBLIC_KEY;

    if (isOfficial) {
      return {
        isSigned: true,
        isValid: true,
        isOfficial: true,
        status: "official",
        message: "Verified official Lattice template.",
        signerPublicKey: signature.publicKey,
        signedAt: signature.signedAt,
      };
    }

    // Valid but third-party
    return {
      isSigned: true,
      isValid: true,
      isOfficial: false,
      status: "third-party-valid",
      message:
        "Template is signed by a third party. Verify you trust the source.",
      signerPublicKey: signature.publicKey,
      signedAt: signature.signedAt,
    };
  } catch (error) {
    console.error("[SECURITY] Signature verification error:", error);
    return {
      isSigned: true,
      isValid: false,
      isOfficial: false,
      status: "third-party-invalid",
      message: `Signature verification failed: ${error instanceof Error ? error.message : "Unknown error"}`,
    };
  }
}

/**
 * Check if a template is officially signed (quick check).
 */
export async function isOfficialTemplate(template: unknown): Promise<boolean> {
  const result = await verifyTemplate(template);
  return result.isOfficial;
}

/**
 * Get verification status for UI display.
 */
export function getVerificationBadge(result: VerificationResult): {
  label: string;
  color: "green" | "yellow" | "red" | "gray";
  icon: string;
} {
  switch (result.status) {
    case "official":
      return {
        label: "Verified by Lattice",
        color: "green",
        icon: "✓",
      };
    case "third-party-valid":
      return {
        label: "Third-party (valid signature)",
        color: "yellow",
        icon: "⚠",
      };
    case "third-party-invalid":
      return {
        label: "Invalid signature",
        color: "red",
        icon: "✗",
      };
    default:
      return {
        label: "Unsigned template",
        color: "gray",
        icon: "?",
      };
  }
}

// ============================================================================
// Signing Functions (for build-time signing)
// ============================================================================

/**
 * Sign a template with a private key.
 *
 * SECURITY: This should only be used in build scripts, not at runtime.
 * The private key should never be in the browser.
 *
 * @param template - Template data to sign
 * @param privateKeyBase64 - Base64-encoded Ed25519 private key (64 bytes)
 * @returns Template with _signature block added
 */
export async function signTemplate(
  template: Record<string, unknown>,
  privateKeyBase64: string,
): Promise<SignedTemplate> {
  // This function requires tweetnacl which may not be bundled
  // It's meant for build-time use only
  const nacl = await loadNaCl();
  if (!nacl) {
    throw new Error("tweetnacl not installed - run: npm install tweetnacl");
  }

  try {
    const privateKey = base64ToUint8Array(privateKeyBase64);
    const publicKey = privateKey.slice(32); // Ed25519 public key is last 32 bytes

    // Create canonical JSON of template data (excluding any existing signature)
    const { _signature, ...templateData } = template;
    const canonical = createCanonicalJson(templateData);
    const messageBytes = new TextEncoder().encode(canonical);

    // Sign
    const signatureBytes = nacl.sign.detached(messageBytes, privateKey);

    const signature: TemplateSignature = {
      algorithm: "Ed25519",
      publicKey: uint8ArrayToBase64(publicKey),
      signature: uint8ArrayToBase64(signatureBytes),
      signedAt: new Date().toISOString(),
      version: "1.0",
    };

    return {
      data: templateData,
      _signature: signature,
    };
  } catch (error) {
    throw new Error(
      `Failed to sign template: ${error instanceof Error ? error.message : "Unknown error"}`,
    );
  }
}

// ============================================================================
// Internal Functions
// ============================================================================

/**
 * Verify an Ed25519 signature.
 */
async function verifySignature(
  data: Record<string, unknown>,
  signature: TemplateSignature,
): Promise<boolean> {
  const nacl = await loadNaCl();
  if (!nacl) {
    console.error(
      "[SECURITY] tweetnacl not installed - cannot verify signatures",
    );
    return false;
  }

  try {
    const publicKey = base64ToUint8Array(signature.publicKey);
    const signatureBytes = base64ToUint8Array(signature.signature);

    // Create canonical JSON of the data
    const canonical = createCanonicalJson(data);
    const messageBytes = new TextEncoder().encode(canonical);

    // Verify
    return nacl.sign.detached.verify(messageBytes, signatureBytes, publicKey);
  } catch (error) {
    console.error("[SECURITY] Signature verification error:", error);
    return false;
  }
}

/**
 * Validate signature structure.
 */
function isValidSignatureStructure(sig: unknown): sig is TemplateSignature {
  if (!sig || typeof sig !== "object") return false;

  const s = sig as Record<string, unknown>;

  return (
    s.algorithm === "Ed25519" &&
    typeof s.publicKey === "string" &&
    typeof s.signature === "string" &&
    typeof s.signedAt === "string" &&
    typeof s.version === "string"
  );
}

/**
 * Create canonical JSON for signing.
 * Keys are sorted alphabetically at ALL levels for deterministic output.
 *
 * SECURITY: This ensures identical objects always produce identical signatures,
 * regardless of property insertion order.
 */
function createCanonicalJson(obj: unknown): string {
  return JSON.stringify(obj, (_, value) => {
    // Only sort object keys, leave arrays and primitives alone
    if (value && typeof value === "object" && !Array.isArray(value)) {
      const sorted: Record<string, unknown> = {};
      for (const key of Object.keys(value).sort()) {
        sorted[key] = value[key];
      }
      return sorted;
    }
    return value;
  });
}

/**
 * Convert base64 string to Uint8Array.
 */
function base64ToUint8Array(base64: string): Uint8Array {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes;
}

/**
 * Convert Uint8Array to base64 string.
 */
function uint8ArrayToBase64(bytes: Uint8Array): string {
  let binary = "";
  for (let i = 0; i < bytes.length; i++) {
    binary += String.fromCharCode(bytes[i]);
  }
  return btoa(binary);
}

// ============================================================================
// Template Loading with Verification
// ============================================================================

/**
 * Load and verify a template from JSON.
 * Returns both the template data and verification result.
 */
export async function loadAndVerifyTemplate(json: string): Promise<{
  template: Record<string, unknown>;
  verification: VerificationResult;
}> {
  try {
    const parsed = JSON.parse(json);
    const verification = await verifyTemplate(parsed);

    // Remove signature from returned data
    const { _signature, ...templateData } = parsed;

    return {
      template: templateData,
      verification,
    };
  } catch (error) {
    return {
      template: {},
      verification: {
        isSigned: false,
        isValid: false,
        isOfficial: false,
        status: "unsigned",
        message: `Failed to parse template: ${error instanceof Error ? error.message : "Unknown error"}`,
      },
    };
  }
}

/**
 * Check if a template should show a warning before loading.
 */
export function shouldWarnBeforeLoading(
  verification: VerificationResult,
): boolean {
  return verification.status !== "official";
}

/**
 * Get warning message for non-official templates.
 */
export function getLoadingWarning(
  verification: VerificationResult,
): string | null {
  switch (verification.status) {
    case "official":
      return null;
    case "third-party-valid":
      return "This template is signed by a third party. Only load templates from sources you trust.";
    case "third-party-invalid":
      return "WARNING: This template has an invalid signature. It may have been tampered with. Do not load unless you trust the source.";
    case "unsigned":
      return "This template is unsigned. Only load templates from sources you trust.";
  }
}
