#!/usr/bin/env node
/**
 * Template Signing Script
 *
 * Signs a .lattice.json template file with the official Lattice Ed25519 key.
 *
 * Usage:
 *   LATTICE_SIGNING_KEY="base64-private-key" node scripts/signTemplate.js template.lattice.json
 *
 * Output:
 *   Signed template JSON is written to stdout.
 *   Redirect to file: node scripts/signTemplate.js input.json > signed.json
 *
 * SECURITY:
 * - This script should NEVER be bundled in the browser
 * - The private key should be stored offline
 * - Only run this script in a secure environment
 *
 * @see src/services/security/templateVerifier.ts
 */

import { readFileSync } from 'fs';
import nacl from 'tweetnacl';

// ============================================================================
// Helpers
// ============================================================================

function base64ToUint8Array(base64) {
  const binary = Buffer.from(base64, 'base64');
  return new Uint8Array(binary);
}

function uint8ArrayToBase64(bytes) {
  return Buffer.from(bytes).toString('base64');
}

/**
 * Create canonical JSON for signing.
 * Keys are sorted alphabetically at ALL levels for deterministic output.
 */
function createCanonicalJson(obj) {
  return JSON.stringify(obj, (_, value) => {
    if (value && typeof value === 'object' && !Array.isArray(value)) {
      const sorted = {};
      for (const key of Object.keys(value).sort()) {
        sorted[key] = value[key];
      }
      return sorted;
    }
    return value;
  });
}

// ============================================================================
// Main
// ============================================================================

function main() {
  // Check arguments
  const args = process.argv.slice(2);
  if (args.length !== 1) {
    console.error('Usage: LATTICE_SIGNING_KEY="..." node scripts/signTemplate.js <template.lattice.json>');
    console.error('');
    console.error('Environment variables:');
    console.error('  LATTICE_SIGNING_KEY  Base64-encoded Ed25519 private key (64 bytes)');
    console.error('');
    console.error('Output:');
    console.error('  Signed template JSON is written to stdout');
    process.exit(1);
  }

  const templatePath = args[0];

  // Check for private key
  const privateKeyBase64 = process.env.LATTICE_SIGNING_KEY;
  if (!privateKeyBase64) {
    console.error('ERROR: LATTICE_SIGNING_KEY environment variable not set');
    console.error('');
    console.error('Set it with:');
    console.error('  export LATTICE_SIGNING_KEY="your-base64-private-key"');
    process.exit(1);
  }

  // Read template file
  let templateJson;
  try {
    templateJson = readFileSync(templatePath, 'utf-8');
  } catch (error) {
    console.error(`ERROR: Cannot read file: ${templatePath}`);
    console.error(error.message);
    process.exit(1);
  }

  // Parse template
  let template;
  try {
    template = JSON.parse(templateJson);
  } catch (error) {
    console.error(`ERROR: Invalid JSON in file: ${templatePath}`);
    console.error(error.message);
    process.exit(1);
  }

  // Remove any existing signature
  const { _signature, ...templateData } = template;

  // Decode private key
  let privateKey;
  try {
    privateKey = base64ToUint8Array(privateKeyBase64);
    if (privateKey.length !== 64) {
      throw new Error(`Expected 64 bytes, got ${privateKey.length}`);
    }
  } catch (error) {
    console.error('ERROR: Invalid private key format');
    console.error(error.message);
    process.exit(1);
  }

  // Extract public key (last 32 bytes of Ed25519 secret key)
  const publicKey = privateKey.slice(32);

  // Create canonical JSON of template data
  const canonical = createCanonicalJson(templateData);
  const messageBytes = new TextEncoder().encode(canonical);

  // Sign
  const signatureBytes = nacl.sign.detached(messageBytes, privateKey);

  // Create signature block
  const signature = {
    algorithm: 'Ed25519',
    publicKey: uint8ArrayToBase64(publicKey),
    signature: uint8ArrayToBase64(signatureBytes),
    signedAt: new Date().toISOString(),
    version: '1.0',
  };

  // Create signed template
  const signedTemplate = {
    ...templateData,
    _signature: signature,
  };

  // Output to stdout
  console.log(JSON.stringify(signedTemplate, null, 2));

  // Log success to stderr (so it doesn't pollute stdout)
  console.error(`SUCCESS: Signed template with key ${signature.publicKey.substring(0, 16)}...`);
  console.error(`Signature: ${signature.signature.substring(0, 32)}...`);
}

main();
