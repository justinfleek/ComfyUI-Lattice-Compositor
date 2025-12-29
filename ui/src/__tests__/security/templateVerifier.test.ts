/**
 * Template Signature Verification Tests
 *
 * Tests the Ed25519 signature verification for .lattice.json template files.
 *
 * SECURITY: These tests verify that:
 * 1. Officially signed templates are recognized as valid
 * 2. Tampered templates are rejected
 * 3. Unsigned templates are flagged appropriately
 * 4. Third-party signatures are distinguished from official ones
 *
 * @see src/services/security/templateVerifier.ts
 */

import { describe, it, expect } from 'vitest';
import {
  verifyTemplate,
  isOfficialTemplate,
  getVerificationBadge,
  loadAndVerifyTemplate,
  shouldWarnBeforeLoading,
  type VerificationResult,
} from '@/services/security/templateVerifier';

// ============================================================================
// Test Data
// ============================================================================

/**
 * Test template signed with the official Lattice key.
 * Generated using scripts/signTemplate.js with LATTICE_SIGNING_KEY env var.
 *
 * To regenerate:
 * LATTICE_SIGNING_KEY="gt0SdUQuTv6XFIR61+wMQ2BKDacdeNHRaEyw+k9yI0TGYJZd9ErDsNAu7JB2pAgmUBv6vRqulS7ahWNN0mC/+Q==" \
 *   node scripts/signTemplate.js test-template.json
 */
const OFFICIAL_SIGNED_TEMPLATE = {
  name: 'Test Template',
  version: '1.0.0',
  layers: [
    { id: 'layer1', name: 'Background', type: 'solid' },
    { id: 'layer2', name: 'Title', type: 'text' },
  ],
  _signature: {
    algorithm: 'Ed25519' as const,
    publicKey: 'xmCWXfRKw7DQLuyQdqQIJlAb+r0arpUu2oVjTdJgv/k=',
    // This signature will be generated in the test setup
    signature: '', // Placeholder - will be set in beforeAll or computed
    signedAt: '2024-01-01T00:00:00.000Z',
    version: '1.0',
  },
};

/**
 * Template signed by a different (third-party) key.
 */
const THIRD_PARTY_SIGNED_TEMPLATE = {
  name: 'Third Party Template',
  layers: [],
  _signature: {
    algorithm: 'Ed25519' as const,
    publicKey: 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=', // Different key
    signature: 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA',
    signedAt: '2024-01-01T00:00:00.000Z',
    version: '1.0',
  },
};

const UNSIGNED_TEMPLATE = {
  name: 'Unsigned Template',
  layers: [{ id: 'layer1', name: 'Test', type: 'solid' }],
};

const INVALID_SIGNATURE_TEMPLATE = {
  name: 'Tampered Template',
  layers: [{ id: 'layer1', name: 'MODIFIED AFTER SIGNING', type: 'solid' }],
  _signature: {
    algorithm: 'Ed25519' as const,
    publicKey: 'xmCWXfRKw7DQLuyQdqQIJlAb+r0arpUu2oVjTdJgv/k=',
    signature: 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA',
    signedAt: '2024-01-01T00:00:00.000Z',
    version: '1.0',
  },
};

// ============================================================================
// Helper to create a properly signed template for testing
// ============================================================================

/**
 * Create a properly signed template using tweetnacl.
 * This mimics what scripts/signTemplate.js does.
 */
async function createSignedTemplate(
  templateData: Record<string, unknown>,
  privateKeyBase64: string
): Promise<Record<string, unknown>> {
  const nacl = await import('tweetnacl');

  const privateKey = base64ToUint8Array(privateKeyBase64);
  const publicKey = privateKey.slice(32);

  const canonical = createCanonicalJson(templateData);
  const messageBytes = new TextEncoder().encode(canonical);
  const signatureBytes = nacl.sign.detached(messageBytes, privateKey);

  return {
    ...templateData,
    _signature: {
      algorithm: 'Ed25519',
      publicKey: uint8ArrayToBase64(publicKey),
      signature: uint8ArrayToBase64(signatureBytes),
      signedAt: new Date().toISOString(),
      version: '1.0',
    },
  };
}

function base64ToUint8Array(base64: string): Uint8Array {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes;
}

function uint8ArrayToBase64(bytes: Uint8Array): string {
  let binary = '';
  for (let i = 0; i < bytes.length; i++) {
    binary += String.fromCharCode(bytes[i]);
  }
  return btoa(binary);
}

function createCanonicalJson(obj: unknown): string {
  return JSON.stringify(obj, (_, value) => {
    if (value && typeof value === 'object' && !Array.isArray(value)) {
      const sorted: Record<string, unknown> = {};
      for (const key of Object.keys(value).sort()) {
        sorted[key] = value[key];
      }
      return sorted;
    }
    return value;
  });
}

// Official private key for testing (this is the key generated for testing purposes)
// In production, this would NEVER be in the codebase
const TEST_PRIVATE_KEY = 'gt0SdUQuTv6XFIR61+wMQ2BKDacdeNHRaEyw+k9yI0TGYJZd9ErDsNAu7JB2pAgmUBv6vRqulS7ahWNN0mC/+Q==';

// ============================================================================
// Tests
// ============================================================================

describe('Template Signature Verification', () => {
  describe('verifyTemplate', () => {
    it('should verify an officially signed template', async () => {
      // Create a properly signed template
      const templateData = {
        name: 'Official Test Template',
        version: '1.0.0',
        layers: [
          { id: 'bg', name: 'Background', type: 'solid' },
        ],
      };

      const signedTemplate = await createSignedTemplate(templateData, TEST_PRIVATE_KEY);
      const result = await verifyTemplate(signedTemplate);

      expect(result.isSigned).toBe(true);
      expect(result.isValid).toBe(true);
      expect(result.isOfficial).toBe(true);
      expect(result.status).toBe('official');
      expect(result.message).toContain('Verified official');
    });

    it('should reject a tampered template', async () => {
      // Create a signed template then modify it
      const templateData = {
        name: 'Original Template',
        layers: [],
      };

      const signedTemplate = await createSignedTemplate(templateData, TEST_PRIVATE_KEY);

      // Tamper with the template after signing
      const tamperedTemplate = {
        ...signedTemplate,
        name: 'TAMPERED - This was modified after signing',
      };

      const result = await verifyTemplate(tamperedTemplate);

      expect(result.isSigned).toBe(true);
      expect(result.isValid).toBe(false);
      expect(result.isOfficial).toBe(false);
      expect(result.status).toBe('third-party-invalid');
      expect(result.message).toContain('invalid');
    });

    it('should identify unsigned templates', async () => {
      const result = await verifyTemplate(UNSIGNED_TEMPLATE);

      expect(result.isSigned).toBe(false);
      expect(result.isValid).toBe(false);
      expect(result.isOfficial).toBe(false);
      expect(result.status).toBe('unsigned');
    });

    it('should handle invalid input gracefully', async () => {
      const result1 = await verifyTemplate(null);
      expect(result1.status).toBe('unsigned');

      const result2 = await verifyTemplate('not an object');
      expect(result2.status).toBe('unsigned');

      const result3 = await verifyTemplate({ _signature: 'invalid' });
      expect(result3.status).toBe('third-party-invalid');
    });

    it('should reject unsupported signature versions', async () => {
      const templateWithBadVersion = {
        name: 'Test',
        _signature: {
          algorithm: 'Ed25519',
          publicKey: 'xmCWXfRKw7DQLuyQdqQIJlAb+r0arpUu2oVjTdJgv/k=',
          signature: 'AAAA',
          signedAt: '2024-01-01T00:00:00.000Z',
          version: '99.0', // Unsupported version
        },
      };

      const result = await verifyTemplate(templateWithBadVersion);
      expect(result.isValid).toBe(false);
      expect(result.message).toContain('Unsupported signature version');
    });
  });

  describe('isOfficialTemplate', () => {
    it('should return true for officially signed templates', async () => {
      const templateData = { name: 'Test', layers: [] };
      const signedTemplate = await createSignedTemplate(templateData, TEST_PRIVATE_KEY);

      const isOfficial = await isOfficialTemplate(signedTemplate);
      expect(isOfficial).toBe(true);
    });

    it('should return false for unsigned templates', async () => {
      const isOfficial = await isOfficialTemplate(UNSIGNED_TEMPLATE);
      expect(isOfficial).toBe(false);
    });
  });

  describe('getVerificationBadge', () => {
    it('should return green badge for official templates', () => {
      const result: VerificationResult = {
        isSigned: true,
        isValid: true,
        isOfficial: true,
        status: 'official',
        message: 'Verified',
      };

      const badge = getVerificationBadge(result);
      expect(badge.color).toBe('green');
      expect(badge.label).toContain('Verified');
      expect(badge.icon).toBe('✓');
    });

    it('should return yellow badge for third-party valid', () => {
      const result: VerificationResult = {
        isSigned: true,
        isValid: true,
        isOfficial: false,
        status: 'third-party-valid',
        message: 'Third party',
      };

      const badge = getVerificationBadge(result);
      expect(badge.color).toBe('yellow');
      expect(badge.icon).toBe('⚠');
    });

    it('should return red badge for invalid signatures', () => {
      const result: VerificationResult = {
        isSigned: true,
        isValid: false,
        isOfficial: false,
        status: 'third-party-invalid',
        message: 'Invalid',
      };

      const badge = getVerificationBadge(result);
      expect(badge.color).toBe('red');
      expect(badge.icon).toBe('✗');
    });

    it('should return gray badge for unsigned', () => {
      const result: VerificationResult = {
        isSigned: false,
        isValid: false,
        isOfficial: false,
        status: 'unsigned',
        message: 'Unsigned',
      };

      const badge = getVerificationBadge(result);
      expect(badge.color).toBe('gray');
      expect(badge.icon).toBe('?');
    });
  });

  describe('loadAndVerifyTemplate', () => {
    it('should parse and verify JSON template', async () => {
      const templateData = { name: 'JSON Test', layers: [] };
      const signedTemplate = await createSignedTemplate(templateData, TEST_PRIVATE_KEY);
      const json = JSON.stringify(signedTemplate);

      const { template, verification } = await loadAndVerifyTemplate(json);

      expect(template.name).toBe('JSON Test');
      expect(verification.isOfficial).toBe(true);
      // Signature should be stripped from returned template
      expect(template._signature).toBeUndefined();
    });

    it('should handle invalid JSON gracefully', async () => {
      const { template, verification } = await loadAndVerifyTemplate('not valid json');

      expect(Object.keys(template).length).toBe(0);
      expect(verification.status).toBe('unsigned');
      expect(verification.message).toContain('Failed to parse');
    });
  });

  describe('shouldWarnBeforeLoading', () => {
    it('should not warn for official templates', () => {
      const result: VerificationResult = {
        isSigned: true,
        isValid: true,
        isOfficial: true,
        status: 'official',
        message: 'OK',
      };

      expect(shouldWarnBeforeLoading(result)).toBe(false);
    });

    it('should warn for all non-official templates', () => {
      const statuses: VerificationResult['status'][] = [
        'third-party-valid',
        'third-party-invalid',
        'unsigned',
      ];

      for (const status of statuses) {
        const result: VerificationResult = {
          isSigned: status !== 'unsigned',
          isValid: status === 'third-party-valid',
          isOfficial: false,
          status,
          message: 'Test',
        };

        expect(shouldWarnBeforeLoading(result)).toBe(true);
      }
    });
  });

  describe('Canonical JSON ordering', () => {
    it('should produce same signature regardless of property order', async () => {
      // Two templates with same content but different property order
      const template1 = { a: 1, b: 2, c: { x: 10, y: 20 } };
      const template2 = { c: { y: 20, x: 10 }, b: 2, a: 1 };

      const signed1 = await createSignedTemplate(template1, TEST_PRIVATE_KEY);
      const signed2 = await createSignedTemplate(template2, TEST_PRIVATE_KEY);

      // Signatures should be identical because canonical JSON sorts keys
      expect((signed1._signature as { signature: string }).signature)
        .toBe((signed2._signature as { signature: string }).signature);
    });
  });
});
