/**
 * Video Encoder Browser Tests
 * 
 * Tests WebCodecs functionality in real browser environment.
 */

import { describe, expect, test } from 'vitest';
import {
  isWebCodecsSupported,
  getSupportedCodecs,
} from '@/services/export/videoEncoder';

describe('STRICT: WebCodecs Browser Support', () => {
  
  test('isWebCodecsSupported returns boolean', () => {
    const supported = isWebCodecsSupported();
    expect(typeof supported).toBe('boolean');
  });

  test('getSupportedCodecs returns array', async () => {
    const codecs = await getSupportedCodecs();
    expect(Array.isArray(codecs)).toBe(true);
  });

  test('supported codecs include known codecs in browser', async () => {
    const codecs = await getSupportedCodecs();
    
    // In a real browser, at least one codec should be supported
    if (isWebCodecsSupported()) {
      expect(codecs.length).toBeGreaterThan(0);
    }
  });

  test('codec strings are valid', async () => {
    const codecs = await getSupportedCodecs();
    
    for (const codec of codecs) {
      expect(typeof codec).toBe('string');
      expect(codec.length).toBeGreaterThan(0);
    }
  });
});
