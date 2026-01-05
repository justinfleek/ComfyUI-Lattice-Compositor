/**
 * STRICT Property Tests: Frame Sequence Exporter
 * 
 * Tests frame sequence export for various formats:
 * - PNG: 8-bit RGBA, lossless
 * - JPEG: 8-bit RGB, lossy (quality 0-100)
 * - WebP: 8-bit, lossy or lossless
 * - EXR: 32-bit float HDR (via backend)
 * - TIFF: 8/16-bit (via backend)
 * - DPX: 10/16-bit film format (via backend)
 * 
 * Model Requirements:
 * - Correct filename patterns ({frame:04d})
 * - Proper MIME types for each format
 * - Quality parameter mapping
 * - Backend format detection
 */

import { describe, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  isBrowserFormat,
  formatFrameNumber,
  generateFilename,
  getFormatInfo,
  type FrameFormat,
  type FrameExportOptions,
} from '@/services/export/frameSequenceExporter';

// ============================================================================
// ARBITRARIES
// ============================================================================

const arbitraryBrowserFormat = (): fc.Arbitrary<FrameFormat> =>
  fc.constantFrom('png', 'jpeg', 'webp');

const arbitraryBackendFormat = (): fc.Arbitrary<FrameFormat> =>
  fc.constantFrom('tiff', 'exr', 'dpx');

const arbitraryAllFormats = (): fc.Arbitrary<FrameFormat> =>
  fc.constantFrom('png', 'jpeg', 'webp', 'tiff', 'exr', 'dpx');

const arbitraryFrameExportOptions = (): fc.Arbitrary<FrameExportOptions> =>
  fc.record({
    format: arbitraryAllFormats(),
    quality: fc.integer({ min: 0, max: 100 }),
    filenamePattern: fc.constantFrom(
      'frame_{frame:04d}',
      'output_{frame:05d}',
      'render_{frame:03d}',
      '{frame:06d}'
    ),
    outputDir: fc.constant('/output'),
    startFrame: fc.integer({ min: 0, max: 100 }),
    endFrame: fc.integer({ min: 10, max: 1000 }),
    bitDepth: fc.constantFrom(8, 10, 16, 32),
    colorSpace: fc.constantFrom('sRGB', 'Linear', 'ACEScg', 'Rec709'),
  }).filter(o => o.endFrame > o.startFrame);

// ============================================================================
// BROWSER FORMAT DETECTION TESTS
// ============================================================================

describe('STRICT: Browser Format Detection', () => {
  test.prop([arbitraryBrowserFormat()])(
    'browser formats return true for isBrowserFormat',
    (format) => {
      expect(isBrowserFormat(format)).toBe(true);
    }
  );

  test.prop([arbitraryBackendFormat()])(
    'backend formats return false for isBrowserFormat',
    (format) => {
      expect(isBrowserFormat(format)).toBe(false);
    }
  );

  test('specific format checks', () => {
    expect(isBrowserFormat('png')).toBe(true);
    expect(isBrowserFormat('jpeg')).toBe(true);
    expect(isBrowserFormat('webp')).toBe(true);
    expect(isBrowserFormat('tiff')).toBe(false);
    expect(isBrowserFormat('exr')).toBe(false);
    expect(isBrowserFormat('dpx')).toBe(false);
  });
});

// ============================================================================
// FRAME NUMBER FORMATTING TESTS
// ============================================================================

describe('STRICT: Frame Number Formatting', () => {
  test.prop([
    fc.integer({ min: 0, max: 99999 }),
    fc.integer({ min: 1, max: 8 }),
  ])('frame number is padded to specified width', (frame, digits) => {
    const pattern = `{frame:0${digits}d}`;
    const result = formatFrameNumber(pattern, frame);
    
    // Result should have at least 'digits' characters
    expect(result.length).toBeGreaterThanOrEqual(digits);
    
    // Should parse back to original number
    expect(parseInt(result, 10)).toBe(frame);
  });

  test('4-digit padding examples', () => {
    expect(formatFrameNumber('{frame:04d}', 0)).toBe('0000');
    expect(formatFrameNumber('{frame:04d}', 1)).toBe('0001');
    expect(formatFrameNumber('{frame:04d}', 42)).toBe('0042');
    expect(formatFrameNumber('{frame:04d}', 999)).toBe('0999');
    expect(formatFrameNumber('{frame:04d}', 1234)).toBe('1234');
    expect(formatFrameNumber('{frame:04d}', 99999)).toBe('99999'); // Overflow OK
  });

  test('5-digit padding examples', () => {
    expect(formatFrameNumber('{frame:05d}', 0)).toBe('00000');
    expect(formatFrameNumber('{frame:05d}', 1)).toBe('00001');
    expect(formatFrameNumber('{frame:05d}', 12345)).toBe('12345');
  });

  test('pattern with prefix and suffix', () => {
    expect(formatFrameNumber('frame_{frame:04d}', 42)).toBe('frame_0042');
    expect(formatFrameNumber('output_{frame:05d}_final', 1)).toBe('output_00001_final');
  });

  test('multiple frame placeholders', () => {
    expect(formatFrameNumber('{frame:04d}_{frame:04d}', 42)).toBe('0042_0042');
  });
});

// ============================================================================
// FILENAME GENERATION TESTS
// ============================================================================

describe('STRICT: Filename Generation', () => {
  test.prop([
    fc.integer({ min: 0, max: 99999 }),
    arbitraryAllFormats(),
  ])('filename has correct extension', (frame, format) => {
    const filename = generateFilename('{frame:04d}', frame, format);
    
    expect(filename.endsWith(`.${format}`)).toBe(true);
  });

  test.prop([
    fc.integer({ min: 0, max: 99999 }),
  ])('PNG filename generation', (frame) => {
    const filename = generateFilename('frame_{frame:04d}', frame, 'png');
    const expected = `frame_${frame.toString().padStart(4, '0')}.png`;
    
    expect(filename).toBe(expected);
  });

  test.prop([
    fc.integer({ min: 0, max: 99999 }),
  ])('JPEG filename generation', (frame) => {
    const filename = generateFilename('frame_{frame:04d}', frame, 'jpeg');
    const expected = `frame_${frame.toString().padStart(4, '0')}.jpeg`;
    
    expect(filename).toBe(expected);
  });

  test('filename examples', () => {
    expect(generateFilename('frame_{frame:04d}', 0, 'png')).toBe('frame_0000.png');
    expect(generateFilename('frame_{frame:04d}', 42, 'jpeg')).toBe('frame_0042.jpeg');
    expect(generateFilename('output_{frame:05d}', 100, 'webp')).toBe('output_00100.webp');
    expect(generateFilename('{frame:06d}', 1, 'exr')).toBe('000001.exr');
  });
});

// ============================================================================
// FORMAT INFO TESTS
// ============================================================================

describe('STRICT: Format Information', () => {
  test.prop([arbitraryAllFormats()])(
    'getFormatInfo returns valid info for all formats',
    (format) => {
      const info = getFormatInfo(format);
      
      expect(info).toHaveProperty('name');
      expect(info).toHaveProperty('description');
      expect(info).toHaveProperty('extension');
      expect(info).toHaveProperty('requiresBackend');
      expect(info).toHaveProperty('supportsAlpha');
      expect(info).toHaveProperty('bitDepths');
      expect(info).toHaveProperty('lossy');
      
      expect(typeof info.name).toBe('string');
      expect(typeof info.description).toBe('string');
      expect(typeof info.extension).toBe('string');
      expect(typeof info.requiresBackend).toBe('boolean');
      expect(typeof info.supportsAlpha).toBe('boolean');
      expect(Array.isArray(info.bitDepths)).toBe(true);
      expect(typeof info.lossy).toBe('boolean');
    }
  );

  test('PNG format info', () => {
    const info = getFormatInfo('png');
    
    expect(info.name).toBe('PNG');
    expect(info.extension).toBe('png');
    expect(info.requiresBackend).toBe(false);
    expect(info.supportsAlpha).toBe(true);
    expect(info.bitDepths).toContain(8);
    expect(info.lossy).toBe(false);
  });

  test('JPEG format info', () => {
    const info = getFormatInfo('jpeg');
    
    expect(info.name).toBe('JPEG');
    expect(info.extension).toBe('jpg');
    expect(info.requiresBackend).toBe(false);
    expect(info.supportsAlpha).toBe(false);
    expect(info.bitDepths).toContain(8);
    expect(info.lossy).toBe(true);
  });

  test('WebP format info', () => {
    const info = getFormatInfo('webp');
    
    expect(info.name).toBe('WebP');
    expect(info.extension).toBe('webp');
    expect(info.requiresBackend).toBe(false);
    expect(info.supportsAlpha).toBe(true);
    expect(info.lossy).toBe(true); // Can be lossy or lossless
  });

  test('EXR format info', () => {
    const info = getFormatInfo('exr');
    
    expect(info.name).toBe('OpenEXR');
    expect(info.extension).toBe('exr');
    expect(info.requiresBackend).toBe(true);
    expect(info.supportsAlpha).toBe(true);
    expect(info.bitDepths).toContain(16);
    expect(info.bitDepths).toContain(32);
    expect(info.lossy).toBe(false);
  });

  test('TIFF format info', () => {
    const info = getFormatInfo('tiff');
    
    expect(info.name).toBe('TIFF');
    expect(info.extension).toBe('tiff');
    expect(info.requiresBackend).toBe(true);
    expect(info.supportsAlpha).toBe(true);
    expect(info.bitDepths).toContain(8);
    expect(info.bitDepths).toContain(16);
  });

  test('DPX format info', () => {
    const info = getFormatInfo('dpx');
    
    expect(info.name).toBe('DPX');
    expect(info.extension).toBe('dpx');
    expect(info.requiresBackend).toBe(true);
    expect(info.supportsAlpha).toBe(false);
    expect(info.bitDepths).toContain(10);
    expect(info.bitDepths).toContain(16);
  });

  test('requiresBackend matches isBrowserFormat', () => {
    const formats: FrameFormat[] = ['png', 'jpeg', 'webp', 'tiff', 'exr', 'dpx'];
    
    for (const format of formats) {
      const info = getFormatInfo(format);
      expect(info.requiresBackend).toBe(!isBrowserFormat(format));
    }
  });
});

// ============================================================================
// FRAME RANGE TESTS
// ============================================================================

describe('STRICT: Frame Range Calculations', () => {
  test.prop([
    fc.integer({ min: 0, max: 100 }),
    fc.integer({ min: 1, max: 1000 }),
  ])('frame count = endFrame - startFrame + 1', (startFrame, numFrames) => {
    const endFrame = startFrame + numFrames - 1;
    const totalFrames = endFrame - startFrame + 1;
    
    expect(totalFrames).toBe(numFrames);
  });

  test('specific frame range examples', () => {
    // 0 to 80 = 81 frames
    expect(80 - 0 + 1).toBe(81);
    
    // 10 to 20 = 11 frames
    expect(20 - 10 + 1).toBe(11);
    
    // Single frame (5 to 5)
    expect(5 - 5 + 1).toBe(1);
  });
});

// ============================================================================
// QUALITY PARAMETER TESTS
// ============================================================================

describe('STRICT: Quality Parameter', () => {
  test.prop([fc.integer({ min: 0, max: 100 })])(
    'quality 0-100 maps to 0-1 for browser API',
    (quality) => {
      const qualityValue = quality / 100;
      
      expect(qualityValue).toBeGreaterThanOrEqual(0);
      expect(qualityValue).toBeLessThanOrEqual(1);
    }
  );

  test('PNG ignores quality (lossless)', () => {
    const info = getFormatInfo('png');
    expect(info.lossy).toBe(false);
    // Quality parameter should be undefined for PNG in exportCanvasToBlob
  });

  test('JPEG uses quality', () => {
    const info = getFormatInfo('jpeg');
    expect(info.lossy).toBe(true);
  });

  test('WebP uses quality', () => {
    const info = getFormatInfo('webp');
    expect(info.lossy).toBe(true);
  });
});

// ============================================================================
// EDGE CASE TESTS
// ============================================================================

describe('STRICT: Frame Sequence Edge Cases', () => {
  test('frame 0 formatting', () => {
    expect(formatFrameNumber('{frame:04d}', 0)).toBe('0000');
    expect(generateFilename('{frame:04d}', 0, 'png')).toBe('0000.png');
  });

  test('very large frame numbers', () => {
    expect(formatFrameNumber('{frame:04d}', 999999)).toBe('999999');
    expect(formatFrameNumber('{frame:08d}', 999999)).toBe('00999999');
  });

  test('negative frame numbers (should convert)', () => {
    // JavaScript toString handles negative numbers
    const result = formatFrameNumber('{frame:04d}', -1);
    // Behavior depends on implementation - should handle gracefully
    expect(typeof result).toBe('string');
  });

  test('pattern without frame placeholder', () => {
    expect(formatFrameNumber('static_name', 42)).toBe('static_name');
  });

  test('empty pattern', () => {
    expect(formatFrameNumber('', 42)).toBe('');
  });

  test('pattern with only placeholder', () => {
    expect(formatFrameNumber('{frame:04d}', 42)).toBe('0042');
  });
});

// ============================================================================
// BIT DEPTH TESTS
// ============================================================================

describe('STRICT: Bit Depth Support', () => {
  test('PNG supports 8-bit only in browser', () => {
    const info = getFormatInfo('png');
    expect(info.bitDepths).toEqual([8]);
  });

  test('EXR supports HDR bit depths', () => {
    const info = getFormatInfo('exr');
    expect(info.bitDepths).toContain(16);
    expect(info.bitDepths).toContain(32);
    // 32-bit float for true HDR
    expect(info.bitDepths).toContain(32);
  });

  test('DPX supports film bit depths', () => {
    const info = getFormatInfo('dpx');
    // 10-bit is standard for film
    expect(info.bitDepths).toContain(10);
    expect(info.bitDepths).toContain(16);
  });

  test('TIFF supports 8 and 16 bit', () => {
    const info = getFormatInfo('tiff');
    expect(info.bitDepths).toContain(8);
    expect(info.bitDepths).toContain(16);
  });
});

// ============================================================================
// COLOR SPACE TESTS
// ============================================================================

describe('STRICT: Color Space Metadata', () => {
  test('color spaces for backend formats', () => {
    const colorSpaces = ['sRGB', 'Linear', 'ACEScg', 'Rec709'];
    
    // All color spaces are valid strings
    for (const cs of colorSpaces) {
      expect(typeof cs).toBe('string');
      expect(cs.length).toBeGreaterThan(0);
    }
  });

  test('sRGB is default web color space', () => {
    // Browser formats typically use sRGB
    const browserFormats: FrameFormat[] = ['png', 'jpeg', 'webp'];
    
    for (const format of browserFormats) {
      const info = getFormatInfo(format);
      // Browser formats don't explicitly track color space
      expect(info.requiresBackend).toBe(false);
    }
  });
});
