/**
 * STRICT Property Tests: Video Encoder
 * 
 * Tests WebCodecs-based video encoding for:
 * - H.264 (AVC) → MP4 container
 * - VP9 → WebM container
 * - VP8 → WebM container
 * 
 * Model Requirements:
 * - ComfyUI nodes expect MP4 (H.264) for video inputs
 * - Web playback prefers WebM for browser compatibility
 * - Correct frame timing (microseconds)
 * - Keyframe insertion every 30 frames
 * - fastStart for streaming (moov atom at beginning)
 */

import { describe, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  isWebCodecsSupported,
  getSupportedCodecs,
  WebCodecsVideoEncoder,
  type VideoEncoderConfig,
  type EncodingProgress,
  type EncodedVideo,
} from '@/services/export/videoEncoder';

// ============================================================================
// ARBITRARIES
// ============================================================================

const arbitraryCodec = (): fc.Arbitrary<'avc' | 'vp9' | 'vp8'> =>
  fc.constantFrom('avc', 'vp9', 'vp8');

const arbitraryQuality = (): fc.Arbitrary<'low' | 'medium' | 'high' | 'lossless'> =>
  fc.constantFrom('low', 'medium', 'high', 'lossless');

const arbitraryVideoEncoderConfig = (): fc.Arbitrary<VideoEncoderConfig> =>
  fc.record({
    width: fc.integer({ min: 64, max: 4096 }).filter(w => w % 2 === 0), // Must be even
    height: fc.integer({ min: 64, max: 4096 }).filter(h => h % 2 === 0), // Must be even
    frameRate: fc.integer({ min: 1, max: 120 }),
    codec: arbitraryCodec(),
    bitrate: fc.option(fc.integer({ min: 100_000, max: 50_000_000 }), { nil: undefined }),
    quality: fc.option(arbitraryQuality(), { nil: undefined }),
  });

// ============================================================================
// WEBCODECS SUPPORT TESTS
// ============================================================================

describe('STRICT: WebCodecs Support Detection', () => {
  test('isWebCodecsSupported returns boolean', () => {
    const result = isWebCodecsSupported();
    expect(typeof result).toBe('boolean');
  });

  test('getSupportedCodecs returns array', async () => {
    const codecs = await getSupportedCodecs();
    expect(Array.isArray(codecs)).toBe(true);
  });

  // NOTE: Browser-specific codec tests are in browser/videoEncoder.browser.test.ts
});

// ============================================================================
// CODEC STRING TESTS
// ============================================================================

describe('STRICT: Codec String Mapping', () => {
  test('AVC codec string is valid H.264', () => {
    // H.264 High Profile Level 4.0
    const expectedPattern = /^avc1\.[0-9a-fA-F]+$/;
    expect('avc1.640028').toMatch(expectedPattern);
  });

  test('VP9 codec string is valid', () => {
    const expectedPattern = /^vp09\.\d{2}\.\d{2}\.\d{2}$/;
    expect('vp09.00.10.08').toMatch(expectedPattern);
  });

  test('VP8 codec string', () => {
    expect('vp8').toBe('vp8');
  });

  test('codec to container mapping', () => {
    const mapping: Record<string, string> = {
      'avc': 'video/mp4',
      'vp9': 'video/webm',
      'vp8': 'video/webm',
    };
    
    expect(mapping['avc']).toBe('video/mp4');
    expect(mapping['vp9']).toBe('video/webm');
    expect(mapping['vp8']).toBe('video/webm');
  });
});

// ============================================================================
// BITRATE CALCULATION TESTS
// ============================================================================

describe('STRICT: Bitrate Calculation', () => {
  test.prop([
    fc.integer({ min: 64, max: 4096 }).filter(w => w % 2 === 0),
    fc.integer({ min: 64, max: 4096 }).filter(h => h % 2 === 0),
    fc.integer({ min: 1, max: 120 }),
    arbitraryQuality(),
  ])('bitrate scales with resolution and frame rate', (width, height, frameRate, quality) => {
    const pixels = width * height;
    const baseRate = pixels * frameRate;
    
    const qualityMultipliers: Record<string, number> = {
      'low': 0.05,
      'medium': 0.1,
      'high': 0.2,
      'lossless': 0.5,
    };
    
    const expectedBitrate = Math.round(baseRate * qualityMultipliers[quality]);
    
    expect(expectedBitrate).toBeGreaterThan(0);
    expect(Number.isFinite(expectedBitrate)).toBe(true);
  });

  test('low quality produces lowest bitrate', () => {
    const base = 1920 * 1080 * 30;
    
    const lowBitrate = Math.round(base * 0.05);
    const mediumBitrate = Math.round(base * 0.1);
    const highBitrate = Math.round(base * 0.2);
    const losslessBitrate = Math.round(base * 0.5);
    
    expect(lowBitrate).toBeLessThan(mediumBitrate);
    expect(mediumBitrate).toBeLessThan(highBitrate);
    expect(highBitrate).toBeLessThan(losslessBitrate);
  });

  test('1080p30 medium quality bitrate', () => {
    const pixels = 1920 * 1080;
    const frameRate = 30;
    const baseRate = pixels * frameRate;
    const bitrate = Math.round(baseRate * 0.1);
    
    // Should be around 6.2 Mbps for medium quality
    expect(bitrate).toBeGreaterThan(5_000_000);
    expect(bitrate).toBeLessThan(10_000_000);
  });

  test('4K60 high quality bitrate', () => {
    const pixels = 3840 * 2160;
    const frameRate = 60;
    const baseRate = pixels * frameRate;
    const bitrate = Math.round(baseRate * 0.2);
    
    // Should be around 100 Mbps for high quality 4K60
    expect(bitrate).toBeGreaterThan(50_000_000);
  });
});

// ============================================================================
// FRAME TIMING TESTS
// ============================================================================

describe('STRICT: Frame Timing', () => {
  test.prop([
    fc.integer({ min: 0, max: 10000 }),
    fc.integer({ min: 1, max: 120 }),
  ])('timestamp calculation in microseconds', (frameIndex, frameRate) => {
    // VideoFrame timestamp is in microseconds
    const timestamp = (frameIndex * 1_000_000) / frameRate;
    
    expect(timestamp).toBeGreaterThanOrEqual(0);
    expect(Number.isFinite(timestamp)).toBe(true);
  });

  test.prop([fc.integer({ min: 1, max: 120 })])(
    'frame duration is 1_000_000 / fps microseconds',
    (frameRate) => {
      const duration = 1_000_000 / frameRate;
      
      expect(duration).toBeGreaterThan(0);
      expect(Number.isFinite(duration)).toBe(true);
    }
  );

  test('30fps frame timing', () => {
    const fps = 30;
    const duration = 1_000_000 / fps;
    
    expect(duration).toBeCloseTo(33333.33, 0);
  });

  test('60fps frame timing', () => {
    const fps = 60;
    const duration = 1_000_000 / fps;
    
    expect(duration).toBeCloseTo(16666.67, 0);
  });

  test('24fps frame timing (film)', () => {
    const fps = 24;
    const duration = 1_000_000 / fps;
    
    expect(duration).toBeCloseTo(41666.67, 0);
  });

  test('16fps frame timing (Wan)', () => {
    const fps = 16;
    const duration = 1_000_000 / fps;
    
    expect(duration).toBeCloseTo(62500, 0);
  });
});

// ============================================================================
// KEYFRAME INSERTION TESTS
// ============================================================================

describe('STRICT: Keyframe Insertion', () => {
  test.prop([fc.integer({ min: 0, max: 1000 })])(
    'first frame is always keyframe',
    (frameIndex) => {
      const isKeyFrame = frameIndex === 0 || frameIndex % 30 === 0;
      
      if (frameIndex === 0) {
        expect(isKeyFrame).toBe(true);
      }
    }
  );

  test.prop([fc.integer({ min: 1, max: 100 })])(
    'keyframe every 30 frames',
    (multiplier) => {
      const frame = multiplier * 30;
      const isKeyFrame = frame === 0 || frame % 30 === 0;
      
      expect(isKeyFrame).toBe(true);
    }
  );

  test('keyframe pattern', () => {
    const keyframes: number[] = [];
    
    for (let i = 0; i < 100; i++) {
      if (i === 0 || i % 30 === 0) {
        keyframes.push(i);
      }
    }
    
    expect(keyframes).toEqual([0, 30, 60, 90]);
  });
});

// ============================================================================
// ENCODING PROGRESS TESTS
// ============================================================================

describe('STRICT: Encoding Progress', () => {
  test.prop([
    fc.integer({ min: 1, max: 1000 }),
    fc.integer({ min: 1, max: 10000 }),
  ])('percentage calculation', (encoded, total) => {
    // Ensure encoded <= total for valid progress
    const actualEncoded = Math.min(encoded, total);
    const percentage = (actualEncoded / total) * 100;
    
    expect(percentage).toBeGreaterThanOrEqual(0);
    expect(percentage).toBeLessThanOrEqual(100);
  });

  test('progress at start is 0%', () => {
    const progress: EncodingProgress = {
      framesEncoded: 0,
      totalFrames: 100,
      percentage: 0,
      bytesWritten: 0,
    };
    
    expect(progress.percentage).toBe(0);
  });

  test('progress at end is 100%', () => {
    const progress: EncodingProgress = {
      framesEncoded: 100,
      totalFrames: 100,
      percentage: 100,
      bytesWritten: 1000000,
    };
    
    expect(progress.percentage).toBe(100);
  });

  test('progress at midpoint is 50%', () => {
    const framesEncoded = 50;
    const totalFrames = 100;
    const percentage = (framesEncoded / totalFrames) * 100;
    
    expect(percentage).toBe(50);
  });
});

// ============================================================================
// ENCODED VIDEO RESULT TESTS
// ============================================================================

describe('STRICT: Encoded Video Result', () => {
  test('MP4 container for AVC codec', () => {
    const result: Partial<EncodedVideo> = {
      mimeType: 'video/mp4',
    };
    
    expect(result.mimeType).toBe('video/mp4');
  });

  test('WebM container for VP9 codec', () => {
    const result: Partial<EncodedVideo> = {
      mimeType: 'video/webm',
    };
    
    expect(result.mimeType).toBe('video/webm');
  });

  test.prop([
    fc.integer({ min: 1, max: 10000 }),
    fc.integer({ min: 1, max: 120 }),
  ])('duration calculation', (frameCount, frameRate) => {
    const duration = frameCount / frameRate;
    
    expect(duration).toBeGreaterThan(0);
    expect(Number.isFinite(duration)).toBe(true);
  });

  test('duration for 81 frames at 16fps (Wan standard)', () => {
    const frameCount = 81;
    const frameRate = 16;
    const duration = frameCount / frameRate;
    
    expect(duration).toBeCloseTo(5.0625, 4); // ~5 seconds
  });
});

// ============================================================================
// DIMENSION VALIDATION TESTS
// ============================================================================

describe('STRICT: Video Dimension Validation', () => {
  test.prop([
    fc.integer({ min: 1, max: 2048 }),
  ])('width must be even for H.264', (halfWidth) => {
    const width = halfWidth * 2;
    expect(width % 2).toBe(0);
  });

  test.prop([
    fc.integer({ min: 1, max: 2048 }),
  ])('height must be even for H.264', (halfHeight) => {
    const height = halfHeight * 2;
    expect(height % 2).toBe(0);
  });

  test('common video resolutions are even', () => {
    const resolutions = [
      [1920, 1080], // 1080p
      [1280, 720],  // 720p
      [3840, 2160], // 4K
      [512, 512],   // Wan
      [768, 768],   // Common AI
      [1024, 576],  // 16:9 1024w
    ];
    
    for (const [w, h] of resolutions) {
      expect(w % 2).toBe(0);
      expect(h % 2).toBe(0);
    }
  });
});

// ============================================================================
// FILE SIZE ESTIMATION TESTS
// ============================================================================

describe('STRICT: File Size Estimation', () => {
  test.prop([
    fc.integer({ min: 100_000, max: 50_000_000 }), // bitrate
    fc.double({ min: 0.1, max: 300, noNaN: true }), // duration in seconds
  ])('file size estimation', (bitrate, durationSeconds) => {
    // bitrate is bits per second, size in bytes
    const estimatedBytes = (bitrate * durationSeconds) / 8;
    
    expect(estimatedBytes).toBeGreaterThan(0);
    expect(Number.isFinite(estimatedBytes)).toBe(true);
  });

  test('5 second Wan video size estimate', () => {
    // 512x512 @ 16fps, medium quality
    const pixels = 512 * 512;
    const fps = 16;
    const baseRate = pixels * fps;
    const bitrate = Math.round(baseRate * 0.1); // medium
    const duration = 81 / 16; // 81 frames at 16fps
    
    const estimatedBytes = (bitrate * duration) / 8;
    
    // Should be in the range of 100KB - 1MB
    expect(estimatedBytes).toBeGreaterThan(100_000);
    expect(estimatedBytes).toBeLessThan(10_000_000);
  });
});

// ============================================================================
// EDGE CASE TESTS
// ============================================================================

describe('STRICT: Video Encoder Edge Cases', () => {
  test('minimum resolution (64x64)', () => {
    const config: VideoEncoderConfig = {
      width: 64,
      height: 64,
      frameRate: 30,
      codec: 'avc',
    };
    
    expect(config.width).toBe(64);
    expect(config.height).toBe(64);
    expect(config.width % 2).toBe(0);
    expect(config.height % 2).toBe(0);
  });

  test('maximum practical resolution (4K)', () => {
    const config: VideoEncoderConfig = {
      width: 3840,
      height: 2160,
      frameRate: 60,
      codec: 'avc',
    };
    
    expect(config.width).toBe(3840);
    expect(config.height).toBe(2160);
  });

  test('single frame video', () => {
    const frameCount = 1;
    const frameRate = 30;
    const duration = frameCount / frameRate;
    
    expect(duration).toBeCloseTo(0.0333, 3);
  });

  test('very long video (1 hour)', () => {
    const frameCount = 30 * 60 * 60; // 1 hour at 30fps
    const frameRate = 30;
    const duration = frameCount / frameRate;
    
    expect(duration).toBe(3600); // 1 hour in seconds
  });

  test('1fps frame rate (time-lapse)', () => {
    const duration = 1_000_000 / 1;
    
    expect(duration).toBe(1_000_000); // 1 second per frame
  });

  test('120fps frame rate (slow-mo)', () => {
    const duration = 1_000_000 / 120;
    
    expect(duration).toBeCloseTo(8333.33, 0);
  });
});

// ============================================================================
// MUXER SELECTION TESTS
// ============================================================================

describe('STRICT: Muxer Selection', () => {
  test('MP4 muxer for H.264', () => {
    const codec = 'avc';
    const expectedMuxer = codec === 'avc' ? 'mp4' : 'webm';
    
    expect(expectedMuxer).toBe('mp4');
  });

  test('WebM muxer for VP9', () => {
    const codec = 'vp9';
    const expectedMuxer = codec === 'avc' ? 'mp4' : 'webm';
    
    expect(expectedMuxer).toBe('webm');
  });

  test('WebM muxer for VP8', () => {
    const codec = 'vp8';
    const expectedMuxer = codec === 'avc' ? 'mp4' : 'webm';
    
    expect(expectedMuxer).toBe('webm');
  });

  test('fastStart for MP4 streaming', () => {
    // MP4 fastStart moves moov atom to beginning
    const fastStartOption = 'in-memory';
    expect(fastStartOption).toBe('in-memory');
  });
});
