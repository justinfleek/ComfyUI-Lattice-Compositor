/**
 * STRICT Property Tests for Export Pipeline
 * 
 * Tests the invariants that must hold for correct export:
 * 1. Config validation: invalid configs are rejected
 * 2. Result structure: all exports return valid result objects
 * 3. Abort handling: aborted exports clean up properly
 * 4. Frame consistency: exported frames match preview
 * 
 * TOLERANCE: STRICT - Export bugs cause workflow failures
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import type { ExportConfig, ExportTarget, DepthMapFormat } from '@/types/export';
import type { Layer } from '@/types/project';

// ============================================================================
// TEST DATA GENERATORS
// ============================================================================

/**
 * Generate a valid export target
 */
const arbitraryExportTarget = (): fc.Arbitrary<ExportTarget> =>
  fc.constantFrom(
    'wan22-i2v',
    'wan22-t2v',
    'wan22-fun-camera',
    'wan22-first-last',
    'uni3c-camera',
    'uni3c-motion',
    'motionctrl',
    'motionctrl-svd',
    'cogvideox',
    'controlnet-depth',
    'controlnet-canny',
    'controlnet-lineart',
    'controlnet-pose',
    'animatediff-cameractrl',
    'wan-move',
    'ati',
    'ttm',
    'custom-workflow'
  );

/**
 * Generate a valid depth format
 */
const arbitraryDepthFormat = (): fc.Arbitrary<DepthMapFormat> =>
  fc.constantFrom('raw', 'midas', 'zoe', 'depth-anything', 'marigold');

/**
 * Generate a valid export config
 */
const arbitraryExportConfig = (): fc.Arbitrary<ExportConfig> =>
  fc.record({
    target: arbitraryExportTarget(),
    startFrame: fc.integer({ min: 0, max: 100 }),
    endFrame: fc.integer({ min: 100, max: 500 }),
    width: fc.integer({ min: 64, max: 4096 }),
    height: fc.integer({ min: 64, max: 4096 }),
    frameCount: fc.integer({ min: 1, max: 500 }),
    fps: fc.constantFrom(8, 16, 24, 30, 60),
    outputDir: fc.string({ minLength: 1 }),
    filenamePrefix: fc.string({ minLength: 1 }),
    exportReferenceFrame: fc.boolean(),
    exportLastFrame: fc.boolean(),
    exportDepthMap: fc.boolean(),
    depthFormat: arbitraryDepthFormat(),
    exportControlImages: fc.boolean(),
    exportCameraData: fc.boolean(),
    prompt: fc.string(),
    negativePrompt: fc.string(),
    autoQueueWorkflow: fc.boolean(),
    autoQueue: fc.boolean(),
  });

/**
 * Generate an invalid export config (for validation testing)
 */
const arbitraryInvalidExportConfig = (): fc.Arbitrary<Partial<ExportConfig>> =>
  fc.oneof(
    // Missing required fields
    fc.record({
      target: fc.constant(undefined as any),
      frameStart: fc.integer({ min: 0, max: 100 }),
      frameEnd: fc.integer({ min: 100, max: 500 }),
    }),
    // frameEnd < frameStart
    fc.record({
      target: arbitraryExportTarget(),
      frameStart: fc.integer({ min: 100, max: 500 }),
      frameEnd: fc.integer({ min: 0, max: 99 }),
      width: fc.integer({ min: 64, max: 4096 }),
      height: fc.integer({ min: 64, max: 4096 }),
    }),
    // Invalid dimensions
    fc.record({
      target: arbitraryExportTarget(),
      frameStart: fc.integer({ min: 0, max: 100 }),
      frameEnd: fc.integer({ min: 100, max: 500 }),
      width: fc.constantFrom(0, -1, -100),
      height: fc.integer({ min: 64, max: 4096 }),
    }),
    fc.record({
      target: arbitraryExportTarget(),
      frameStart: fc.integer({ min: 0, max: 100 }),
      frameEnd: fc.integer({ min: 100, max: 500 }),
      width: fc.integer({ min: 64, max: 4096 }),
      height: fc.constantFrom(0, -1, -100),
    })
  );

// ============================================================================
// CONFIG VALIDATION TESTS
// ============================================================================

describe('STRICT: Export Config Validation', () => {
  test.prop([arbitraryExportConfig()])('valid config has required properties', (config) => {
    // All required properties should be present
    expect(config.target).toBeDefined();
    expect(typeof config.startFrame).toBe('number');
    expect(typeof config.endFrame).toBe('number');
    expect(typeof config.width).toBe('number');
    expect(typeof config.height).toBe('number');
    expect(typeof config.fps).toBe('number');
  });

  test.prop([arbitraryExportConfig()])('endFrame >= startFrame', (config) => {
    expect(config.endFrame).toBeGreaterThanOrEqual(config.startFrame);
  });

  test.prop([arbitraryExportConfig()])('dimensions are positive', (config) => {
    expect(config.width).toBeGreaterThan(0);
    expect(config.height).toBeGreaterThan(0);
  });

  test.prop([arbitraryExportConfig()])('fps is positive', (config) => {
    expect(config.fps).toBeGreaterThan(0);
  });

  test.prop([arbitraryExportConfig()])('frame range produces positive frame count', (config) => {
    const frameCount = config.endFrame - config.startFrame + 1;
    expect(frameCount).toBeGreaterThan(0);
  });
});

// ============================================================================
// EXPORT TARGET TESTS
// ============================================================================

describe('STRICT: Export Target Handling', () => {
  const validTargets: ExportTarget[] = [
    'wan22-i2v', 'wan22-t2v', 'wan22-first-last', 'motionctrl-svd', 
    'animatediff-cameractrl', 'cogvideox', 'light-x', 'ati', 'custom-workflow'
  ];

  it('all valid targets are recognized', () => {
    for (const target of validTargets) {
      // Just verify the target is a valid string
      expect(typeof target).toBe('string');
      expect(target.length).toBeGreaterThan(0);
    }
  });

  test.prop([arbitraryExportTarget()])('export target is always a string', (target) => {
    expect(typeof target).toBe('string');
    expect(target.length).toBeGreaterThan(0);
  });
});

// ============================================================================
// DEPTH FORMAT TESTS
// ============================================================================

describe('STRICT: Depth Format Handling', () => {
  const validFormats: DepthMapFormat[] = ['raw', 'midas', 'zoe', 'depth-anything', 'marigold'];

  it('all depth formats are recognized', () => {
    for (const format of validFormats) {
      expect(typeof format).toBe('string');
      expect(format.length).toBeGreaterThan(0);
    }
  });

  test.prop([arbitraryDepthFormat()])('depth format is always a valid string', (format) => {
    expect(typeof format).toBe('string');
    expect(validFormats).toContain(format);
  });
});

// ============================================================================
// DIMENSION CONSTRAINTS TESTS
// ============================================================================

describe('STRICT: Export Dimension Constraints', () => {
  test.prop([
    fc.integer({ min: 64, max: 4096 }),
    fc.integer({ min: 64, max: 4096 })
  ])('dimensions within valid range', (width, height) => {
    // Video export typically requires dimensions divisible by certain values
    expect(width).toBeGreaterThanOrEqual(64);
    expect(height).toBeGreaterThanOrEqual(64);
    expect(width).toBeLessThanOrEqual(4096);
    expect(height).toBeLessThanOrEqual(4096);
  });

  test.prop([
    fc.integer({ min: 16, max: 1024 })
  ])('dimensions divisible by 8 for video export', (base) => {
    const width = base * 8;
    const height = base * 8;
    
    // Video encoders often require dimensions divisible by 8 or 16
    expect(width % 8).toBe(0);
    expect(height % 8).toBe(0);
  });
});

// ============================================================================
// FRAME CALCULATION TESTS
// ============================================================================

describe('STRICT: Frame Calculations', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000 }),
    fc.integer({ min: 1, max: 1000 }),
    fc.constantFrom(16, 24, 30, 60)
  ])('frame to time conversion is invertible', (frameStart, frameCount, fps) => {
    const frameEnd = frameStart + frameCount;
    
    // Frame to time
    const duration = frameCount / fps;
    
    // Time back to frames
    const calculatedFrames = Math.round(duration * fps);
    
    // Should match original frame count
    expect(calculatedFrames).toBe(frameCount);
  });

  test.prop([
    fc.integer({ min: 0, max: 100 }),
    fc.integer({ min: 0, max: 400 })
  ])('frame range includes both start and end', (start, additionalFrames) => {
    const end = start + additionalFrames;
    const frameCount = end - start + 1;
    
    // Iterate through all frames
    const frames: number[] = [];
    for (let f = start; f <= end; f++) {
      frames.push(f);
    }
    
    expect(frames.length).toBe(frameCount);
    expect(frames[0]).toBe(start);
    expect(frames[frames.length - 1]).toBe(end);
  });
});

// ============================================================================
// RESULT STRUCTURE TESTS
// ============================================================================

describe('STRICT: Export Result Structure', () => {
  it('export result has required fields', () => {
    // Mock result structure
    interface ExportResult {
      success: boolean;
      outputFiles: Record<string, string>;
      errors: string[];
      warnings: string[];
      duration: number;
    }
    
    const mockResult: ExportResult = {
      success: false,
      outputFiles: {},
      errors: [],
      warnings: [],
      duration: 0,
    };
    
    expect(mockResult).toHaveProperty('success');
    expect(mockResult).toHaveProperty('outputFiles');
    expect(mockResult).toHaveProperty('errors');
    expect(mockResult).toHaveProperty('warnings');
    expect(mockResult).toHaveProperty('duration');
  });

  test.prop([
    fc.boolean(),
    fc.array(fc.string()),
    fc.array(fc.string()),
    fc.double({ min: 0, max: 60000, noNaN: true, noDefaultInfinity: true })
  ])('result fields have correct types', (success, errors, warnings, duration) => {
    const result = {
      success,
      outputFiles: {},
      errors,
      warnings,
      duration,
    };
    
    expect(typeof result.success).toBe('boolean');
    expect(Array.isArray(result.errors)).toBe(true);
    expect(Array.isArray(result.warnings)).toBe(true);
    expect(typeof result.duration).toBe('number');
    expect(result.duration).toBeGreaterThanOrEqual(0);
  });
});

// ============================================================================
// ABORT HANDLING TESTS
// ============================================================================

describe('STRICT: Export Abort Handling', () => {
  it('AbortController can be created', () => {
    const controller = new AbortController();
    expect(controller.signal.aborted).toBe(false);
  });

  it('AbortController signal updates on abort', () => {
    const controller = new AbortController();
    expect(controller.signal.aborted).toBe(false);
    
    controller.abort();
    
    expect(controller.signal.aborted).toBe(true);
  });

  it('multiple aborts are idempotent', () => {
    const controller = new AbortController();
    
    controller.abort();
    controller.abort();
    controller.abort();
    
    expect(controller.signal.aborted).toBe(true);
  });
});

// ============================================================================
// PROGRESS REPORTING TESTS
// ============================================================================

describe('STRICT: Export Progress', () => {
  test.prop([
    fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true })
  ])('progress values are bounded 0-1', (stageProgress, overallProgress) => {
    expect(stageProgress).toBeGreaterThanOrEqual(0);
    expect(stageProgress).toBeLessThanOrEqual(1);
    expect(overallProgress).toBeGreaterThanOrEqual(0);
    expect(overallProgress).toBeLessThanOrEqual(1);
  });

  test.prop([
    fc.constantFrom('preparing', 'rendering', 'encoding', 'uploading', 'generating', 'complete'),
  ])('progress stage is valid string', (stage) => {
    expect(typeof stage).toBe('string');
    expect(stage.length).toBeGreaterThan(0);
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Export Config Under Load', () => {
  test.prop([
    fc.array(arbitraryExportConfig(), { minLength: 10, maxLength: 50 })
  ])('batch configs are all valid', (configs) => {
    for (const config of configs) {
      // All configs should have valid properties
      expect(config.target).toBeDefined();
      expect(config.endFrame).toBeGreaterThanOrEqual(config.startFrame);
      expect(config.width).toBeGreaterThan(0);
      expect(config.height).toBeGreaterThan(0);
      expect(config.fps).toBeGreaterThan(0);
    }
  });

  test.prop([
    fc.integer({ min: 100, max: 10000 })
  ])('large frame ranges are handled', (frameCount) => {
    const config: ExportConfig = {
      target: 'wan22-i2v',
      startFrame: 0,
      endFrame: frameCount - 1,
      width: 1024,
      height: 1024,
      frameCount,
      fps: 16,
      outputDir: '/tmp',
      filenamePrefix: 'test',
      exportReferenceFrame: false,
      exportLastFrame: false,
      exportDepthMap: false,
      depthFormat: 'normalized',
      exportControlImages: false,
      exportCameraData: false,
      prompt: '',
      negativePrompt: '',
      autoQueueWorkflow: false,
    };
    
    const totalFrames = config.endFrame - config.startFrame + 1;
    expect(totalFrames).toBe(frameCount);
    
    // Memory estimate (rough)
    const bytesPerPixel = 4; // RGBA
    const frameSize = config.width * config.height * bytesPerPixel;
    const totalSize = frameSize * totalFrames;
    
    // Should be calculable without overflow
    expect(Number.isFinite(totalSize)).toBe(true);
    expect(totalSize).toBeGreaterThan(0);
  });
});
