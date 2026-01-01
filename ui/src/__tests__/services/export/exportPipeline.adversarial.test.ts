/**
 * Export Pipeline Adversarial Tests
 *
 * These tests are designed to BREAK the export system and verify it fails gracefully.
 * Each test is categorized by severity:
 *
 * CRITICAL: User loses all work, corrupt files, hangs indefinitely
 * HIGH: Export fails with cryptic errors, wrong format, data truncation
 * MEDIUM: Degraded quality, missing frames, incorrect metadata
 * LOW: Progress reporting issues, filename formatting
 *
 * @module ExportPipelineAdversarialTests
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';

// Mock dependencies before importing the module
vi.mock('@/services/comfyui/comfyuiClient', () => ({
  getComfyUIClient: vi.fn(() => ({
    uploadImage: vi.fn().mockRejectedValue(new Error('Upload failed')),
  })),
}));

vi.mock('@/services/layerEvaluationCache', () => ({
  evaluateLayerCached: vi.fn(() => ({
    transform: {
      position: { x: 0, y: 0, z: 0 },
      scale: { x: 100, y: 100 },
      rotation: 0,
      anchorPoint: { x: 0, y: 0 },
    },
    opacity: 100,
  })),
}));

// Import after mocks are set up
import { ExportPipeline, type ExportPipelineOptions } from '@/services/export/exportPipeline';
import type { ExportConfig, ExportTarget } from '@/types/export';
import type { Layer } from '@/types/project';
import type { CameraKeyframe } from '@/types/camera';

// ============================================================================
// Test Fixtures
// ============================================================================

/**
 * Creates a minimal valid ExportConfig for testing
 */
function createValidConfig(overrides: Partial<ExportConfig> = {}): ExportConfig {
  return {
    target: 'wan22-i2v' as ExportTarget,
    width: 512,
    height: 512,
    frameCount: 24,
    fps: 24,
    startFrame: 0,
    endFrame: 24,  // ADV-004/005/019 fix: was missing, caused validation to fail before tests ran
    filenamePrefix: 'export_test',
    depthFormat: 'midas',
    exportReferenceFrame: false,
    exportLastFrame: false,
    exportDepthMap: false,
    exportCameraData: false,
    exportControlImages: false,
    exportSceneVideo: false,
    exportMaskVideo: false,
    comfyuiServer: '',
    autoQueueWorkflow: false,
    outputDir: '/tmp/export',
    prompt: 'test',
    negativePrompt: '',
    ...overrides,
  };
}

/**
 * Creates valid ExportPipelineOptions for testing
 */
function createValidOptions(configOverrides: Partial<ExportConfig> = {}, optionOverrides: Partial<ExportPipelineOptions> = {}): ExportPipelineOptions {
  return {
    layers: [],
    cameraKeyframes: [],
    config: createValidConfig(configOverrides),
    ...optionOverrides,
  };
}

/**
 * Creates a mock layer for testing
 */
function createMockLayer(overrides: Partial<Layer> = {}): Layer {
  return {
    id: 'test-layer',
    name: 'Test Layer',
    type: 'solid',
    visible: true,
    startFrame: 0,
    endFrame: 100,
    inPoint: 0,
    outPoint: 100,
    transform: {
      position: { value: { x: 0, y: 0 }, animated: false },
      scale: { value: { x: 100, y: 100 }, animated: false },
      rotation: { value: 0, animated: false },
      anchorPoint: { value: { x: 0, y: 0 }, animated: false },
    },
    opacity: { value: 100 },
    ...overrides,
  } as unknown as Layer;
}

/**
 * Mock engine that simulates various failure modes
 */
function createMockEngine(options: {
  captureReturnsNull?: boolean;
  captureThrows?: boolean;
  depthReturnsNull?: boolean;
  renderThrows?: boolean;
} = {}) {
  return {
    setFrame: vi.fn(),
    render: vi.fn(() => {
      if (options.renderThrows) {
        throw new Error('WebGL context lost');
      }
    }),
    captureFrame: vi.fn(() => {
      if (options.captureThrows) {
        throw new Error('Frame capture failed');
      }
      if (options.captureReturnsNull) {
        return null;
      }
      return new ImageData(512, 512);
    }),
    captureDepth: vi.fn(() => {
      if (options.depthReturnsNull) {
        return null;
      }
      return {
        depthBuffer: new Float32Array(512 * 512),
        width: 512,
        height: 512,
        minDepth: 0,
        maxDepth: 1000,
      };
    }),
    getState: vi.fn(() => ({ currentFrame: 0 })),
    exportSceneAsVideo: vi.fn().mockResolvedValue({ blob: new Blob(), frames: 24 }),
    exportLayerAsMaskVideo: vi.fn().mockResolvedValue({ blob: new Blob(), frames: 24 }),
  };
}

// ============================================================================
// CRITICAL SEVERITY TESTS
// These would cause users to lose hours of work
// ============================================================================

describe('CRITICAL: Export Pipeline - Config Validation', () => {

  describe('Invalid Dimensions (would corrupt all output)', () => {

    it('should return error for width = 0', async () => {
      const options = createValidOptions({ width: 0 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.length).toBeGreaterThan(0);
      expect(result.errors.some(e => e.toLowerCase().includes('width'))).toBe(true);
    });

    it('should return error for height = 0', async () => {
      const options = createValidOptions({ height: 0 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('height'))).toBe(true);
    });

    it('should return error for negative width', async () => {
      const options = createValidOptions({ width: -100 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('width'))).toBe(true);
    });

    it('should return error for NaN width', async () => {
      const options = createValidOptions({ width: NaN });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('width'))).toBe(true);
    });

    it('should return error for Infinity height', async () => {
      const options = createValidOptions({ height: Infinity });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('height'))).toBe(true);
    });

    it('should return error for dimensions exceeding 4096 (max in validator)', async () => {
      const options = createValidOptions({ width: 8192, height: 8192 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('width') || e.toLowerCase().includes('4096'))).toBe(true);
    });
  });

  describe('Invalid Frame Settings (would export nothing or hang)', () => {

    it('should return error for frameCount = 0', async () => {
      const options = createValidOptions({ frameCount: 0 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('frame'))).toBe(true);
    });

    it('should return error for negative frameCount', async () => {
      const options = createValidOptions({ frameCount: -10 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('frame'))).toBe(true);
    });

    it('should return error for frameCount > 1000', async () => {
      const options = createValidOptions({ frameCount: 10000 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('frame'))).toBe(true);
    });

    it('should return error for NaN frameCount', async () => {
      const options = createValidOptions({ frameCount: NaN });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('frame'))).toBe(true);
    });

    it('should return error for negative startFrame', async () => {
      const options = createValidOptions({ startFrame: -10 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('frame') || e.toLowerCase().includes('start'))).toBe(true);
    });
  });

  describe('Invalid FPS (would corrupt video timing)', () => {

    it('should return error for fps = 0', async () => {
      const options = createValidOptions({ fps: 0 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('fps'))).toBe(true);
    });

    it('should return error for negative fps', async () => {
      const options = createValidOptions({ fps: -24 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('fps'))).toBe(true);
    });

    it('should return error for NaN fps', async () => {
      const options = createValidOptions({ fps: NaN });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('fps'))).toBe(true);
    });

    it('should return error for fps > 120', async () => {
      const options = createValidOptions({ fps: 1000 });
      const pipeline = new ExportPipeline(options);
      const result = await pipeline.execute();

      expect(result.success).toBe(false);
      expect(result.errors.some(e => e.toLowerCase().includes('fps'))).toBe(true);
    });
  });
});

describe('CRITICAL: Export Pipeline - Engine Failure Handling', () => {

  it('should handle missing engine for video export gracefully', async () => {
    const options = createValidOptions({
      exportSceneVideo: true,
    });
    // No engine provided
    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should either succeed without video or have a warning/error
    // But should NOT crash
    expect(result).toBeDefined();
  });

  it('should handle engine with captureFrame returning null', async () => {
    const options = createValidOptions({
      exportReferenceFrame: true,
    }, {
      engine: createMockEngine({ captureReturnsNull: true }) as any,
    });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should handle gracefully (either error or warning)
    expect(result).toBeDefined();
  });

  it('should handle engine with captureFrame throwing', async () => {
    const options = createValidOptions({
      exportReferenceFrame: true,
    }, {
      engine: createMockEngine({ captureThrows: true }) as any,
    });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should handle gracefully
    expect(result).toBeDefined();
  });
});

// ============================================================================
// HIGH SEVERITY TESTS
// Export fails or produces wrong output
// ============================================================================

describe('HIGH: Export Pipeline - Layer Validation', () => {

  it('should handle layer with NaN opacity', async () => {
    const options = createValidOptions({}, {
      layers: [createMockLayer({
        opacity: { value: NaN } as any,
      })],
    });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should not crash - may succeed with default opacity
    expect(result).toBeDefined();
  });

  it('should handle layer with Infinity position', async () => {
    const options = createValidOptions({}, {
      layers: [createMockLayer({
        transform: {
          position: { value: { x: Infinity, y: -Infinity } },
          scale: { value: { x: 100, y: 100 } },
          rotation: { value: 0 },
          anchorPoint: { value: { x: 0, y: 0 } },
        } as any,
      })],
    });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    expect(result).toBeDefined();
  });

  it('should handle empty layers array', async () => {
    const options = createValidOptions({}, { layers: [] });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Empty layers should be valid
    expect(result).toBeDefined();
  });

  it('should handle null layers', async () => {
    const options = createValidOptions({}, { layers: null as any });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should handle gracefully
    expect(result).toBeDefined();
  });
});

// ============================================================================
// MEDIUM SEVERITY TESTS
// Degraded output but still usable
// ============================================================================

describe('MEDIUM: Export Pipeline - Quality Edge Cases', () => {

  it('should handle fractional dimensions (rounds to integer)', async () => {
    const options = createValidOptions({
      width: 512.7,
      height: 384.3,
    } as any);

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should either round or reject with error
    expect(result).toBeDefined();
  });

  it('should handle minimum valid dimensions (64x64)', async () => {
    // Use controlnet-depth which doesn't require reference image
    const options = createValidOptions({
      width: 64,
      height: 64,
      target: 'controlnet-depth' as ExportTarget,
    });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should pass validation - no dimension-related errors
    const dimensionErrors = result.errors.filter(e =>
      e.toLowerCase().includes('width') || e.toLowerCase().includes('height') || e.toLowerCase().includes('dimension')
    );
    expect(dimensionErrors).toHaveLength(0);
  });

  it('should handle maximum valid dimensions (4096x4096)', async () => {
    // Use controlnet-depth which doesn't require reference image
    const options = createValidOptions({
      width: 4096,
      height: 4096,
      target: 'controlnet-depth' as ExportTarget,
    });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should pass validation - no dimension-related errors
    const dimensionErrors = result.errors.filter(e =>
      e.toLowerCase().includes('width') || e.toLowerCase().includes('height') || e.toLowerCase().includes('dimension')
    );
    expect(dimensionErrors).toHaveLength(0);
  });
});

// ============================================================================
// EDGE CASE TESTS
// Unusual but valid inputs
// ============================================================================

describe('EDGE CASES: Export Pipeline - Boundary Conditions', () => {

  it('should handle single frame export (frameCount = 1)', async () => {
    // Use controlnet-depth and fix endFrame to match frameCount
    const options = createValidOptions({
      frameCount: 1,
      startFrame: 0,
      endFrame: 1,  // Must be > startFrame and <= frameCount
      target: 'controlnet-depth' as ExportTarget,
    });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should pass validation - no frame-related errors
    const frameErrors = result.errors.filter(e =>
      e.toLowerCase().includes('frame')
    );
    expect(frameErrors).toHaveLength(0);
  });

  it('should handle empty camera keyframes', async () => {
    const options = createValidOptions({
      exportCameraData: true,
    }, {
      cameraKeyframes: [],
    });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    // Should handle gracefully
    expect(result).toBeDefined();
  });

  it('should handle abort signal', async () => {
    const abortController = new AbortController();
    // Use controlnet-depth which doesn't require reference image
    const options = createValidOptions({
      target: 'controlnet-depth' as ExportTarget,
    }, {
      abortSignal: abortController.signal,
    });

    const pipeline = new ExportPipeline(options);

    // Abort immediately
    abortController.abort();

    const result = await pipeline.execute();

    // Should be aborted - error message is "Export was cancelled" (not "abort")
    expect(result.success).toBe(false);
    expect(result.errors.some(e =>
      e.toLowerCase().includes('abort') || e.toLowerCase().includes('cancel')
    )).toBe(true);
  });
});

// ============================================================================
// MULTIPLE ERROR ACCUMULATION
// ============================================================================

describe('MULTIPLE ERRORS: Export Pipeline - Error Accumulation', () => {

  it('should report multiple validation errors at once', async () => {
    const options = createValidOptions({
      width: -100,
      height: 0,
      frameCount: -5,
      fps: 0,
    });

    const pipeline = new ExportPipeline(options);
    const result = await pipeline.execute();

    expect(result.success).toBe(false);
    // Should have multiple errors, not just the first one
    expect(result.errors.length).toBeGreaterThan(1);
  });
});
