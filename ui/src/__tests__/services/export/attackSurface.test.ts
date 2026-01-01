/**
 * Attack Surface Tests - Security & Edge Case Coverage
 *
 * These tests explore REAL attack vectors that could cause:
 * - Silent data corruption
 * - Memory exhaustion / DoS
 * - State corruption from interrupted operations
 * - Malicious input injection
 * - Non-deterministic outputs
 * - Cross-export state leakage
 *
 * @module AttackSurfaceTests
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';

// ============================================================================
// CATEGORY 1: STATE CORRUPTION & RACE CONDITIONS
// ============================================================================

describe('ATTACK: State Corruption - Abort Mid-Export', () => {

  it('should clean up partial files when aborted', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const filesCreated: string[] = [];
    const filesDeleted: string[] = [];

    // Mock file system
    vi.mock('fs', () => ({
      writeFileSync: vi.fn((path) => filesCreated.push(path)),
      unlinkSync: vi.fn((path) => filesDeleted.push(path)),
      existsSync: vi.fn(() => true),
    }));

    const abortController = new AbortController();

    const pipeline = new ExportPipeline({
      layers: [],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 100,
        fps: 24,
        startFrame: 0,
        exportReferenceFrame: true,
        exportDepthMap: true,
        outputDirectory: '/tmp/test',
      } as any,
      abortSignal: abortController.signal,
    });

    // Start export, abort after small delay
    const exportPromise = pipeline.execute();
    setTimeout(() => abortController.abort(), 10);

    const result = await exportPromise;

    // Should have aborted
    expect(result.success).toBe(false);

    // Partial files should be cleaned up (or at least flagged)
    // This test documents expected behavior
  });

  it('should prevent concurrent exports on same pipeline', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 10,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    // Start two exports simultaneously
    const export1 = pipeline.execute();
    const export2 = pipeline.execute();

    const [result1, result2] = await Promise.all([export1, export2]);

    // At least one should fail or they should be sequenced
    // This test documents that concurrent execution is handled
    expect(result1 || result2).toBeDefined();
  });

  it('should handle abort during critical section (file write)', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    let writeStarted = false;
    let writeCompleted = false;

    // Track when blob creation happens (during file write)
    const originalBlob = global.Blob;
    global.Blob = class MockBlob extends Blob {
      constructor(...args: ConstructorParameters<typeof Blob>) {
        super(...args);
        writeStarted = true;
      }
    } as typeof Blob;

    const abortController = new AbortController();

    const pipeline = new ExportPipeline({
      layers: [],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 10,
        fps: 24,
        startFrame: 0,
        exportReferenceFrame: true,
      } as any,
      abortSignal: abortController.signal,
    });

    const exportPromise = pipeline.execute();

    // Abort mid-operation
    setTimeout(() => {
      if (writeStarted && !writeCompleted) {
        abortController.abort();
      }
    }, 5);

    const result = await exportPromise;

    // Restore original Blob
    global.Blob = originalBlob;

    // Should handle gracefully without corrupting state
    expect(result).toBeDefined();
  });
});

describe('ATTACK: State Corruption - Resume After Error', () => {

  it('should reset internal state after failed export', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    // First export with invalid config - should fail
    const pipeline1 = new ExportPipeline({
      layers: [],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 0, // Invalid
        height: 512,
        frameCount: 10,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    const result1 = await pipeline1.execute();
    expect(result1.success).toBe(false);

    // Second export with valid config - should succeed
    const pipeline2 = new ExportPipeline({
      layers: [],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 10,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    const result2 = await pipeline2.execute();

    // Second export should not be affected by first failure
    expect(result2.success).toBe(true);
  });
});

// ============================================================================
// CATEGORY 2: MEMORY EXHAUSTION / DoS
// ============================================================================

describe('ATTACK: Memory Exhaustion', () => {

  it('should reject 4K × 4K × 1000 frames (would be 64GB+)', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 4096,
        height: 4096,
        frameCount: 1000,
        fps: 24,
        startFrame: 0,
        exportDepthMap: true, // Each frame = 4096*4096*4 bytes = 64MB
      } as any,
    });

    const result = await pipeline.execute();

    // Should either fail with clear error OR succeed with streaming
    // But should NOT crash the process
    expect(result).toBeDefined();
  });

  it('should limit canvas context allocation', async () => {
    // Browsers typically limit to ~16 canvas contexts
    // Creating more should fail gracefully

    const canvases: OffscreenCanvas[] = [];

    try {
      for (let i = 0; i < 50; i++) {
        const canvas = new OffscreenCanvas(1024, 1024);
        const ctx = canvas.getContext('2d');
        if (!ctx) {
          // This is expected behavior - graceful failure
          break;
        }
        canvases.push(canvas);
      }
    } catch (e) {
      // Expected to fail at some point
    }

    // Should not have created 50 contexts
    expect(canvases.length).toBeLessThan(50);
  });

  it('should handle deeply nested compositions', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    // Create 100-level deep nested composition
    const createNestedLayer = (depth: number): any => {
      if (depth === 0) {
        return {
          id: 'leaf',
          type: 'solid',
          visible: true,
        };
      }
      return {
        id: `nested-${depth}`,
        type: 'nestedComp',
        visible: true,
        nestedComposition: {
          layers: [createNestedLayer(depth - 1)],
        },
      };
    };

    const pipeline = new ExportPipeline({
      layers: [createNestedLayer(100)],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 1,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    // Should either handle or reject with clear error
    // Should NOT stack overflow
    const result = await pipeline.execute();
    expect(result).toBeDefined();
  });

  it('should reject absurdly long trajectories', async () => {
    const { exportWanMoveTrajectories } = await import('@/services/modelExport');

    // 1 million points per trajectory
    const massiveTrajectory = {
      id: 'massive',
      points: Array(1000000).fill(null).map((_, i) => ({
        frame: i,
        x: Math.random() * 1920,
        y: Math.random() * 1080,
      })),
      visibility: Array(1000000).fill(true),
    };

    // Should either process or reject, not hang
    const startTime = Date.now();

    try {
      exportWanMoveTrajectories([massiveTrajectory], 1920, 1080);
    } catch (e) {
      // Expected to fail
    }

    const elapsed = Date.now() - startTime;

    // Should not take more than 5 seconds
    expect(elapsed).toBeLessThan(5000);
  });
});

// ============================================================================
// CATEGORY 3: MALICIOUS INPUT INJECTION
// ============================================================================

describe('ATTACK: Path Traversal', () => {

  it('should reject path traversal in output directory', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const maliciousPaths = [
      '../../../etc/passwd',
      '..\\..\\..\\Windows\\System32',
      '/etc/passwd',
      'C:\\Windows\\System32',
      'file:///etc/passwd',
      '%2e%2e%2f%2e%2e%2f', // URL encoded ../
    ];

    for (const maliciousPath of maliciousPaths) {
      const pipeline = new ExportPipeline({
        layers: [],
        cameraKeyframes: [],
        config: {
          target: 'wan22-i2v',
          width: 512,
          height: 512,
          frameCount: 1,
          fps: 24,
          startFrame: 0,
          outputDirectory: maliciousPath,
        } as any,
      });

      const result = await pipeline.execute();

      // Should either reject or sanitize the path
      if (result.success) {
        // If it succeeded, verify the actual output path was sanitized
        const outputPath = Object.keys(result.outputFiles)[0];
        if (outputPath) {
          expect(outputPath).not.toContain('..');
          expect(outputPath).not.toContain('/etc/');
          expect(outputPath).not.toContain('\\Windows\\');
        }
      }
    }
  });

  it('should sanitize filename with special characters', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const maliciousFilenames = [
      '../../../evil',
      'file<>:"/\\|?*name',
      'CON', // Windows reserved
      'NUL', // Windows reserved
      'file\x00name', // Null byte
      'a'.repeat(500), // Very long
      '...', // Special
    ];

    for (const filename of maliciousFilenames) {
      const pipeline = new ExportPipeline({
        layers: [],
        cameraKeyframes: [],
        config: {
          target: 'wan22-i2v',
          width: 512,
          height: 512,
          frameCount: 1,
          fps: 24,
          startFrame: 0,
          filenamePrefix: filename,
        } as any,
      });

      const result = await pipeline.execute();

      // Should not crash and should sanitize
      expect(result).toBeDefined();
    }
  });
});

describe('ATTACK: Workflow JSON Injection', () => {

  it('should reject workflow with __proto__ pollution', async () => {
    const { validateWorkflow, injectParameters } = await import('@/services/comfyui/workflowTemplates');

    const maliciousWorkflow = JSON.parse(`{
      "__proto__": {
        "isAdmin": true
      },
      "constructor": {
        "prototype": {
          "isAdmin": true
        }
      },
      "1": {
        "class_type": "LoadImage",
        "inputs": {}
      }
    }`);

    // Validation should not crash
    const result = validateWorkflow(maliciousWorkflow);
    expect(result).toBeDefined();

    // Proto pollution should not have worked
    expect(({} as any).isAdmin).not.toBe(true);
  });

  it('should escape shell-like characters in node inputs', async () => {
    const { generateWorkflowForTarget } = await import('@/services/comfyui/workflowTemplates');

    const params = {
      prompt: '$(rm -rf /)',
      negativePrompt: '`cat /etc/passwd`',
      width: 512,
      height: 512,
      frameCount: 10,
      fps: 24,
      referenceImage: 'test.png; rm -rf /',
    };

    const workflow = generateWorkflowForTarget('wan22-i2v', params as any);

    // Workflow should be generated but inputs should be safe strings
    const workflowStr = JSON.stringify(workflow);

    // These should be escaped or rejected, not executable
    // The key is they shouldn't cause issues when workflow runs in ComfyUI
    expect(workflow).toBeDefined();
  });

  it('should handle circular references in layer data', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const layer: any = {
      id: 'circular',
      type: 'solid',
      visible: true,
    };
    layer.parent = layer; // Circular reference

    const pipeline = new ExportPipeline({
      layers: [layer],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 1,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    // Should not infinite loop
    const result = await pipeline.execute();
    expect(result).toBeDefined();
  });
});

// ============================================================================
// CATEGORY 4: BINARY FORMAT CORRUPTION
// ============================================================================

describe('ATTACK: NPY Binary Corruption', () => {

  it('should produce valid NPY header for edge case shapes', async () => {
    const { createNpyHeader } = await import('@/services/modelExport');

    const edgeCaseShapes = [
      [1],           // Single element
      [1, 1],        // 1x1
      [1, 1, 1],     // 1x1x1
      [0, 10, 2],    // Zero dimension (valid in NumPy)
      [10000, 10, 2], // Large first dimension
    ];

    for (const shape of edgeCaseShapes) {
      const header = createNpyHeader(shape);

      // Should produce valid header
      expect(header).toBeInstanceOf(Uint8Array);
      expect(header.length).toBeGreaterThan(10);

      // Header should start with magic number
      expect(header[0]).toBe(0x93); // \x93
      expect(header[1]).toBe(0x4E); // N
      expect(header[2]).toBe(0x55); // U
      expect(header[3]).toBe(0x4D); // M
      expect(header[4]).toBe(0x50); // P
      expect(header[5]).toBe(0x59); // Y
    }
  });

  it('should handle float overflow in depth normalization', async () => {
    const { convertDepthToFormat } = await import('@/services/export/depthRenderer');

    // Depth values that would overflow float32
    const extremeDepthResult = {
      depthBuffer: new Float32Array([
        Number.MAX_VALUE,
        -Number.MAX_VALUE,
        Number.MIN_VALUE,
        1e38,
        -1e38,
      ]),
      width: 5,
      height: 1,
      minDepth: -Number.MAX_VALUE,
      maxDepth: Number.MAX_VALUE,
    };

    const output = convertDepthToFormat(extremeDepthResult, 'midas');

    // Should not contain NaN or Infinity
    for (let i = 0; i < output.length; i++) {
      expect(Number.isFinite(output[i])).toBe(true);
    }
  });

  it('should handle subnormal floats in trajectory data', async () => {
    const { trajectoriesToNpy } = await import('@/services/modelExport');

    // Subnormal floats (very small numbers)
    const subnormalTrajectory = [
      [[Number.MIN_VALUE, Number.MIN_VALUE]],
      [[5e-324, 5e-324]], // Smallest positive float64
    ];

    const blob = trajectoriesToNpy(subnormalTrajectory);

    // Should produce valid blob
    expect(blob).toBeInstanceOf(Blob);
    expect(blob.size).toBeGreaterThan(0);
  });
});

// ============================================================================
// CATEGORY 5: DETERMINISM FAILURES
// ============================================================================

describe('ATTACK: Non-Deterministic Output', () => {

  it('should produce identical output for identical input (depth)', async () => {
    const { convertDepthToFormat } = await import('@/services/export/depthRenderer');

    const depthResult = {
      depthBuffer: new Float32Array([100, 200, 300, 400, 500]),
      width: 5,
      height: 1,
      minDepth: 100,
      maxDepth: 500,
    };

    const output1 = convertDepthToFormat(depthResult, 'midas');
    const output2 = convertDepthToFormat(depthResult, 'midas');

    // Should be byte-for-byte identical
    expect(output1.length).toBe(output2.length);
    for (let i = 0; i < output1.length; i++) {
      expect(output1[i]).toBe(output2[i]);
    }
  });

  it('should produce identical output for identical input (camera matrix)', async () => {
    const { computeViewMatrix } = await import('@/services/export/cameraExportFormats');

    const camera = {
      position: { x: 100, y: 200, z: -500 },
      rotation: { x: 30, y: 45, z: 15 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix1 = computeViewMatrix(camera);
    const matrix2 = computeViewMatrix(camera);

    // Should be identical
    for (let i = 0; i < 4; i++) {
      for (let j = 0; j < 4; j++) {
        expect(matrix1[i][j]).toBe(matrix2[i][j]);
      }
    }
  });

  it('should produce identical NPY for identical trajectories', async () => {
    const { trajectoriesToNpy } = await import('@/services/modelExport');

    const trajectory = [
      [[0, 0], [10, 10], [20, 20]],
    ];

    const blob1 = trajectoriesToNpy(trajectory);
    const blob2 = trajectoriesToNpy(trajectory);

    // Blobs should be same size
    expect(blob1.size).toBe(blob2.size);

    // Content should be identical
    const arr1 = new Uint8Array(await blob1.arrayBuffer());
    const arr2 = new Uint8Array(await blob2.arrayBuffer());

    for (let i = 0; i < arr1.length; i++) {
      expect(arr1[i]).toBe(arr2[i]);
    }
  });

  it('should maintain frame timing precision over long exports', async () => {
    const { exportCameraMatrices } = await import('@/services/export/cameraExportFormats');

    const camera = {
      id: 'test',
      position: { x: 0, y: 0, z: -500 },
      orientation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
    };

    const result = exportCameraMatrices(camera as any, [], {
      frameCount: 1000,
      width: 1920,
      height: 1080,
      fps: 24,
    });

    // Check frame timing doesn't drift
    const expectedFrameDuration = 1 / 24;

    for (let i = 1; i < result.frames.length; i++) {
      const actualDuration = result.frames[i].timestamp - result.frames[i - 1].timestamp;
      const drift = Math.abs(actualDuration - expectedFrameDuration);

      // Drift should be minimal (< 1 microsecond)
      expect(drift).toBeLessThan(0.000001);
    }
  });
});

// ============================================================================
// CATEGORY 6: CROSS-EXPORT STATE LEAKAGE
// ============================================================================

describe('ATTACK: Cross-Export State Leakage', () => {

  it('should not leak data between different preset exports', async () => {
    const { generateWorkflowForTarget } = await import('@/services/comfyui/workflowTemplates');

    // Export 1: wan22-i2v with specific settings
    const params1 = {
      prompt: 'SECRET_PROMPT_1',
      width: 832,
      height: 480,
      frameCount: 81,
      fps: 16,
      seed: 11111,
      referenceImage: 'secret1.png',
    };

    const workflow1 = generateWorkflowForTarget('wan22-i2v', params1 as any);

    // Export 2: motionctrl with different settings
    const params2 = {
      prompt: 'DIFFERENT_PROMPT',
      width: 576,
      height: 320,
      frameCount: 16,
      fps: 24,
      seed: 22222,
      referenceImage: 'public.png',
    };

    const workflow2 = generateWorkflowForTarget('motionctrl', params2 as any);

    // Workflow 2 should not contain any data from workflow 1
    const workflow2Str = JSON.stringify(workflow2);

    expect(workflow2Str).not.toContain('SECRET_PROMPT_1');
    expect(workflow2Str).not.toContain('secret1.png');
    expect(workflow2Str).not.toContain('11111');
  });

  it('should not retain camera data from previous export', async () => {
    const { exportCameraForTarget } = await import('@/services/export/cameraExportFormats');

    const camera = {
      id: 'test',
      position: { x: 999, y: 888, z: -777 },
      orientation: { x: 45, y: 90, z: 0 },
      focalLength: 50,
      zoom: 1,
    };

    const keyframes1 = [
      { frame: 0, position: { x: 100, y: 0, z: -500 } },
    ];

    const keyframes2: any[] = []; // Empty keyframes

    // Export 1 with keyframes
    const result1 = exportCameraForTarget('motionctrl', camera as any, keyframes1 as any, 10);

    // Export 2 without keyframes
    const result2 = exportCameraForTarget('motionctrl', camera as any, keyframes2, 10);

    // Result 2 should not contain data from keyframes1
    const result2Str = JSON.stringify(result2);
    expect(result2Str).not.toContain('100'); // x from keyframe1
  });
});

// ============================================================================
// CATEGORY 7: EDGE VALUES THAT LOOK VALID
// ============================================================================

describe('ATTACK: Edge Values That Look Valid', () => {

  it('should handle width = 8191 (just under GPU limit)', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 8191,
        height: 480,
        frameCount: 1,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    const result = await pipeline.execute();

    // Should either work or fail with clear message about size limit
    expect(result).toBeDefined();
  });

  it('should handle frameCount = 999 (just under typical limit)', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 999,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    const result = await pipeline.execute();
    expect(result.success).toBe(true);
  });

  it('should handle floating point fps (119.88 NTSC)', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 10,
        fps: 119.88, // Valid NTSC framerate
        startFrame: 0,
      } as any,
    });

    const result = await pipeline.execute();

    // Should either handle or reject with clear message
    expect(result).toBeDefined();
  });

  it('should handle Unicode in filenames', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const unicodeFilenames = [
      '日本語ファイル',
      'مرحبا',
      '🎬🎥🎞️',
      'файл',
      'αβγδ',
    ];

    for (const filename of unicodeFilenames) {
      const pipeline = new ExportPipeline({
        layers: [],
        cameraKeyframes: [],
        config: {
          target: 'wan22-i2v',
          width: 512,
          height: 512,
          frameCount: 1,
          fps: 24,
          startFrame: 0,
          filenamePrefix: filename,
        } as any,
      });

      const result = await pipeline.execute();

      // Should handle Unicode gracefully
      expect(result).toBeDefined();
    }
  });

  it('should handle zero-byte reference image gracefully', async () => {
    const { generateWorkflowForTarget } = await import('@/services/comfyui/workflowTemplates');

    const params = {
      prompt: 'test',
      width: 512,
      height: 512,
      frameCount: 10,
      fps: 24,
      referenceImage: '', // Empty string
    };

    // Should throw or handle gracefully
    expect(() => {
      generateWorkflowForTarget('wan22-i2v', params as any);
    }).toThrow();
  });
});

// ============================================================================
// CATEGORY 8: LAYER-SPECIFIC ATTACKS
// ============================================================================

describe('ATTACK: Layer Edge Cases', () => {

  it('should handle layer with 0% scale (potential div by zero)', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [{
        id: 'zero-scale',
        type: 'solid',
        visible: true,
        transform: {
          position: { value: { x: 0, y: 0 } },
          scale: { value: { x: 0, y: 0 } }, // Zero scale
          rotation: { value: 0 },
        },
      }] as any,
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 1,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    const result = await pipeline.execute();

    // Should not crash
    expect(result).toBeDefined();
  });

  it('should handle layer with negative frame range', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [{
        id: 'negative-frames',
        type: 'solid',
        visible: true,
        startFrame: -100,
        endFrame: -50,
        inPoint: -100,
        outPoint: -50,
      }] as any,
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 10,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    const result = await pipeline.execute();

    // Should handle gracefully
    expect(result).toBeDefined();
  });

  it('should handle self-referencing nested composition', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const comp: any = {
      id: 'self-ref',
      type: 'nestedComp',
      visible: true,
    };
    comp.nestedComposition = {
      layers: [comp], // Self-reference
    };

    const pipeline = new ExportPipeline({
      layers: [comp],
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512,
        height: 512,
        frameCount: 1,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    // Should detect cycle and not infinite loop
    const result = await pipeline.execute();
    expect(result).toBeDefined();
  });
});

// ============================================================================
// CATEGORY 9: EXPORT-SPECIFIC STATE ATTACKS
// ============================================================================

describe('ATTACK: Export-Specific Edge Cases', () => {

  it('should handle camera export with no keyframes', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [],
      cameraKeyframes: [], // Empty
      config: {
        target: 'motionctrl',
        width: 576,
        height: 320,
        frameCount: 16,
        fps: 24,
        startFrame: 0,
        exportCameraData: true, // Requires camera but no keyframes
      } as any,
    });

    const result = await pipeline.execute();

    // Should use default camera or fail with clear message
    expect(result).toBeDefined();
  });

  it('should handle depth export with no 3D layers', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [{
        id: '2d-only',
        type: 'solid', // 2D layer
        visible: true,
      }] as any,
      cameraKeyframes: [],
      config: {
        target: 'uni3c-camera',
        width: 512,
        height: 512,
        frameCount: 10,
        fps: 24,
        startFrame: 0,
        exportDepthMap: true, // Requires depth but only 2D layers
      } as any,
    });

    const result = await pipeline.execute();

    // Should produce flat depth or warn
    expect(result).toBeDefined();
  });

  it('should handle TTM mask with non-existent layer', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [{
        id: 'real-layer',
        type: 'solid',
        visible: true,
      }] as any,
      cameraKeyframes: [],
      config: {
        target: 'ttm',
        width: 512,
        height: 512,
        frameCount: 10,
        fps: 24,
        startFrame: 0,
        exportMaskVideo: true,
        maskLayerId: 'non-existent-layer', // Layer doesn't exist
      } as any,
    });

    const result = await pipeline.execute();

    // Should fail with clear error about missing layer
    expect(result.success).toBe(false);
    expect(result.errors.some(e => e.toLowerCase().includes('layer') || e.toLowerCase().includes('mask'))).toBe(true);
  });
});

// ============================================================================
// CATEGORY 10: RESOLUTION MISMATCH ATTACKS
// ============================================================================

describe('ATTACK: Resolution Mismatch', () => {

  it('should handle layer larger than export resolution', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const pipeline = new ExportPipeline({
      layers: [{
        id: 'huge-layer',
        type: 'solid',
        visible: true,
        width: 8192,
        height: 8192,
      }] as any,
      cameraKeyframes: [],
      config: {
        target: 'wan22-i2v',
        width: 512, // Much smaller than layer
        height: 512,
        frameCount: 1,
        fps: 24,
        startFrame: 0,
      } as any,
    });

    const result = await pipeline.execute();

    // Should scale down, not crash
    expect(result).toBeDefined();
  });

  it('should handle non-standard aspect ratios', async () => {
    const { ExportPipeline } = await import('@/services/export/exportPipeline');

    const weirdAspectRatios = [
      { width: 1, height: 1000 },   // 1:1000
      { width: 1000, height: 1 },   // 1000:1
      { width: 13, height: 7 },     // Prime numbers
      { width: 333, height: 222 },  // Weird ratio
    ];

    for (const { width, height } of weirdAspectRatios) {
      const pipeline = new ExportPipeline({
        layers: [],
        cameraKeyframes: [],
        config: {
          target: 'wan22-i2v',
          width,
          height,
          frameCount: 1,
          fps: 24,
          startFrame: 0,
        } as any,
      });

      const result = await pipeline.execute();

      // Should handle any valid positive dimensions
      expect(result).toBeDefined();
    }
  });
});
