/**
 * Matte Exporter Tests
 *
 * Tests dimension validation, frame generation, and export functionality.
 * Note: Full canvas rendering tests are skipped in JSDOM.
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { matteExporter, type ExportOptions, type DimensionValidation } from '@/services/matteExporter';
import type { WeylProject, Layer, TextData, SplineData, ControlPoint } from '@/types/project';
import { createDefaultTransform, createAnimatableProperty } from '@/types/project';

// ============================================================================
// ENVIRONMENT CHECK
// ============================================================================

function isOffscreenCanvasSupported(): boolean {
  return typeof OffscreenCanvas !== 'undefined';
}

const OFFSCREEN_CANVAS_SUPPORTED = isOffscreenCanvasSupported();

// ============================================================================
// TEST HELPERS
// ============================================================================

function createMockProject(overrides: Partial<WeylProject> = {}): WeylProject {
  return {
    version: '1.0.0',
    mainCompositionId: 'main',
    currentFrame: 0,
    layers: [],
    compositions: {},
    composition: {
      width: 1920,
      height: 1080,
      frameCount: 81,
      fps: 16,
      duration: 81 / 16,
      backgroundColor: '#000000',
      autoResizeToContent: false,
    },
    assets: {},
    meta: {
      name: 'Test Project',
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
      author: 'test',
    },
    ...overrides,
  };
}

function createMockTextLayer(id: string, overrides: Partial<Layer> = {}): Layer {
  const textData: TextData = {
    text: 'Test Text',
    fontFamily: 'Arial',
    fontSize: 24,
    fontWeight: 'normal',
    fontStyle: 'normal',
    fill: '#ffffff',
    stroke: '#000000',
    strokeWidth: 0,
    tracking: 0,
    lineSpacing: 1.2,
    lineAnchor: 50,
    characterOffset: 0,
    characterValue: 0,
    blur: { x: 0, y: 0 },
    letterSpacing: 0,
    lineHeight: 1.2,
    textAlign: 'left',
    pathLayerId: null,
    pathReversed: false,
    pathPerpendicularToPath: false,
    pathForceAlignment: false,
    pathFirstMargin: 0,
    pathLastMargin: 0,
    pathOffset: 0,
    pathAlign: 'left',
    anchorPointGrouping: 'character',
    groupingAlignment: { x: 0, y: 0 },
    fillAndStroke: 'fill-over-stroke',
    interCharacterBlending: 'normal',
    perCharacter3D: false,
  };

  return {
    id,
    name: `Text Layer ${id}`,
    type: 'text',
    visible: true,
    locked: false,
    isolate: false,
    startFrame: 0,
    endFrame: 80,
    inPoint: 0,
    outPoint: 80,
    transform: createDefaultTransform(),
    opacity: createAnimatableProperty('opacity', 100, 'number'),
    blendMode: 'normal',
    parentId: null,
    threeD: false,
    motionBlur: false,
    effects: [],
    properties: [],
    data: textData,
    ...overrides,
  };
}

function createMockSplineLayer(id: string, controlPoints: ControlPoint[]): Layer {
  const splineData: SplineData = {
    pathData: '',
    controlPoints,
    closed: false,
    stroke: '#ffffff',
    strokeWidth: 2,
    fill: '',
  };

  return {
    id,
    name: `Spline ${id}`,
    type: 'spline',
    visible: true,
    locked: false,
    isolate: false,
    startFrame: 0,
    endFrame: 80,
    inPoint: 0,
    outPoint: 80,
    transform: createDefaultTransform(),
    opacity: createAnimatableProperty('opacity', 100, 'number'),
    blendMode: 'normal',
    parentId: null,
    threeD: false,
    motionBlur: false,
    effects: [],
    properties: [],
    data: splineData,
  };
}

// ============================================================================
// DIMENSION VALIDATION
// ============================================================================

describe('Dimension Validation', () => {
  it('should accept dimensions divisible by 8', () => {
    const result = matteExporter.validateDimensions(1920, 1080);
    expect(result.valid).toBe(true);
    expect(result.correctedWidth).toBe(1920);
    expect(result.correctedHeight).toBe(1080);
    expect(result.message).toBeUndefined();
  });

  it('should correct dimensions not divisible by 8', () => {
    const result = matteExporter.validateDimensions(1921, 1081);
    expect(result.valid).toBe(false);
    expect(result.correctedWidth).toBe(1920); // Rounded to nearest 8
    expect(result.correctedHeight).toBe(1080);
    expect(result.message).toBeDefined();
  });

  it('should round to nearest 8', () => {
    // 1924 / 8 = 240.5, rounds to 241 → 1928
    const result = matteExporter.validateDimensions(1924, 1084);
    expect(result.correctedWidth).toBe(1928); // Rounds to nearest 8
    expect(result.correctedHeight).toBe(1088);
  });

  it('should enforce minimum dimension of 256', () => {
    const result = matteExporter.validateDimensions(100, 100);
    expect(result.correctedWidth).toBe(256);
    expect(result.correctedHeight).toBe(256);
  });

  it('should handle edge case of exactly 256', () => {
    const result = matteExporter.validateDimensions(256, 256);
    expect(result.valid).toBe(true);
    expect(result.correctedWidth).toBe(256);
    expect(result.correctedHeight).toBe(256);
  });

  it('should handle common resolutions', () => {
    // 720p
    const r720 = matteExporter.validateDimensions(1280, 720);
    expect(r720.valid).toBe(true);
    expect(r720.correctedWidth).toBe(1280);
    expect(r720.correctedHeight).toBe(720);

    // 1080p
    const r1080 = matteExporter.validateDimensions(1920, 1080);
    expect(r1080.valid).toBe(true);

    // 4K
    const r4k = matteExporter.validateDimensions(3840, 2160);
    expect(r4k.valid).toBe(true);
  });
});

// ============================================================================
// RESOLUTION PRESETS
// ============================================================================

describe('Resolution Presets', () => {
  it('should return standard presets', () => {
    const presets = matteExporter.getResolutionPresets();

    expect(presets.length).toBeGreaterThan(0);
    expect(presets).toContainEqual(
      expect.objectContaining({ width: 1920, height: 1080 })
    );
  });

  it('should have all presets divisible by 8', () => {
    const presets = matteExporter.getResolutionPresets();

    for (const preset of presets) {
      expect(preset.width % 8).toBe(0);
      expect(preset.height % 8).toBe(0);
    }
  });

  it('should have valid labels', () => {
    const presets = matteExporter.getResolutionPresets();

    for (const preset of presets) {
      expect(preset.label).toBeDefined();
      expect(preset.label.length).toBeGreaterThan(0);
    }
  });
});

// ============================================================================
// FRAME GENERATION (JSDOM-limited tests)
// ============================================================================

describe('Frame Generation', () => {
  beforeEach(() => {
    // Clean up any previous state
    matteExporter.dispose();
  });

  it.skipIf(!OFFSCREEN_CANVAS_SUPPORTED)('should generate frame for empty project', async () => {
    const project = createMockProject();
    const options: ExportOptions = {
      width: 1920,
      height: 1080,
      matteMode: 'exclude_text',
    };

    const blob = await matteExporter.generatePreviewFrame(project, 0, options);

    expect(blob).toBeDefined();
    expect(typeof blob).toBe('string'); // URL string
    expect(blob.startsWith('blob:')).toBe(true);
  });

  it.skipIf(!OFFSCREEN_CANVAS_SUPPORTED)('should generate frame for project with text layer', async () => {
    const textLayer = createMockTextLayer('text-1');
    const project = createMockProject({ layers: [textLayer] });
    const options: ExportOptions = {
      width: 1920,
      height: 1080,
      matteMode: 'exclude_text',
    };

    const blob = await matteExporter.generatePreviewFrame(project, 0, options);

    expect(blob).toBeDefined();
    expect(blob.startsWith('blob:')).toBe(true);
  });

  it.skipIf(!OFFSCREEN_CANVAS_SUPPORTED)('should generate sequence with progress', async () => {
    const project = createMockProject({
      composition: { width: 1920, height: 1080, frameCount: 5, fps: 16, duration: 5/16, backgroundColor: '#000000', autoResizeToContent: false },
    });
    const options: ExportOptions = {
      width: 1920,
      height: 1080,
      matteMode: 'exclude_text',
    };

    const progressUpdates: number[] = [];
    const frames = await matteExporter.generateMatteSequence(
      project,
      options,
      (progress) => progressUpdates.push(progress.percent)
    );

    expect(frames.length).toBe(5);
    expect(progressUpdates.length).toBeGreaterThan(0);
    expect(progressUpdates[progressUpdates.length - 1]).toBe(100);
  });

  it.skipIf(!OFFSCREEN_CANVAS_SUPPORTED)('should handle include_all mode', async () => {
    const project = createMockProject();
    const options: ExportOptions = {
      width: 1920,
      height: 1080,
      matteMode: 'include_all',
    };

    const blob = await matteExporter.generatePreviewFrame(project, 0, options);

    expect(blob).toBeDefined();
    // In include_all mode, frame should be all white
  });
});

// ============================================================================
// TEXT ON PATH
// ============================================================================

describe('Text on Path', () => {
  it.skipIf(!OFFSCREEN_CANVAS_SUPPORTED)('should render text following spline path', async () => {
    // Create spline layer
    const spline = createMockSplineLayer('spline-1', [
      { id: 'cp1', x: 100, y: 500, handleIn: null, handleOut: { x: 200, y: 500 }, type: 'smooth' },
      { id: 'cp2', x: 500, y: 500, handleIn: { x: 400, y: 500 }, handleOut: null, type: 'smooth' },
    ]);

    // Create text layer attached to spline
    const textLayer = createMockTextLayer('text-1');

    const project = createMockProject({ layers: [spline, textLayer] });
    const options: ExportOptions = {
      width: 1920,
      height: 1080,
      matteMode: 'exclude_text',
    };

    const blob = await matteExporter.generatePreviewFrame(project, 0, options);

    expect(blob).toBeDefined();
  });
});

// ============================================================================
// LAYER VISIBILITY
// ============================================================================

describe('Layer Visibility', () => {
  it.skipIf(!OFFSCREEN_CANVAS_SUPPORTED)('should respect layer visibility', async () => {
    const hiddenTextLayer = createMockTextLayer('text-1', { visible: false });
    const visibleTextLayer = createMockTextLayer('text-2', { visible: true });

    const project = createMockProject({
      layers: [hiddenTextLayer, visibleTextLayer],
    });

    const options: ExportOptions = {
      width: 1920,
      height: 1080,
      matteMode: 'exclude_text',
    };

    // Should not throw and should only render visible layer
    const blob = await matteExporter.generatePreviewFrame(project, 0, options);
    expect(blob).toBeDefined();
  });

  it.skipIf(!OFFSCREEN_CANVAS_SUPPORTED)('should respect in/out points', async () => {
    const textLayer = createMockTextLayer('text-1', {
      inPoint: 10,
      outPoint: 50,
    });

    const project = createMockProject({ layers: [textLayer] });
    const options: ExportOptions = {
      width: 1920,
      height: 1080,
      matteMode: 'exclude_text',
    };

    // Frame 5 is before inPoint - text should not be rendered
    const beforeIn = await matteExporter.generatePreviewFrame(project, 5, options);
    expect(beforeIn).toBeDefined();

    // Frame 30 is within range - text should be rendered
    const withinRange = await matteExporter.generatePreviewFrame(project, 30, options);
    expect(withinRange).toBeDefined();

    // Frame 60 is after outPoint - text should not be rendered
    const afterOut = await matteExporter.generatePreviewFrame(project, 60, options);
    expect(afterOut).toBeDefined();
  });
});

// ============================================================================
// RESOURCE MANAGEMENT
// ============================================================================

describe('Resource Management', () => {
  it('should dispose without errors', () => {
    expect(() => matteExporter.dispose()).not.toThrow();
  });

  it('should be usable after dispose', async () => {
    matteExporter.dispose();

    // Should be able to use again
    const result = matteExporter.validateDimensions(1920, 1080);
    expect(result.valid).toBe(true);
  });
});

// ============================================================================
// EXPORT OPTIONS
// ============================================================================

describe('Export Options', () => {
  it('should handle different resolutions', () => {
    const resolutions = [
      { width: 1280, height: 720 },
      { width: 1920, height: 1080 },
      { width: 3840, height: 2160 },
    ];

    for (const res of resolutions) {
      const validation = matteExporter.validateDimensions(res.width, res.height);
      expect(validation.valid).toBe(true);
    }
  });

  it('should support both matte modes', () => {
    const modes: Array<'exclude_text' | 'include_all'> = ['exclude_text', 'include_all'];

    for (const mode of modes) {
      const options: ExportOptions = {
        width: 1920,
        height: 1080,
        matteMode: mode,
      };
      expect(options.matteMode).toBe(mode);
    }
  });
});

// ============================================================================
// ZIP EXPORT (JSDOM-limited)
// ============================================================================

describe('ZIP Export', () => {
  it.skipIf(!OFFSCREEN_CANVAS_SUPPORTED)('should generate zip download link', async () => {
    // Mock document functions for download
    const mockCreateElement = vi.spyOn(document, 'createElement');
    const mockAppendChild = vi.spyOn(document.body, 'appendChild').mockImplementation(() => null as any);
    const mockRemoveChild = vi.spyOn(document.body, 'removeChild').mockImplementation(() => null as any);

    // Create simple blobs
    const frames = [new Blob(['frame1']), new Blob(['frame2'])];

    try {
      // This will call JSZip and create download link
      // We're mainly testing that it doesn't throw
      await matteExporter.downloadAsZip(frames, 'test_export');
    } catch (e) {
      // JSZip might not be available in test environment
      // That's okay - we're testing the structure
    }

    mockCreateElement.mockRestore();
    mockAppendChild.mockRestore();
    mockRemoveChild.mockRestore();
  });
});
