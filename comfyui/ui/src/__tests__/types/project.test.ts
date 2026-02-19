/**
 * AUDIT TEST: ui/src/types/project.ts
 * 
 * Created: 2026-01-06
 * File Lines: 2,137
 * Importers: 198 (MOST CRITICAL FILE)
 * 
 * This file tests ALL exported functions from project.ts
 * Following MASTER_AUDIT.md methodology exactly.
 */

import { describe, expect, it } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  // Functions to test
  isLayerOfType,
  getLayerData,
  createDefaultEffectLayerData,
  createDefaultLightLayerData,
  createDefaultSolidLayerData,
  createDefaultNullLayerData,
  createDefaultPoseLayerData,
  createDefaultProceduralMatteData,
  normalizeLayerTiming,
  createEmptyProject,
  // Constants to test
  BLEND_MODE_CATEGORIES,
  // Types needed for testing
  type Layer,
  type LayerType,
  type EffectLayerData,
  type LightLayerData,
  type SolidLayerData,
  type NullLayerData,
  type PoseLayerData,
  type ProceduralMatteData,
  type LatticeProject,
} from '@/types/project';
import { createDefaultTransform } from '@/types/transform';
import { createAnimatableProperty } from '@/types/animation';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// HELPER: Create a minimal valid layer for testing
// ═══════════════════════════════════════════════════════════════════════════

function createMinimalLayer(type: LayerType, data: import("@/types/project").LayerDataUnion | null = null): Layer {
  return {
    id: 'test-layer-1',
    name: 'Test Layer',
    type,
    visible: true,
    locked: false,
    isolate: false,
    threeD: false,
    motionBlur: false,
    startFrame: 0,
    endFrame: 100,
    parentId: null,
    blendMode: 'normal',
    opacity: createAnimatableProperty('Opacity', 100, 'number'),
    transform: createDefaultTransform(),
    properties: [],
    effects: [],
    data,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// TEST: isLayerOfType (lines 733-738)
// ═══════════════════════════════════════════════════════════════════════════

describe('isLayerOfType', () => {
  it('returns true when layer type matches', () => {
    const layer = createMinimalLayer('solid', { color: '#ff0000', width: 100, height: 100 });
    expect(isLayerOfType(layer, 'solid')).toBe(true);
  });

  it('returns false when layer type does not match', () => {
    const layer = createMinimalLayer('solid', { color: '#ff0000', width: 100, height: 100 });
    expect(isLayerOfType(layer, 'image')).toBe(false);
  });

  // Test all 27 layer types
  const layerTypes: LayerType[] = [
    'depth', 'normal', 'spline', 'path', 'text', 'shape', 'particle', 'particles',
    'depthflow', 'image', 'video', 'audio', 'generated', 'camera', 'light', 'solid',
    'control', 'null', 'group', 'nestedComp', 'matte', 'model', 'pointcloud', 'pose',
    'effectLayer', 'adjustment',
  ];

  layerTypes.forEach((type) => {
    it(`correctly identifies '${type}' layer`, () => {
      const layer = createMinimalLayer(type, null);
      expect(isLayerOfType(layer, type)).toBe(true);
      
      // Should return false for a different type
      const otherType = type === 'solid' ? 'image' : 'solid';
      expect(isLayerOfType(layer, otherType)).toBe(false);
    });
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: getLayerData (lines 744-752)
// ═══════════════════════════════════════════════════════════════════════════

describe('getLayerData', () => {
  it('returns data when layer type matches', () => {
    const solidData = { color: '#ff0000', width: 100, height: 100 };
    const layer = createMinimalLayer('solid', solidData);
    
    const result = getLayerData(layer, 'solid');
    expect(result).toEqual(solidData);
  });

  it('returns null when layer type does not match', () => {
    const solidData = { color: '#ff0000', width: 100, height: 100 };
    const layer = createMinimalLayer('solid', solidData);
    
    const result = getLayerData(layer, 'image');
    expect(result).toBeNull();
  });

  it('returns null data correctly when data is null', () => {
    const layer = createMinimalLayer('null', null);
    // When type matches but data is null, still returns null
    expect(getLayerData(layer, 'null')).toBeNull();
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: createDefaultEffectLayerData (lines 1051-1057)
// ═══════════════════════════════════════════════════════════════════════════

describe('createDefaultEffectLayerData', () => {
  it('returns correct structure', () => {
    const data = createDefaultEffectLayerData();
    
    expect(data).toEqual({
      effectLayer: true,
      adjustmentLayer: true,
      color: '#FF6B6B',
    });
  });

  it('effectLayer is always true', () => {
    const data = createDefaultEffectLayerData();
    expect(data.effectLayer).toBe(true);
  });

  it('adjustmentLayer backwards compat is true', () => {
    const data = createDefaultEffectLayerData();
    expect(data.adjustmentLayer).toBe(true);
  });

  it('has valid hex color', () => {
    const data = createDefaultEffectLayerData();
    expect(data.color).toMatch(/^#[0-9A-Fa-f]{6}$/);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: createDefaultLightLayerData (lines 1105-1117)
// ═══════════════════════════════════════════════════════════════════════════

describe('createDefaultLightLayerData', () => {
  it('returns correct structure', () => {
    const data = createDefaultLightLayerData();
    
    expect(data).toEqual({
      lightType: 'point',
      color: '#ffffff',
      intensity: 100,
      radius: 500,
      falloff: 'none',
      falloffDistance: 500,
      castShadows: false,
      shadowDarkness: 100,
      shadowDiffusion: 0,
    });
  });

  it('lightType is point by default', () => {
    const data = createDefaultLightLayerData();
    expect(data.lightType).toBe('point');
  });

  it('color is white', () => {
    const data = createDefaultLightLayerData();
    expect(data.color).toBe('#ffffff');
  });

  it('intensity is 100', () => {
    const data = createDefaultLightLayerData();
    expect(data.intensity).toBe(100);
  });

  it('shadows disabled by default', () => {
    const data = createDefaultLightLayerData();
    expect(data.castShadows).toBe(false);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: createDefaultSolidLayerData (lines 1149-1158)
// ═══════════════════════════════════════════════════════════════════════════

describe('createDefaultSolidLayerData', () => {
  it('returns correct structure with defaults', () => {
    const data = createDefaultSolidLayerData();
    
    expect(data).toEqual({
      color: '#808080',
      width: 1920,
      height: 1080,
    });
  });

  it('accepts custom dimensions', () => {
    const data = createDefaultSolidLayerData(800, 600);
    
    expect(data.width).toBe(800);
    expect(data.height).toBe(600);
  });

  it('color is gray (#808080)', () => {
    const data = createDefaultSolidLayerData();
    expect(data.color).toBe('#808080');
  });

  // Edge cases
  it('handles zero dimensions', () => {
    const data = createDefaultSolidLayerData(0, 0);
    expect(data.width).toBe(0);
    expect(data.height).toBe(0);
  });

  it('handles very large dimensions', () => {
    const data = createDefaultSolidLayerData(16384, 16384);
    expect(data.width).toBe(16384);
    expect(data.height).toBe(16384);
  });

  it('handles negative dimensions (no validation in factory)', () => {
    // Note: Factory doesn't validate, this is a potential issue
    const data = createDefaultSolidLayerData(-100, -100);
    expect(data.width).toBe(-100);
    expect(data.height).toBe(-100);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: createDefaultNullLayerData (lines 1172-1176)
// ═══════════════════════════════════════════════════════════════════════════

describe('createDefaultNullLayerData', () => {
  it('returns correct structure', () => {
    const data = createDefaultNullLayerData();
    
    expect(data).toEqual({
      size: 40,
    });
  });

  it('size is 40 by default', () => {
    const data = createDefaultNullLayerData();
    expect(data.size).toBe(40);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: createDefaultPoseLayerData (lines 1235-1257)
// ═══════════════════════════════════════════════════════════════════════════

describe('createDefaultPoseLayerData', () => {
  it('returns correct structure', () => {
    const data = createDefaultPoseLayerData();
    
    expect(data.format).toBe('coco18');
    expect(data.normalized).toBe(true);
    expect(data.boneWidth).toBe(4);
    expect(data.keypointRadius).toBe(4);
    expect(data.showKeypoints).toBe(true);
    expect(data.showBones).toBe(true);
    expect(data.showLabels).toBe(false);
    expect(data.useDefaultColors).toBe(true);
    expect(data.customBoneColor).toBe('#FFFFFF');
    expect(data.customKeypointColor).toBe('#FF0000');
    expect(data.selectedKeypoint).toBe(-1);
    expect(data.selectedPose).toBe(0);
  });

  it('has exactly one pose', () => {
    const data = createDefaultPoseLayerData();
    expect(data.poses).toHaveLength(1);
  });

  it('default pose has 18 keypoints (COCO format)', () => {
    const data = createDefaultPoseLayerData();
    expect(data.poses[0].keypoints).toHaveLength(18);
  });

  it('all keypoints have valid structure', () => {
    const data = createDefaultPoseLayerData();
    
    data.poses[0].keypoints.forEach((kp, index) => {
      expect(typeof kp.x).toBe('number');
      expect(typeof kp.y).toBe('number');
      expect(typeof kp.confidence).toBe('number');
      expect(kp.x).toBeGreaterThanOrEqual(0);
      expect(kp.x).toBeLessThanOrEqual(1);
      expect(kp.y).toBeGreaterThanOrEqual(0);
      expect(kp.y).toBeLessThanOrEqual(1);
      expect(kp.confidence).toBe(1);
    });
  });

  it('keypoints form valid T-pose', () => {
    const data = createDefaultPoseLayerData();
    const kp = data.poses[0].keypoints;
    
    // Nose should be at top center
    expect(kp[0].x).toBeCloseTo(0.5, 2);
    expect(kp[0].y).toBeCloseTo(0.1, 2);
    
    // Left and right shoulders should be symmetric
    expect(kp[2].x + kp[5].x).toBeCloseTo(1, 2); // x coords sum to 1
    expect(kp[2].y).toBeCloseTo(kp[5].y, 2); // same y
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: createDefaultProceduralMatteData (lines 1537-1565)
// ═══════════════════════════════════════════════════════════════════════════

describe('createDefaultProceduralMatteData', () => {
  it('returns correct structure with default pattern', () => {
    const data = createDefaultProceduralMatteData();
    
    expect(data.patternType).toBe('linear_gradient');
    expect(data.inverted).toBe(false);
    expect(data.animation.enabled).toBe(false);
  });

  it('accepts custom pattern type', () => {
    const data = createDefaultProceduralMatteData('noise');
    expect(data.patternType).toBe('noise');
  });

  it('has all required parameter properties', () => {
    const data = createDefaultProceduralMatteData();
    
    expect(data.parameters.angle).toBeDefined();
    expect(data.parameters.blend).toBeDefined();
    expect(data.parameters.progress).toBeDefined();
    expect(data.parameters.centerX).toBeDefined();
    expect(data.parameters.centerY).toBeDefined();
    expect(data.parameters.radius).toBeDefined();
  });

  it('has all level controls', () => {
    const data = createDefaultProceduralMatteData();
    
    expect(data.levels.inputBlack).toBeDefined();
    expect(data.levels.inputWhite).toBeDefined();
    expect(data.levels.gamma).toBeDefined();
    expect(data.levels.outputBlack).toBeDefined();
    expect(data.levels.outputWhite).toBeDefined();
  });

  // Test all pattern types
  const patternTypes = [
    'linear_gradient', 'radial_gradient', 'angular_gradient', 'ramp',
    'noise', 'checkerboard', 'circle', 'rectangle', 'grid', 'wave',
    'venetian_blinds', 'iris', 'radial_wipe', 'dissolve',
  ] as const;

  patternTypes.forEach((pattern) => {
    it(`creates data for '${pattern}' pattern`, () => {
      const data = createDefaultProceduralMatteData(pattern);
      expect(data.patternType).toBe(pattern);
    });
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: normalizeLayerTiming (lines 2072-2089)
// ═══════════════════════════════════════════════════════════════════════════

describe('normalizeLayerTiming', () => {
  it('converts inPoint to startFrame', () => {
    const layer = createMinimalLayer('solid', null);
    // Test migration: create layer with inPoint but no startFrame
    // Using Partial<Layer> to create incomplete layer for testing migration path
    const layerWithInPoint: Partial<Layer> = { ...layer };
    delete layerWithInPoint.startFrame;
    layerWithInPoint.inPoint = 10;
    
    const result = normalizeLayerTiming(layerWithInPoint as Layer);
    
    expect(result.startFrame).toBe(10);
  });

  it('converts outPoint to endFrame', () => {
    const layer = createMinimalLayer('solid', null);
    // Test migration: create layer with outPoint but no endFrame
    // Using Partial<Layer> to create incomplete layer for testing migration path
    const layerWithOutPoint: Partial<Layer> = { ...layer };
    delete layerWithOutPoint.endFrame;
    layerWithOutPoint.outPoint = 200;
    
    const result = normalizeLayerTiming(layerWithOutPoint as Layer);
    
    expect(result.endFrame).toBe(200);
  });

  it('sets inPoint from startFrame for backwards compat', () => {
    const layer = createMinimalLayer('solid', null);
    layer.startFrame = 25;
    delete layer.inPoint;
    
    const result = normalizeLayerTiming(layer);
    
    expect(result.inPoint).toBe(25);
  });

  it('sets outPoint from endFrame for backwards compat', () => {
    const layer = createMinimalLayer('solid', null);
    layer.endFrame = 150;
    delete layer.outPoint;
    
    const result = normalizeLayerTiming(layer);
    
    expect(result.outPoint).toBe(150);
  });

  it('preserves existing startFrame if inPoint undefined', () => {
    const layer = createMinimalLayer('solid', null);
    layer.startFrame = 5;
    
    const result = normalizeLayerTiming(layer);
    
    expect(result.startFrame).toBe(5);
  });

  it('MUTATES the input layer (documented behavior)', () => {
    const layer = createMinimalLayer('solid', null);
    // Test migration: create layer with inPoint but no startFrame
    // Using Partial<Layer> to create incomplete layer for testing migration path
    const layerWithInPoint: Partial<Layer> = { ...layer };
    delete layerWithInPoint.startFrame;
    layerWithInPoint.inPoint = 10;
    
    normalizeLayerTiming(layerWithInPoint as Layer);
    
    // The input layer should be modified
    expect(layerWithInPoint.startFrame).toBe(10);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: createEmptyProject (lines 2094-2136)
// ═══════════════════════════════════════════════════════════════════════════

describe('createEmptyProject', () => {
  it('creates valid project structure', () => {
    const project = createEmptyProject(1920, 1080);
    
    expect(project.version).toBe('1.0.0');
    expect(project.schemaVersion).toBe(2);
    expect(project.mainCompositionId).toBe('main');
  });

  it('uses provided dimensions', () => {
    const project = createEmptyProject(800, 600);
    
    expect(project.composition.width).toBe(800);
    expect(project.composition.height).toBe(600);
  });

  it('has empty layers array', () => {
    const project = createEmptyProject(1920, 1080);
    
    expect(project.layers).toEqual([]);
    expect(project.compositions.main.layers).toEqual([]);
  });

  it('has correct default frame settings', () => {
    const project = createEmptyProject(1920, 1080);
    
    expect(project.composition.frameCount).toBe(81);
    expect(project.composition.fps).toBe(16);
    expect(project.composition.duration).toBe(81 / 16);
  });

  it('has valid meta timestamps', () => {
    const before = new Date().toISOString();
    const project = createEmptyProject(1920, 1080);
    const after = new Date().toISOString();
    
    expect(project.meta.created).toBeDefined();
    expect(project.meta.modified).toBeDefined();
    expect(project.meta.created >= before).toBe(true);
    expect(project.meta.created <= after).toBe(true);
  });

  it('has empty assets', () => {
    const project = createEmptyProject(1920, 1080);
    expect(project.assets).toEqual({});
  });

  it('main composition matches legacy composition alias', () => {
    const project = createEmptyProject(1920, 1080);
    
    expect(project.composition.width).toBe(project.compositions.main.settings.width);
    expect(project.composition.height).toBe(project.compositions.main.settings.height);
    expect(project.composition.fps).toBe(project.compositions.main.settings.fps);
  });

  // Edge cases - valid (divisible by 8)
  it('handles zero dimensions (divisible by 8)', () => {
    const project = createEmptyProject(0, 0);
    expect(project.composition.width).toBe(0);
    expect(project.composition.height).toBe(0);
  });

  it('handles large dimensions (divisible by 8)', () => {
    const project = createEmptyProject(8192, 8192);
    expect(project.composition.width).toBe(8192);
    expect(project.composition.height).toBe(8192);
  });

  // VALIDATION: Dimensions must be divisible by 8
  it('throws for width not divisible by 8', () => {
    expect(() => createEmptyProject(1921, 1080)).toThrow(/divisible by 8/);
  });

  it('throws for height not divisible by 8', () => {
    expect(() => createEmptyProject(1920, 1081)).toThrow(/divisible by 8/);
  });

  it('throws for both dimensions not divisible by 8', () => {
    expect(() => createEmptyProject(1921, 1081)).toThrow(/divisible by 8/);
  });

  it('error message suggests corrected dimensions', () => {
    try {
      createEmptyProject(1921, 1081);
      expect.fail('Should have thrown');
    } catch (e) {
      const error = e as Error;
      expect(error.message).toContain('1920'); // suggested width
      expect(error.message).toContain('1080'); // suggested height
    }
  });

  // Property test: all 8-divisible dimensions work
  test.prop([
    fc.integer({ min: 0, max: 1000 }).map(n => n * 8), // width divisible by 8
    fc.integer({ min: 0, max: 1000 }).map(n => n * 8), // height divisible by 8
  ])('accepts any dimensions divisible by 8', (width, height) => {
    const project = createEmptyProject(width, height);
    expect(project.composition.width).toBe(width);
    expect(project.composition.height).toBe(height);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TEST: BLEND_MODE_CATEGORIES (lines 804-834)
// ═══════════════════════════════════════════════════════════════════════════

describe('BLEND_MODE_CATEGORIES', () => {
  it('has all required categories', () => {
    expect(BLEND_MODE_CATEGORIES.normal).toBeDefined();
    expect(BLEND_MODE_CATEGORIES.darken).toBeDefined();
    expect(BLEND_MODE_CATEGORIES.lighten).toBeDefined();
    expect(BLEND_MODE_CATEGORIES.contrast).toBeDefined();
    expect(BLEND_MODE_CATEGORIES.inversion).toBeDefined();
    expect(BLEND_MODE_CATEGORIES.component).toBeDefined();
    expect(BLEND_MODE_CATEGORIES.utility).toBeDefined();
  });

  it('normal category has correct modes', () => {
    expect(BLEND_MODE_CATEGORIES.normal).toContain('normal');
    expect(BLEND_MODE_CATEGORIES.normal).toContain('dissolve');
    expect(BLEND_MODE_CATEGORIES.normal).toHaveLength(2);
  });

  it('darken category has 5 modes', () => {
    expect(BLEND_MODE_CATEGORIES.darken).toHaveLength(5);
    expect(BLEND_MODE_CATEGORIES.darken).toContain('multiply');
  });

  it('lighten category has 6 modes', () => {
    expect(BLEND_MODE_CATEGORIES.lighten).toHaveLength(6);
    expect(BLEND_MODE_CATEGORIES.lighten).toContain('screen');
    expect(BLEND_MODE_CATEGORIES.lighten).toContain('add');
  });

  it('contrast category has 7 modes', () => {
    expect(BLEND_MODE_CATEGORIES.contrast).toHaveLength(7);
    expect(BLEND_MODE_CATEGORIES.contrast).toContain('overlay');
  });

  it('all categories contain only strings', () => {
    Object.values(BLEND_MODE_CATEGORIES).forEach((modes) => {
      modes.forEach((mode) => {
        expect(typeof mode).toBe('string');
      });
    });
  });

  it('no duplicate modes across categories', () => {
    const allModes: string[] = [];
    Object.values(BLEND_MODE_CATEGORIES).forEach((modes) => {
      allModes.push(...modes);
    });
    
    const uniqueModes = new Set(allModes);
    expect(uniqueModes.size).toBe(allModes.length);
  });
});
