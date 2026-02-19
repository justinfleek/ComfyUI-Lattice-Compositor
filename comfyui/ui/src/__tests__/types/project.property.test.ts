/**
 * PROPERTY TESTS: ui/src/types/project.ts
 * 
 * Created: 2026-01-06
 * Methodology: fast-check property-based testing
 * 
 * These tests verify INVARIANTS that must hold for ALL possible inputs,
 * not just specific examples. fast-check generates thousands of random
 * inputs to find edge cases.
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
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
  BLEND_MODE_CATEGORIES,
  type Layer,
  type LayerType,
  type BlendMode,
  type ProceduralMatteType,
} from '@/types/project';
import { createDefaultTransform } from '@/types/transform';
import { createAnimatableProperty } from '@/types/animation';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// ARBITRARIES (Generators)
// ═══════════════════════════════════════════════════════════════════════════

// All valid layer types
const ALL_LAYER_TYPES: LayerType[] = [
  'image', 'video', 'text', 'solid', 'shape', 'null', 'adjustment',
  'camera', 'light', 'audio', 'effectLayer', 'group', 'nestedComp',
  'spline', 'path', 'pose', 'generated', 'depth', 'normal',
  'control', 'matte', 'particle', 'depthflow',
  'model', 'pointcloud'
];

const layerTypeArb = fc.constantFrom(...ALL_LAYER_TYPES);

// All valid blend modes
const ALL_BLEND_MODES: BlendMode[] = [
  'normal', 'dissolve', 'multiply', 'darken', 'color-burn', 'linear-burn',
  'darker-color', 'screen', 'lighten', 'color-dodge', 'linear-dodge', 'add',
  'lighter-color', 'overlay', 'soft-light', 'hard-light', 'vivid-light',
  'linear-light', 'pin-light', 'hard-mix', 'difference', 'exclusion',
  'subtract', 'divide', 'hue', 'saturation', 'color', 'luminosity',
  'stencil-alpha', 'stencil-luma',
  'silhouette-alpha', 'silhouette-luma', 'alpha-add', 'luminescent-premul',
  'classic-color-burn', 'classic-color-dodge'
];

const blendModeArb = fc.constantFrom(...ALL_BLEND_MODES);

// Valid procedural matte pattern types (must match ProceduralMatteType)
const PATTERN_TYPES: ProceduralMatteType[] = [
  'linear_gradient', 'radial_gradient', 'angular_gradient',
  'ramp', 'noise', 'checkerboard', 'circle', 'rectangle',
  'grid', 'wave', 'venetian_blinds', 'iris', 'radial_wipe', 'dissolve'
];

const patternTypeArb = fc.constantFrom(...PATTERN_TYPES);

// Dimensions divisible by 8 (required for AI video models)
const dimensionArb = fc.integer({ min: 0, max: 1000 }).map(n => n * 8);

// Positive dimensions divisible by 8
const positiveDimensionArb = fc.integer({ min: 1, max: 1000 }).map(n => n * 8);

// Invalid dimensions (NOT divisible by 8)
const invalidDimensionArb = fc.integer({ min: 1, max: 7999 }).filter(n => n % 8 !== 0);

// Frame numbers (non-negative integers)
const frameArb = fc.integer({ min: 0, max: 10000 });

// Generate a minimal valid layer
function createMinimalLayer(type: LayerType): Layer {
  return {
    id: 'test-layer',
    name: 'Test',
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
    opacity: createAnimatableProperty("Opacity", 100, "number"),
    transform: createDefaultTransform(),
    properties: [],
    effects: [],
    data: null,
  };
}

const layerArb = layerTypeArb.map(type => createMinimalLayer(type));

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: isLayerOfType
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: isLayerOfType', () => {
  test.prop([layerArb])('always returns boolean', (layer) => {
    for (const type of ALL_LAYER_TYPES) {
      const result = isLayerOfType(layer, type);
      expect(typeof result).toBe('boolean');
    }
  });

  test.prop([layerTypeArb])('returns true when types match', (type) => {
    const layer = createMinimalLayer(type);
    expect(isLayerOfType(layer, type)).toBe(true);
  });

  test.prop([layerTypeArb, layerTypeArb])('returns false when types differ', (type1, type2) => {
    fc.pre(type1 !== type2); // Skip if same type
    const layer = createMinimalLayer(type1);
    expect(isLayerOfType(layer, type2)).toBe(false);
  });

  test.prop([layerArb])('is deterministic', (layer) => {
    const type = layer.type;
    const result1 = isLayerOfType(layer, type);
    const result2 = isLayerOfType(layer, type);
    expect(result1).toBe(result2);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: getLayerData
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: getLayerData', () => {
  test.prop([layerArb])('returns data when types match', (layer) => {
    // Set test data matching layer type
    // Type assertion: data must match LayerDataMap for the layer type
    const testData = { testField: 'value' };
    layer.data = testData as typeof layer.data;
    const result = getLayerData(layer, layer.type);
    expect(result).toBe(layer.data);
  });

  test.prop([layerTypeArb, layerTypeArb])('returns null when types differ', (type1, type2) => {
    fc.pre(type1 !== type2);
    const layer = createMinimalLayer(type1);
    // Set test data matching layer type
    const testData = { testField: 'value' };
    layer.data = testData as typeof layer.data;
    const result = getLayerData(layer, type2);
    expect(result).toBeNull();
  });

  test.prop([layerArb])('never throws', (layer) => {
    for (const type of ALL_LAYER_TYPES) {
      expect(() => getLayerData(layer, type)).not.toThrow();
    }
  });

  test.prop([layerArb])('is deterministic', (layer) => {
    const result1 = getLayerData(layer, layer.type);
    const result2 = getLayerData(layer, layer.type);
    expect(result1).toBe(result2);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: createDefaultEffectLayerData
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: createDefaultEffectLayerData', () => {
  test.prop([fc.constant(null)])('always returns valid structure', () => {
    const data = createDefaultEffectLayerData();
    
    // Actual interface: effectLayer, adjustmentLayer, color
    expect(data).toBeDefined();
    expect(typeof data.effectLayer).toBe('boolean');
    expect(typeof data.adjustmentLayer).toBe('boolean');
    expect(typeof data.color).toBe('string');
  });

  test.prop([fc.integer({ min: 1, max: 100 })])('is deterministic (same output every call)', (n) => {
    const results = Array.from({ length: n }, () => createDefaultEffectLayerData());
    
    // All results should be structurally identical
    for (let i = 1; i < results.length; i++) {
      expect(results[i].effectLayer).toBe(results[0].effectLayer);
      expect(results[i].adjustmentLayer).toBe(results[0].adjustmentLayer);
      expect(results[i].color).toBe(results[0].color);
    }
  });

  test.prop([fc.constant(null)])('effectLayer is always true', () => {
    const data = createDefaultEffectLayerData();
    expect(data.effectLayer).toBe(true);
  });

  test.prop([fc.constant(null)])('color is valid hex', () => {
    const data = createDefaultEffectLayerData();
    expect(data.color).toMatch(/^#[0-9a-fA-F]{6}$/);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: createDefaultLightLayerData
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: createDefaultLightLayerData', () => {
  test.prop([fc.constant(null)])('always returns valid structure', () => {
    const data = createDefaultLightLayerData();
    
    expect(data).toBeDefined();
    expect(typeof data.lightType).toBe('string');
    expect(typeof data.color).toBe('string');
    expect(typeof data.intensity).toBe('number');
    expect(data.intensity).toBeGreaterThanOrEqual(0);
  });

  test.prop([fc.integer({ min: 1, max: 100 })])('is deterministic', (n) => {
    const results = Array.from({ length: n }, () => createDefaultLightLayerData());
    
    for (let i = 1; i < results.length; i++) {
      expect(results[i].lightType).toBe(results[0].lightType);
      expect(results[i].color).toBe(results[0].color);
      expect(results[i].intensity).toBe(results[0].intensity);
    }
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: createDefaultSolidLayerData
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: createDefaultSolidLayerData', () => {
  test.prop([positiveDimensionArb, positiveDimensionArb])(
    'preserves exact dimensions',
    (width, height) => {
      const data = createDefaultSolidLayerData(width, height);
      expect(data.width).toBe(width);
      expect(data.height).toBe(height);
    }
  );

  test.prop([positiveDimensionArb, positiveDimensionArb])(
    'always has valid color',
    (width, height) => {
      const data = createDefaultSolidLayerData(width, height);
      expect(typeof data.color).toBe('string');
      expect(data.color).toMatch(/^#[0-9a-fA-F]{6}$/);
    }
  );

  test.prop([positiveDimensionArb, positiveDimensionArb])(
    'is deterministic for same inputs',
    (width, height) => {
      const data1 = createDefaultSolidLayerData(width, height);
      const data2 = createDefaultSolidLayerData(width, height);
      expect(data1.width).toBe(data2.width);
      expect(data1.height).toBe(data2.height);
      expect(data1.color).toBe(data2.color);
    }
  );

  test.prop([dimensionArb, dimensionArb])(
    'handles zero dimensions',
    (width, height) => {
      const data = createDefaultSolidLayerData(width, height);
      expect(data.width).toBe(width);
      expect(data.height).toBe(height);
    }
  );
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: createDefaultNullLayerData
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: createDefaultNullLayerData', () => {
  test.prop([fc.constant(null)])('always returns valid structure', () => {
    const data = createDefaultNullLayerData();
    expect(data).toBeDefined();
    expect(typeof data).toBe('object');
  });

  test.prop([fc.integer({ min: 1, max: 100 })])('is deterministic', (n) => {
    const results = Array.from({ length: n }, () => createDefaultNullLayerData());
    
    // All should be equivalent
    for (let i = 1; i < results.length; i++) {
      expect(JSON.stringify(results[i])).toBe(JSON.stringify(results[0]));
    }
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: createDefaultPoseLayerData
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: createDefaultPoseLayerData', () => {
  test.prop([fc.constant(null)])('always returns exactly 18 keypoints (COCO18)', () => {
    const data = createDefaultPoseLayerData();
    expect(data.poses).toBeDefined();
    expect(data.poses.length).toBe(1);
    expect(data.poses[0].keypoints.length).toBe(18);
  });

  test.prop([fc.constant(null)])('all keypoints have valid structure', () => {
    const data = createDefaultPoseLayerData();
    
    // Actual interface: x, y, confidence (NO name field)
    for (const keypoint of data.poses[0].keypoints) {
      expect(typeof keypoint.x).toBe('number');
      expect(typeof keypoint.y).toBe('number');
      expect(typeof keypoint.confidence).toBe('number');
      expect(keypoint.confidence).toBeGreaterThanOrEqual(0);
      expect(keypoint.confidence).toBeLessThanOrEqual(1);
    }
  });

  test.prop([fc.constant(null)])('has required PoseLayerData fields', () => {
    const data = createDefaultPoseLayerData();
    
    expect(data.format).toBeDefined();
    expect(typeof data.normalized).toBe('boolean');
    expect(typeof data.boneWidth).toBe('number');
    expect(typeof data.keypointRadius).toBe('number');
    expect(typeof data.showKeypoints).toBe('boolean');
    expect(typeof data.showBones).toBe('boolean');
  });

  test.prop([fc.integer({ min: 1, max: 100 })])('is deterministic', (n) => {
    const results = Array.from({ length: n }, () => createDefaultPoseLayerData());
    
    for (let i = 1; i < results.length; i++) {
      expect(results[i].poses.length).toBe(results[0].poses.length);
      expect(results[i].poses[0].keypoints.length).toBe(results[0].poses[0].keypoints.length);
    }
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: createDefaultProceduralMatteData
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: createDefaultProceduralMatteData', () => {
  test.prop([patternTypeArb])('preserves pattern type', (patternType) => {
    const data = createDefaultProceduralMatteData(patternType);
    expect(data.patternType).toBe(patternType);
  });

  test.prop([patternTypeArb])('always has required fields', (patternType) => {
    const data = createDefaultProceduralMatteData(patternType);
    
    // Actual interface: patternType, parameters, animation, inverted, levels
    expect(data.patternType).toBeDefined();
    expect(data.parameters).toBeDefined();
    expect(data.animation).toBeDefined();
    expect(typeof data.inverted).toBe('boolean');
    expect(data.levels).toBeDefined();
  });

  test.prop([patternTypeArb])('parameters has expected structure', (patternType) => {
    const data = createDefaultProceduralMatteData(patternType);
    
    expect(data.parameters.angle).toBeDefined();
    expect(data.parameters.blend).toBeDefined();
    expect(data.parameters.progress).toBeDefined();
    expect(data.parameters.centerX).toBeDefined();
    expect(data.parameters.centerY).toBeDefined();
  });

  test.prop([patternTypeArb])('animation has expected structure', (patternType) => {
    const data = createDefaultProceduralMatteData(patternType);
    
    expect(typeof data.animation.enabled).toBe('boolean');
    expect(data.animation.speed).toBeDefined();
    expect(data.animation.phase).toBeDefined();
    expect(data.animation.direction).toBeDefined();
  });

  test.prop([patternTypeArb])('levels has expected structure', (patternType) => {
    const data = createDefaultProceduralMatteData(patternType);
    
    expect(data.levels.inputBlack).toBeDefined();
    expect(data.levels.inputWhite).toBeDefined();
    expect(data.levels.gamma).toBeDefined();
    expect(data.levels.outputBlack).toBeDefined();
    expect(data.levels.outputWhite).toBeDefined();
  });

  test.prop([patternTypeArb])('is deterministic', (patternType) => {
    const data1 = createDefaultProceduralMatteData(patternType);
    const data2 = createDefaultProceduralMatteData(patternType);
    
    expect(data1.patternType).toBe(data2.patternType);
    expect(data1.inverted).toBe(data2.inverted);
    expect(data1.animation.enabled).toBe(data2.animation.enabled);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: normalizeLayerTiming
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: normalizeLayerTiming', () => {
  test.prop([frameArb, frameArb])('is idempotent: f(f(x)) = f(x)', (start, end) => {
    const layer = createMinimalLayer('solid');
    layer.startFrame = start;
    layer.endFrame = end;
    
    const once = normalizeLayerTiming({ ...layer });
    const twice = normalizeLayerTiming({ ...once });
    
    expect(twice.startFrame).toBe(once.startFrame);
    expect(twice.endFrame).toBe(once.endFrame);
    expect(twice.inPoint).toBe(once.inPoint);
    expect(twice.outPoint).toBe(once.outPoint);
  });

  test.prop([frameArb, frameArb])('preserves startFrame/endFrame', (start, end) => {
    const layer = createMinimalLayer('solid');
    layer.startFrame = start;
    layer.endFrame = end;
    
    const normalized = normalizeLayerTiming({ ...layer });
    
    expect(normalized.startFrame).toBe(start);
    expect(normalized.endFrame).toBe(end);
  });

  test.prop([frameArb, frameArb])('sets inPoint/outPoint from startFrame/endFrame', (start, end) => {
    const layer = createMinimalLayer('solid');
    layer.startFrame = start;
    layer.endFrame = end;
    delete layer.inPoint;
    delete layer.outPoint;
    
    const normalized = normalizeLayerTiming({ ...layer });
    
    expect(normalized.inPoint).toBe(start);
    expect(normalized.outPoint).toBe(end);
  });

  test.prop([frameArb, frameArb])('migrates inPoint/outPoint to startFrame/endFrame', (inP, outP) => {
    const baseLayer = createMinimalLayer('solid');
    // Create layer without startFrame/endFrame for testing migration behavior
    const { startFrame, endFrame, ...layerWithoutFrames } = baseLayer;
    const layer: Omit<Layer, 'startFrame' | 'endFrame'> & { inPoint: number; outPoint: number } = {
      ...layerWithoutFrames,
      inPoint: inP,
      outPoint: outP,
    };
    
    const normalized = normalizeLayerTiming(layer as Layer);
    
    expect(normalized.startFrame).toBe(inP);
    expect(normalized.endFrame).toBe(outP);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: createEmptyProject
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: createEmptyProject', () => {
  test.prop([positiveDimensionArb, positiveDimensionArb])(
    'preserves dimensions (divisible by 8)',
    (width, height) => {
      const project = createEmptyProject(width, height);
      
      expect(project.composition.width).toBe(width);
      expect(project.composition.height).toBe(height);
    }
  );

  test.prop([invalidDimensionArb, positiveDimensionArb])(
    'throws for width not divisible by 8',
    (width, height) => {
      expect(() => createEmptyProject(width, height)).toThrow(/divisible by 8/);
    }
  );

  test.prop([positiveDimensionArb, invalidDimensionArb])(
    'throws for height not divisible by 8',
    (width, height) => {
      expect(() => createEmptyProject(width, height)).toThrow(/divisible by 8/);
    }
  );

  test.prop([positiveDimensionArb, positiveDimensionArb])(
    'always has valid structure',
    (width, height) => {
      const project = createEmptyProject(width, height);
      
      expect(project.version).toBe('1.0.0');
      expect(project.schemaVersion).toBe(2);
      expect(project.mainCompositionId).toBe('main');
      expect(project.compositions).toBeDefined();
      expect(project.compositions.main).toBeDefined();
      expect(Array.isArray(project.layers)).toBe(true);
      expect(project.assets).toBeDefined();
    }
  );

  test.prop([positiveDimensionArb, positiveDimensionArb])(
    'has consistent composition settings',
    (width, height) => {
      const project = createEmptyProject(width, height);
      
      // Main composition should match legacy alias
      expect(project.composition.width).toBe(project.compositions.main.settings.width);
      expect(project.composition.height).toBe(project.compositions.main.settings.height);
      expect(project.composition.fps).toBe(project.compositions.main.settings.fps);
    }
  );

  test.prop([positiveDimensionArb, positiveDimensionArb])(
    'has valid frame settings',
    (width, height) => {
      const project = createEmptyProject(width, height);
      
      expect(project.composition.frameCount).toBeGreaterThan(0);
      expect(project.composition.fps).toBeGreaterThan(0);
      expect(project.composition.duration).toBe(
        project.composition.frameCount / project.composition.fps
      );
    }
  );
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: BLEND_MODE_CATEGORIES
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: BLEND_MODE_CATEGORIES', () => {
  test.prop([fc.constant(null)])('all modes are strings', () => {
    for (const category of Object.values(BLEND_MODE_CATEGORIES)) {
      for (const mode of category) {
        expect(typeof mode).toBe('string');
        expect(mode.length).toBeGreaterThan(0);
      }
    }
  });

  test.prop([fc.constant(null)])('no duplicate modes across categories', () => {
    const allModes: string[] = [];
    for (const category of Object.values(BLEND_MODE_CATEGORIES)) {
      allModes.push(...category);
    }
    
    const uniqueModes = new Set(allModes);
    expect(uniqueModes.size).toBe(allModes.length);
  });

  test.prop([fc.constant(null)])('all expected categories exist', () => {
    const expectedCategories = [
      'normal', 'darken', 'lighten', 'contrast',
      'inversion', 'component', 'utility'
    ];
    
    for (const category of expectedCategories) {
      expect(BLEND_MODE_CATEGORIES[category as keyof typeof BLEND_MODE_CATEGORIES]).toBeDefined();
    }
  });
});
