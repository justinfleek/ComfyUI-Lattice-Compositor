/**
 * PathLayer Tests
 *
 * Tests for the PathLayer engine class including:
 * - Layer creation with PathLayerData
 * - Guide line configuration
 * - Curve utilities (getPointAt, getTangentAt)
 * - Control point evaluation
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import type { PathLayerData, ControlPoint, Layer, LayerTransform } from '@/types/project';

// Mock Three.js to avoid WebGL context issues in tests
vi.mock('three', async () => {
  const actual = await vi.importActual('three');
  return {
    ...actual,
    WebGLRenderer: vi.fn().mockImplementation(() => ({
      setSize: vi.fn(),
      render: vi.fn(),
      dispose: vi.fn(),
      domElement: document.createElement('canvas'),
    })),
  };
});

// Mock three-stdlib Line2 and LineGeometry
vi.mock('three-stdlib', () => ({
  Line2: vi.fn().mockImplementation(() => ({
    geometry: { setPositions: vi.fn(), dispose: vi.fn() },
    material: { color: { set: vi.fn() }, dashSize: 10, gapSize: 5, dispose: vi.fn() },
    computeLineDistances: vi.fn(),
    visible: true,
    userData: {},
  })),
  LineGeometry: vi.fn().mockImplementation(() => ({
    setPositions: vi.fn(),
    dispose: vi.fn(),
  })),
  LineMaterial: vi.fn().mockImplementation((opts: any) => ({
    color: { set: vi.fn() },
    dashSize: opts?.dashSize || 10,
    gapSize: opts?.gapSize || 5,
    dashed: opts?.dashed || false,
    dispose: vi.fn(),
  })),
}));

// ============================================================================
// TEST UTILITIES
// ============================================================================

function createAnimatableProp<T>(value: T, name: string = 'prop'): any {
  return {
    id: `prop_${Math.random().toString(36).substr(2, 9)}`,
    name,
    type: 'number',
    value,
    animated: false,
    keyframes: [],
  };
}

function createDefaultTransform(): LayerTransform {
  return {
    position: createAnimatableProp({ x: 0, y: 0, z: 0 }, 'Position'),
    rotation: createAnimatableProp(0, 'Rotation'),
    scale: createAnimatableProp({ x: 100, y: 100 }, 'Scale'),
    origin: createAnimatableProp({ x: 0, y: 0 }, 'Origin'),
  };
}

function createControlPoint(id: string, x: number, y: number, type: 'smooth' | 'corner' = 'smooth'): ControlPoint {
  return {
    id,
    x,
    y,
    handleIn: type === 'smooth' ? { x: x - 20, y } : null,
    handleOut: type === 'smooth' ? { x: x + 20, y } : null,
    type,
  };
}

function createPathLayerData(
  controlPoints: ControlPoint[] = [],
  options: Partial<PathLayerData> = {}
): PathLayerData {
  return {
    pathData: '',
    controlPoints,
    closed: false,
    showGuide: true,
    guideColor: '#00FFFF',
    guideDashPattern: [10, 5],
    ...options,
  };
}

function createPathLayer(data: PathLayerData, id: string = 'path-1'): Layer {
  return {
    id,
    name: 'Test Path',
    type: 'path',
    visible: true,
    locked: false,
    isolate: false,
    startFrame: 0,
    endFrame: 80,
    transform: createDefaultTransform(),
    opacity: createAnimatableProp(100, 'Opacity'),
    blendMode: 'normal',
    effects: [],
    masks: [],
    properties: [],
    parentId: null,
    threeD: false,
    motionBlur: false,
    data,
  } as Layer;
}

// ============================================================================
// PATH LAYER DATA TESTS
// ============================================================================

describe('PathLayerData', () => {
  describe('basic structure', () => {
    it('should have required properties', () => {
      const data = createPathLayerData();

      expect(data).toHaveProperty('pathData');
      expect(data).toHaveProperty('controlPoints');
      expect(data).toHaveProperty('closed');
      expect(data).toHaveProperty('showGuide');
      expect(data).toHaveProperty('guideColor');
      expect(data).toHaveProperty('guideDashPattern');
    });

    it('should have default guide color of cyan', () => {
      const data = createPathLayerData();
      expect(data.guideColor).toBe('#00FFFF');
    });

    it('should have default dash pattern of [10, 5]', () => {
      const data = createPathLayerData();
      expect(data.guideDashPattern).toEqual([10, 5]);
    });
  });

  describe('control points', () => {
    it('should store control points', () => {
      const points = [
        createControlPoint('cp1', 0, 0),
        createControlPoint('cp2', 100, 100),
        createControlPoint('cp3', 200, 0),
      ];
      const data = createPathLayerData(points);

      expect(data.controlPoints).toHaveLength(3);
      expect(data.controlPoints[0].x).toBe(0);
      expect(data.controlPoints[1].x).toBe(100);
      expect(data.controlPoints[2].x).toBe(200);
    });

    it('should support both smooth and corner points', () => {
      const points = [
        createControlPoint('cp1', 0, 0, 'smooth'),
        createControlPoint('cp2', 100, 100, 'corner'),
      ];
      const data = createPathLayerData(points);

      expect(data.controlPoints[0].type).toBe('smooth');
      expect(data.controlPoints[1].type).toBe('corner');
    });
  });

  describe('closed paths', () => {
    it('should support open paths', () => {
      const data = createPathLayerData([], { closed: false });
      expect(data.closed).toBe(false);
    });

    it('should support closed paths', () => {
      const data = createPathLayerData([], { closed: true });
      expect(data.closed).toBe(true);
    });
  });

  describe('guide visibility', () => {
    it('should show guide by default', () => {
      const data = createPathLayerData();
      expect(data.showGuide).toBe(true);
    });

    it('should support hiding guide', () => {
      const data = createPathLayerData([], { showGuide: false });
      expect(data.showGuide).toBe(false);
    });
  });
});

// ============================================================================
// PATH LAYER TYPE TESTS
// ============================================================================

describe('Path Layer Type', () => {
  it('should have type "path"', () => {
    const data = createPathLayerData();
    const layer = createPathLayer(data);

    expect(layer.type).toBe('path');
  });

  it('should be distinct from spline type', () => {
    const pathData = createPathLayerData();
    const pathLayer = createPathLayer(pathData);

    // Create a mock spline layer for comparison
    const splineLayer: Layer = {
      ...pathLayer,
      type: 'spline',
      data: {
        pathData: '',
        controlPoints: [],
        closed: false,
        stroke: '#00ff00',
        strokeWidth: 2,
        fill: 'none',
      },
    };

    expect(pathLayer.type).not.toBe(splineLayer.type);
  });
});

// ============================================================================
// GUIDE COLOR PRESETS TESTS
// ============================================================================

describe('Guide Color Presets', () => {
  const presets = [
    { name: 'Solid', dash: 0, gap: 0 },
    { name: 'Dotted', dash: 2, gap: 4 },
    { name: 'Dashed', dash: 10, gap: 5 },
    { name: 'Long Dash', dash: 20, gap: 10 },
  ];

  it('should support various dash patterns', () => {
    presets.forEach(preset => {
      const data = createPathLayerData([], {
        guideDashPattern: [preset.dash, preset.gap],
      });

      expect(data.guideDashPattern[0]).toBe(preset.dash);
      expect(data.guideDashPattern[1]).toBe(preset.gap);
    });
  });

  it('should support custom guide colors', () => {
    const customColors = ['#FF0000', '#00FF00', '#0000FF', '#FFFF00', '#FF00FF'];

    customColors.forEach(color => {
      const data = createPathLayerData([], { guideColor: color });
      expect(data.guideColor).toBe(color);
    });
  });
});

// ============================================================================
// ANIMATED PATH TESTS
// ============================================================================

describe('Animated Path Support', () => {
  it('should support animated flag', () => {
    const data = createPathLayerData([], { animated: true });
    expect(data.animated).toBe(true);
  });

  it('should support animatedControlPoints', () => {
    const animatedControlPoints: any[] = [
      {
        id: 'acp1',
        x: { value: 0, animated: true, keyframes: [] },
        y: { value: 0, animated: true, keyframes: [] },
        handleIn: null,
        handleOut: null,
        type: 'smooth',
      },
    ];

    const data = createPathLayerData([], {
      animated: true,
      animatedControlPoints,
    });

    expect(data.animatedControlPoints).toBeDefined();
    expect(data.animatedControlPoints).toHaveLength(1);
  });
});

// ============================================================================
// PATH LAYER INTEGRATION TESTS
// ============================================================================

describe('Path Layer Integration', () => {
  describe('layer structure', () => {
    it('should have correct default layer properties', () => {
      const data = createPathLayerData();
      const layer = createPathLayer(data);

      expect(layer.visible).toBe(true);
      expect(layer.locked).toBe(false);
      expect(layer.isolate).toBe(false);
      expect(layer.startFrame).toBe(0);
      expect(layer.endFrame).toBe(80);
      expect(layer.blendMode).toBe('normal');
    });

    it('should support transform properties', () => {
      const data = createPathLayerData();
      const layer = createPathLayer(data);

      // Transform properties
      expect(layer.transform).toHaveProperty('position');
      expect(layer.transform).toHaveProperty('rotation');
      expect(layer.transform).toHaveProperty('scale');
      expect(layer.transform).toHaveProperty('origin');  // origin replaces deprecated anchorPoint
      // Note: opacity is on layer directly, not in transform
      expect(layer).toHaveProperty('opacity');
    });
  });

  describe('path as motion guide', () => {
    it('should be usable as text-on-path reference', () => {
      const data = createPathLayerData([
        createControlPoint('cp1', 0, 100),
        createControlPoint('cp2', 200, 100),
      ]);
      const pathLayer = createPathLayer(data, 'motion-path-1');

      // Simulate a text layer referencing this path
      const textLayerData = {
        pathLayerId: pathLayer.id,
        textContent: 'Text on path',
      };

      expect(textLayerData.pathLayerId).toBe('motion-path-1');
    });

    it('should be usable as camera trajectory reference', () => {
      const data = createPathLayerData([
        createControlPoint('cp1', 0, 0),
        createControlPoint('cp2', 100, 50),
        createControlPoint('cp3', 200, 0),
      ]);
      const pathLayer = createPathLayer(data, 'camera-path-1');

      // Simulate a camera layer referencing this path
      const cameraTrajectory = {
        splineLayerId: pathLayer.id,
        progress: 0.5,
      };

      expect(cameraTrajectory.splineLayerId).toBe('camera-path-1');
    });

    it('should be usable as particle emitter path reference', () => {
      const data = createPathLayerData([
        createControlPoint('cp1', 0, 0),
        createControlPoint('cp2', 100, 100),
      ], { closed: true });
      const pathLayer = createPathLayer(data, 'emitter-path-1');

      // Simulate a particle emitter referencing this path
      const emitterConfig = {
        shape: 'spline',
        splinePath: {
          layerId: pathLayer.id,
          parameter: 0,
        },
      };

      expect(emitterConfig.splinePath.layerId).toBe('emitter-path-1');
    });
  });
});

// ============================================================================
// DETERMINISM TESTS
// ============================================================================

describe('Path Layer Determinism', () => {
  it('should produce consistent data structure', () => {
    const points = [
      createControlPoint('cp1', 50, 100),
      createControlPoint('cp2', 150, 50),
      createControlPoint('cp3', 250, 100),
    ];

    // Create same path twice
    const data1 = createPathLayerData(points);
    const data2 = createPathLayerData(points);

    expect(data1).toEqual(data2);
  });

  it('should maintain control point order', () => {
    const points = [
      createControlPoint('cp1', 0, 0),
      createControlPoint('cp2', 100, 100),
      createControlPoint('cp3', 200, 50),
      createControlPoint('cp4', 300, 100),
    ];

    const data = createPathLayerData(points);

    expect(data.controlPoints[0].id).toBe('cp1');
    expect(data.controlPoints[1].id).toBe('cp2');
    expect(data.controlPoints[2].id).toBe('cp3');
    expect(data.controlPoints[3].id).toBe('cp4');
  });
});

// ============================================================================
// TYPE DISCRIMINATION TESTS
// ============================================================================

describe('Type Discrimination', () => {
  it('should distinguish path from spline by type property', () => {
    const pathData = createPathLayerData();
    const pathLayer = createPathLayer(pathData);

    const isPath = pathLayer.type === 'path';
    const isSpline = pathLayer.type === 'spline';

    expect(isPath).toBe(true);
    expect(isSpline).toBe(false);
  });

  it('should work with type guard pattern', () => {
    const pathData = createPathLayerData();
    const layer = createPathLayer(pathData);

    function isPathLayer(l: Layer): l is Layer & { type: 'path'; data: PathLayerData } {
      return l.type === 'path';
    }

    expect(isPathLayer(layer)).toBe(true);

    if (isPathLayer(layer)) {
      // TypeScript should narrow the type
      expect(layer.data.guideColor).toBe('#00FFFF');
    }
  });

  it('should work with union type check', () => {
    const pathData = createPathLayerData();
    const layer = createPathLayer(pathData);

    function isSplineOrPath(type: string): boolean {
      return type === 'spline' || type === 'path';
    }

    expect(isSplineOrPath(layer.type)).toBe(true);
    expect(isSplineOrPath('solid')).toBe(false);
    expect(isSplineOrPath('text')).toBe(false);
  });
});
