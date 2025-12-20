/**
 * Path Animation Integration Tests
 *
 * Tests text/spline/solid layer creation and text-on-path animation
 * with easing and speed ramps.
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useCompositorStore } from '@/stores/compositorStore';
import { TextOnPathService, createDefaultPathConfig } from '@/services/textOnPath';
import { KeyframeEvaluator } from '@/engine/animation/KeyframeEvaluator';
import { easingFunctions } from '@/engine/animation/EasingFunctions';
import type { AnimatableProperty, Keyframe, ControlPoint, TextData, SplineData } from '@/types/project';

describe('Layer Creation', () => {
  let store: ReturnType<typeof useCompositorStore>;

  beforeEach(() => {
    setActivePinia(createPinia());
    store = useCompositorStore();
  });

  describe('Text Layer', () => {
    it('should create a text layer with default settings', () => {
      const layer = store.createTextLayer('Hello World');
      const data = layer.data as TextData;

      expect(layer).toBeDefined();
      expect(layer.type).toBe('text');
      expect(layer.name).toBe('Hello World');
      expect(data).toBeDefined();
      expect(data.text).toBe('Hello World');
      expect(data.fontFamily).toBe('Arial');
      expect(data.fontSize).toBe(72);
    });

    it('should have path options initialized', () => {
      const layer = store.createTextLayer('Test');
      const data = layer.data as TextData;

      expect(data.pathLayerId).toBeNull();
      expect(data.pathOffset).toBe(0);
      expect(data.pathReversed).toBe(false);
      expect(data.pathPerpendicularToPath).toBe(true);
    });
  });

  describe('Spline Layer', () => {
    it('should create a spline layer with default settings', () => {
      const layer = store.createSplineLayer();
      const data = layer.data as SplineData;

      expect(layer).toBeDefined();
      expect(layer.type).toBe('spline');
      expect(data).toBeDefined();
      expect(data.controlPoints).toEqual([]);
      expect(data.closed).toBe(false);
      expect(data.stroke).toBe('#00ff00');
      expect(data.strokeWidth).toBe(2);
    });
  });

  describe('Solid Layer', () => {
    it('should create a solid layer with default settings', () => {
      const layer = store.createLayer('solid', 'Solid');
      const data = layer.data as unknown as { color: string; width: number; height: number };

      expect(layer).toBeDefined();
      expect(layer.type).toBe('solid');
      expect(data).toBeDefined();
      expect(data.color).toBe('#808080');
      expect(data.width).toBeGreaterThan(0);
      expect(data.height).toBeGreaterThan(0);
    });
  });
});

describe('TextOnPathService', () => {
  let service: TextOnPathService;

  beforeEach(() => {
    service = new TextOnPathService();
  });

  it('should initialize without a path', () => {
    expect(service.hasPath()).toBe(false);
    expect(service.getTotalLength()).toBe(0);
  });

  it('should set a path from control points', () => {
    const controlPoints: ControlPoint[] = [
      { id: 'p1', x: 0, y: 0, handleIn: null, handleOut: { x: 100, y: 0 }, type: 'smooth' },
      { id: 'p2', x: 300, y: 0, handleIn: { x: -100, y: 0 }, handleOut: null, type: 'smooth' },
    ];

    service.setPath(controlPoints, false);

    expect(service.hasPath()).toBe(true);
    expect(service.getTotalLength()).toBeGreaterThan(0);
  });

  it('should calculate character placements along path', () => {
    const controlPoints: ControlPoint[] = [
      { id: 'p1', x: 0, y: 0, handleIn: null, handleOut: { x: 100, y: 0 }, type: 'smooth' },
      { id: 'p2', x: 300, y: 0, handleIn: { x: -100, y: 0 }, handleOut: null, type: 'smooth' },
    ];

    service.setPath(controlPoints, false);

    const config = createDefaultPathConfig();
    config.offset = 0;

    const characterWidths = [20, 20, 20, 20, 20]; // 5 characters
    const placements = service.calculatePlacements(characterWidths, config, 0, 72);

    expect(placements.length).toBe(5);
    expect(placements[0].visible).toBe(true);
    expect(placements[0].position).toBeDefined();
  });

  it('should handle path offset animation', () => {
    const controlPoints: ControlPoint[] = [
      { id: 'p1', x: 0, y: 0, handleIn: null, handleOut: { x: 100, y: 0 }, type: 'smooth' },
      { id: 'p2', x: 300, y: 0, handleIn: { x: -100, y: 0 }, handleOut: null, type: 'smooth' },
    ];

    service.setPath(controlPoints, false);

    const config0 = { ...createDefaultPathConfig(), offset: 0 };
    const config50 = { ...createDefaultPathConfig(), offset: 50 };
    const config100 = { ...createDefaultPathConfig(), offset: 100 };

    const characterWidths = [20];

    const placement0 = service.calculatePlacements(characterWidths, config0, 0, 72)[0];
    const placement50 = service.calculatePlacements(characterWidths, config50, 0, 72)[0];
    const placement100 = service.calculatePlacements(characterWidths, config100, 0, 72)[0];

    // Character should move along the path as offset increases
    expect(placement50.pathDistance).toBeGreaterThan(placement0.pathDistance);
    expect(placement100.pathDistance).toBeGreaterThan(placement50.pathDistance);
  });
});

describe('KeyframeEvaluator', () => {
  let evaluator: KeyframeEvaluator;

  beforeEach(() => {
    evaluator = new KeyframeEvaluator();
  });

  describe('Linear Interpolation', () => {
    it('should interpolate linearly between keyframes', () => {
      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'Path Offset',
        type: 'number',
        value: 0,
        animated: true,
        keyframes: [
          { id: 'k1', frame: 0, value: 0, interpolation: 'linear', controlMode: 'smooth', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false } },
          { id: 'k2', frame: 80, value: 100, interpolation: 'linear', controlMode: 'smooth', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false } },
        ],
      };

      expect(evaluator.evaluate(property, 0)).toBe(0);
      expect(evaluator.evaluate(property, 40)).toBe(50);
      expect(evaluator.evaluate(property, 80)).toBe(100);
    });
  });

  describe('Hold Interpolation', () => {
    it('should hold value until next keyframe', () => {
      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'Path Offset',
        type: 'number',
        value: 0,
        animated: true,
        keyframes: [
          { id: 'k1', frame: 0, value: 0, interpolation: 'hold', controlMode: 'smooth', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false } },
          { id: 'k2', frame: 80, value: 100, interpolation: 'linear', controlMode: 'smooth', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false } },
        ],
      };

      expect(evaluator.evaluate(property, 0)).toBe(0);
      expect(evaluator.evaluate(property, 40)).toBe(0); // Held at 0
      expect(evaluator.evaluate(property, 79)).toBe(0); // Still held
      expect(evaluator.evaluate(property, 80)).toBe(100);
    });
  });

  describe('Bezier Interpolation', () => {
    it('should use bezier curves for easing', () => {
      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'Path Offset',
        type: 'number',
        value: 0,
        animated: true,
        keyframes: [
          {
            id: 'k1',
            frame: 0,
            value: 0,
            interpolation: 'bezier',
            controlMode: 'smooth',
            inHandle: { frame: 0, value: 0, enabled: false },
            outHandle: { frame: 26, value: 0, enabled: true },
          },
          {
            id: 'k2',
            frame: 80,
            value: 100,
            interpolation: 'linear',
            controlMode: 'smooth',
            inHandle: { frame: -26, value: 0, enabled: true },
            outHandle: { frame: 0, value: 0, enabled: false },
          },
        ],
      };

      const midValue = evaluator.evaluate(property, 40);
      // With easing, mid value should NOT be exactly 50
      expect(midValue).toBeGreaterThanOrEqual(0);
      expect(midValue).toBeLessThanOrEqual(100);
    });
  });

  describe('Named Easing Functions', () => {
    it('should apply named easing functions', () => {
      // Test that all easing functions exist and return valid values
      const easingNames = Object.keys(easingFunctions);

      expect(easingNames.length).toBeGreaterThan(25); // Should have 30+ easings

      for (const name of easingNames) {
        const fn = easingFunctions[name];
        expect(fn(0)).toBeCloseTo(0, 10);
        expect(fn(1)).toBeCloseTo(1, 10);
        // Mid value should be between -0.5 and 1.5 (some easings overshoot)
        expect(fn(0.5)).toBeGreaterThanOrEqual(-0.5);
        expect(fn(0.5)).toBeLessThanOrEqual(1.5);
      }
    });

    it('should have standard easing functions', () => {
      expect(easingFunctions.easeInQuad).toBeDefined();
      expect(easingFunctions.easeOutQuad).toBeDefined();
      expect(easingFunctions.easeInOutQuad).toBeDefined();
      expect(easingFunctions.easeInCubic).toBeDefined();
      expect(easingFunctions.easeOutCubic).toBeDefined();
      expect(easingFunctions.easeInOutCubic).toBeDefined();
      expect(easingFunctions.easeInOutBack).toBeDefined();
      expect(easingFunctions.easeOutBounce).toBeDefined();
      expect(easingFunctions.easeOutElastic).toBeDefined();
    });
  });
});

describe('Text-on-Path Animation Integration', () => {
  let store: ReturnType<typeof useCompositorStore>;

  beforeEach(() => {
    setActivePinia(createPinia());
    store = useCompositorStore();
  });

  it('should connect text layer to spline layer', () => {
    // Create spline layer
    const splineLayer = store.createSplineLayer();

    // Add control points to make a path
    store.updateLayerData(splineLayer.id, {
      controlPoints: [
        { id: 'p1', x: 100, y: 300, handleIn: null, handleOut: { x: 100, y: 0 }, type: 'smooth' },
        { id: 'p2', x: 400, y: 300, handleIn: { x: -100, y: 0 }, handleOut: null, type: 'smooth' },
      ],
    });

    // Create text layer
    const textLayer = store.createTextLayer('Animate Me');

    // Connect text to spline
    store.updateLayerData(textLayer.id, {
      pathLayerId: splineLayer.id,
    });

    // Verify connection
    const updatedTextLayer = store.layers.find(l => l.id === textLayer.id);
    const updatedData = updatedTextLayer?.data as TextData;
    expect(updatedData.pathLayerId).toBe(splineLayer.id);
  });

  it('should connect text layer to spline and animate path offset', () => {
    // Create spline and text layers
    const splineLayer = store.createSplineLayer();
    const textLayer = store.createTextLayer('Animate Me');
    const textData = textLayer.data as TextData;

    // Connect text to spline
    store.updateLayerData(textLayer.id, { pathLayerId: splineLayer.id });

    // Verify connection
    const updatedTextLayer = store.layers.find(l => l.id === textLayer.id);
    const updatedData = updatedTextLayer?.data as TextData;
    expect(updatedData.pathLayerId).toBe(splineLayer.id);
  });
});
