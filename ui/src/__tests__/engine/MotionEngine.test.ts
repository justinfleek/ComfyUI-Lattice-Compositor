/**
 * MotionEngine Determinism Tests
 *
 * These tests verify that the MotionEngine produces deterministic results
 * regardless of evaluation order (scrubbing).
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { MotionEngine, type FrameState } from '@/engine/MotionEngine';
import type { WeylProject, AnimatableProperty, Keyframe, Layer } from '@/types/project';
import { createEmptyProject, createAnimatableProperty, createDefaultTransform } from '@/types/project';

// ============================================================================
// TEST UTILITIES
// ============================================================================

function createTestProject(): WeylProject {
  const project = createEmptyProject(1920, 1080);

  // Add a layer with animated properties
  const layer: Layer = {
    id: 'layer-1',
    name: 'Test Layer',
    type: 'solid',
    visible: true,
    locked: false,
    solo: false,
      isolate: false,
    threeD: false,
    motionBlur: false,
    inPoint: 0,
    outPoint: 80,
    parentId: null,
    blendMode: 'normal',
    opacity: createAnimatedOpacity(),
    transform: createAnimatedTransform(),
    properties: [],
    effects: [],
    data: null,
  };

  project.compositions['main'].layers.push(layer);
  return project;
}

function createAnimatedOpacity(): AnimatableProperty<number> {
  return {
    id: 'opacity',
    name: 'Opacity',
    type: 'number',
    value: 100,
    animated: true,
    keyframes: [
      createKeyframe(0, 0, 100),
      createKeyframe(1, 40, 50),
      createKeyframe(2, 80, 100),
    ],
  };
}

function createAnimatedTransform() {
  const transform = createDefaultTransform();

  // Animate position
  transform.position.animated = true;
  transform.position.keyframes = [
    createKeyframe(0, 0, { x: 0, y: 0 }),
    createKeyframe(1, 40, { x: 500, y: 300 }),
    createKeyframe(2, 80, { x: 1000, y: 0 }),
  ];

  return transform;
}

function createKeyframe<T>(id: number, frame: number, value: T): Keyframe<T> {
  return {
    id: `kf-${id}`,
    frame,
    value,
    interpolation: 'linear',
    inHandle: { frame: 0, value: 0, enabled: false },
    outHandle: { frame: 0, value: 0, enabled: false },
    controlMode: 'smooth',
  };
}

/**
 * Deep equality check for FrameState
 */
function frameStatesEqual(a: FrameState, b: FrameState): boolean {
  // Compare frame number
  if (a.frame !== b.frame) return false;

  // Compare layer count
  if (a.layers.length !== b.layers.length) return false;

  // Compare each layer
  for (let i = 0; i < a.layers.length; i++) {
    const layerA = a.layers[i];
    const layerB = b.layers[i];

    if (layerA.id !== layerB.id) return false;
    if (layerA.opacity !== layerB.opacity) return false;
    if (layerA.visible !== layerB.visible) return false;

    // Compare transform
    if (layerA.transform.position.x !== layerB.transform.position.x) return false;
    if (layerA.transform.position.y !== layerB.transform.position.y) return false;
    if (layerA.transform.rotation !== layerB.transform.rotation) return false;
  }

  // Compare audio
  if (a.audio.hasAudio !== b.audio.hasAudio) return false;
  if (a.audio.amplitude !== b.audio.amplitude) return false;

  return true;
}

// ============================================================================
// TESTS
// ============================================================================

describe('MotionEngine Determinism', () => {
  let engine: MotionEngine;
  let project: WeylProject;

  beforeEach(() => {
    engine = new MotionEngine();
    project = createTestProject();
  });

  describe('Basic Evaluation', () => {
    it('should return consistent state for same frame', () => {
      const state1 = engine.evaluate(40, project);
      const state2 = engine.evaluate(40, project);

      expect(frameStatesEqual(state1, state2)).toBe(true);
    });

    it('should return FrameState with correct frame number', () => {
      const state = engine.evaluate(25, project);
      expect(state.frame).toBe(25);
    });

    it('should evaluate layer visibility based on in/out points', () => {
      const stateInRange = engine.evaluate(40, project);
      expect(stateInRange.layers[0].visible).toBe(true);
      expect(stateInRange.layers[0].inRange).toBe(true);
    });
  });

  describe('Scrub Determinism', () => {
    it('should produce identical results regardless of evaluation order', () => {
      // First evaluation order: 0 → 50 → 100 → 50
      engine.evaluate(0, project);
      engine.evaluate(50, project);
      const state100_first = engine.evaluate(100, project);
      const state50_after100 = engine.evaluate(50, project);

      // Reset engine (create new instance)
      const engine2 = new MotionEngine();

      // Second evaluation order: 0 → 100 → 50
      engine2.evaluate(0, project);
      const state100_second = engine2.evaluate(100, project);
      const state50_direct = engine2.evaluate(50, project);

      // Results should be identical regardless of order
      expect(frameStatesEqual(state100_first, state100_second)).toBe(true);
      expect(frameStatesEqual(state50_after100, state50_direct)).toBe(true);
    });

    it('should produce same results when scrubbing forward and backward', () => {
      // Evaluate frame 60 directly
      const state60_direct = engine.evaluate(60, project);

      // Evaluate in different order: 0 → 80 → 40 → 60
      engine.evaluate(0, project);
      engine.evaluate(80, project);
      engine.evaluate(40, project);
      const state60_after_scrub = engine.evaluate(60, project);

      expect(frameStatesEqual(state60_direct, state60_after_scrub)).toBe(true);
    });
  });

  describe('Keyframe Interpolation', () => {
    it('should interpolate opacity correctly at keyframe', () => {
      const state0 = engine.evaluate(0, project);
      const state40 = engine.evaluate(40, project);
      const state80 = engine.evaluate(80, project);

      expect(state0.layers[0].opacity).toBe(100);
      expect(state40.layers[0].opacity).toBe(50);
      expect(state80.layers[0].opacity).toBe(100);
    });

    it('should interpolate opacity between keyframes', () => {
      const state20 = engine.evaluate(20, project);
      // Linear interpolation: 100 → 50 over 40 frames, at frame 20: 100 - (50/40)*20 = 75
      expect(state20.layers[0].opacity).toBeCloseTo(75, 0);
    });

    it('should interpolate position correctly', () => {
      const state0 = engine.evaluate(0, project);
      const state40 = engine.evaluate(40, project);

      expect(state0.layers[0].transform.position.x).toBe(0);
      expect(state0.layers[0].transform.position.y).toBe(0);

      expect(state40.layers[0].transform.position.x).toBe(500);
      expect(state40.layers[0].transform.position.y).toBe(300);
    });
  });

  describe('Multiple Evaluations', () => {
    it('should handle 100 sequential evaluations consistently', () => {
      const results: FrameState[] = [];

      // Evaluate frames 0-99
      for (let i = 0; i < 100; i++) {
        results.push(engine.evaluate(i % 81, project));
      }

      // Re-evaluate same frames in reverse
      for (let i = 99; i >= 0; i--) {
        const frame = i % 81;
        const newResult = engine.evaluate(frame, project);
        const originalResult = results[i];

        expect(frameStatesEqual(newResult, originalResult)).toBe(true);
      }
    });

    it('should handle random access pattern', () => {
      // Random-ish access pattern
      const frames = [50, 10, 70, 30, 60, 20, 80, 0, 40];
      const firstResults = new Map<number, FrameState>();

      // First pass
      for (const frame of frames) {
        firstResults.set(frame, engine.evaluate(frame, project));
      }

      // Second pass (different order)
      const reversedFrames = [...frames].reverse();
      for (const frame of reversedFrames) {
        const newResult = engine.evaluate(frame, project);
        const originalResult = firstResults.get(frame)!;

        expect(frameStatesEqual(newResult, originalResult)).toBe(true);
      }
    });
  });

  describe('Audio Determinism', () => {
    it('should return consistent audio state without analysis', () => {
      const state1 = engine.evaluate(40, project, null);
      const state2 = engine.evaluate(40, project, null);

      expect(state1.audio.hasAudio).toBe(false);
      expect(state2.audio.hasAudio).toBe(false);
      expect(state1.audio.amplitude).toBe(state2.audio.amplitude);
    });
  });

  describe('Immutability', () => {
    it('should return frozen FrameState', () => {
      const state = engine.evaluate(40, project);

      expect(Object.isFrozen(state)).toBe(true);
      expect(Object.isFrozen(state.layers)).toBe(true);
      expect(Object.isFrozen(state.audio)).toBe(true);
    });

    it('should not allow mutation of returned state', () => {
      const state = engine.evaluate(40, project);

      // Attempting to modify should throw in strict mode or fail silently
      expect(() => {
        (state as any).frame = 999;
      }).toThrow();
    });
  });

  describe('Empty Project', () => {
    it('should handle project with no layers', () => {
      const emptyProject = createEmptyProject(1920, 1080);
      const state = engine.evaluate(40, emptyProject);

      expect(state.frame).toBe(40);
      expect(state.layers.length).toBe(0);
      expect(state.camera).toBe(null);
    });
  });
});

describe('interpolateProperty Determinism', () => {
  it('should return identical values for same frame', () => {
    const engine = new MotionEngine();

    const property: AnimatableProperty<number> = {
      id: 'test',
      name: 'Test',
      type: 'number',
      value: 50,
      animated: true,
      keyframes: [
        createKeyframe(0, 0, 0),
        createKeyframe(1, 100, 100),
      ],
    };

    const value1 = engine.evaluateProperty(property, 50);
    const value2 = engine.evaluateProperty(property, 50);
    const value3 = engine.evaluateProperty(property, 50);

    expect(value1).toBe(value2);
    expect(value2).toBe(value3);
    expect(value1).toBeCloseTo(50, 5);
  });
});
