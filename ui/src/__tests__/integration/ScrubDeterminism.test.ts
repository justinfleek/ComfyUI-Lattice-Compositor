/**
 * Scrub Determinism Integration Tests
 *
 * These tests verify that the rendering pipeline produces identical results
 * regardless of the order in which frames are evaluated (scrub order).
 *
 * AXIOM 4: Scrub-Independence
 * evaluate(N) must return identical results whether reached via:
 * - Direct: evaluate(N)
 * - Forward: evaluate(0) → evaluate(1) → ... → evaluate(N)
 * - Backward: evaluate(M) → evaluate(N) where M > N
 * - Random: Any arbitrary sequence ending at N
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { MotionEngine, type FrameState, type EvaluatedLayer } from '@/engine/MotionEngine';
import type { WeylProject, Layer, Keyframe, AnimatableProperty } from '@/types/project';
import { createEmptyProject, createDefaultTransform } from '@/types/project';

// ============================================================================
// TEST UTILITIES
// ============================================================================

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

  // Animate rotation
  transform.rotation.animated = true;
  transform.rotation.keyframes = [
    createKeyframe(10, 0, 0),
    createKeyframe(11, 80, 360),
  ];

  return transform;
}

/**
 * Create a minimal test project with animated layers
 */
function createTestProject(): WeylProject {
  const project = createEmptyProject(1920, 1080);

  // Add a layer with animated properties
  const layer: Layer = {
    id: 'test-layer-1',
    name: 'Test Layer',
    type: 'solid',
    visible: true,
    locked: false,
    isolate: false,
    threeD: false,
    motionBlur: false,
    startFrame: 0,
    endFrame: 80,
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

/**
 * Compare two FrameStates for exact equality
 */
function frameStatesEqual(a: FrameState, b: FrameState): boolean {
  if (a.frame !== b.frame) return false;
  if (a.layers.length !== b.layers.length) return false;

  for (let i = 0; i < a.layers.length; i++) {
    if (!evaluatedLayersEqual(a.layers[i], b.layers[i])) {
      return false;
    }
  }

  return true;
}

/**
 * Compare two EvaluatedLayers for exact equality
 */
function evaluatedLayersEqual(a: EvaluatedLayer, b: EvaluatedLayer): boolean {
  if (a.id !== b.id) return false;
  if (a.visible !== b.visible) return false;
  if (Math.abs(a.opacity - b.opacity) > 0.0001) return false;

  // Compare transform
  const ta = a.transform;
  const tb = b.transform;

  if (Math.abs(ta.position.x - tb.position.x) > 0.0001) return false;
  if (Math.abs(ta.position.y - tb.position.y) > 0.0001) return false;
  if (Math.abs((ta.position.z ?? 0) - (tb.position.z ?? 0)) > 0.0001) return false;

  if (Math.abs(ta.scale.x - tb.scale.x) > 0.0001) return false;
  if (Math.abs(ta.scale.y - tb.scale.y) > 0.0001) return false;

  if (Math.abs(ta.rotation - tb.rotation) > 0.0001) return false;

  return true;
}

// ============================================================================
// MOTION ENGINE DETERMINISM TESTS
// ============================================================================

describe('MotionEngine Scrub Determinism', () => {
  let motionEngine: MotionEngine;
  let project: WeylProject;

  beforeEach(() => {
    motionEngine = new MotionEngine();
    project = createTestProject();
  });

  describe('Direct vs Sequential Evaluation', () => {
    it('should produce identical results for frame 40 via direct access', () => {
      // Direct evaluation
      const directResult = motionEngine.evaluate(40, project, null, null);

      // Sequential from 0
      for (let f = 0; f < 40; f++) {
        motionEngine.evaluate(f, project, null, null);
      }
      const sequentialResult = motionEngine.evaluate(40, project, null, null);

      expect(frameStatesEqual(directResult, sequentialResult)).toBe(true);
    });

    it('should produce identical results for frame 60 via different paths', () => {
      // Path 1: Direct
      const direct = motionEngine.evaluate(60, project, null, null);

      // Path 2: 0 → 30 → 60
      motionEngine.evaluate(0, project, null, null);
      motionEngine.evaluate(30, project, null, null);
      const stepped = motionEngine.evaluate(60, project, null, null);

      expect(frameStatesEqual(direct, stepped)).toBe(true);
    });
  });

  describe('Backward Scrub', () => {
    it('should produce identical results when scrubbing backward', () => {
      // First, evaluate frame 30 directly
      const frame30_direct = motionEngine.evaluate(30, project, null, null);

      // Then evaluate frame 60, then back to 30
      motionEngine.evaluate(60, project, null, null);
      const frame30_after_60 = motionEngine.evaluate(30, project, null, null);

      expect(frameStatesEqual(frame30_direct, frame30_after_60)).toBe(true);
    });

    it('should handle scrubbing from end to beginning', () => {
      // Evaluate frame 0 directly
      const frame0_direct = motionEngine.evaluate(0, project, null, null);

      // Evaluate all frames forward, then back to 0
      for (let f = 0; f <= 80; f++) {
        motionEngine.evaluate(f, project, null, null);
      }
      const frame0_after_full = motionEngine.evaluate(0, project, null, null);

      expect(frameStatesEqual(frame0_direct, frame0_after_full)).toBe(true);
    });
  });

  describe('Random Scrub Patterns', () => {
    it('should produce identical results with random access pattern', () => {
      const frames = [45, 15, 72, 30, 5, 60, 40, 80, 0, 20];
      const results = new Map<number, FrameState>();

      // First pass: random order
      for (const frame of frames) {
        results.set(frame, motionEngine.evaluate(frame, project, null, null));
      }

      // Second pass: reversed order, compare results
      const reversedFrames = [...frames].reverse();
      for (const frame of reversedFrames) {
        const newResult = motionEngine.evaluate(frame, project, null, null);
        const originalResult = results.get(frame)!;

        expect(frameStatesEqual(newResult, originalResult)).toBe(true);
      }
    });

    it('should handle rapid back-and-forth scrubbing', () => {
      const frame40_baseline = motionEngine.evaluate(40, project, null, null);

      // Rapid back and forth
      for (let i = 0; i < 10; i++) {
        motionEngine.evaluate(60, project, null, null);
        motionEngine.evaluate(20, project, null, null);
        motionEngine.evaluate(70, project, null, null);
        motionEngine.evaluate(10, project, null, null);
      }

      const frame40_after_chaos = motionEngine.evaluate(40, project, null, null);

      expect(frameStatesEqual(frame40_baseline, frame40_after_chaos)).toBe(true);
    });
  });

  describe('Interpolation Consistency', () => {
    it('should interpolate position linearly', () => {
      // Frame 20 should be 50% between frame 0 and frame 40
      const frame20 = motionEngine.evaluate(20, project, null, null);

      // Find the layer (may be filtered based on visibility)
      const layer = frame20.layers.find(l => l.id === 'test-layer-1');
      expect(layer).toBeDefined();

      if (layer) {
        // Position at frame 0: (0, 0), frame 40: (500, 300)
        // Frame 20 (50% of 0-40): (250, 150)
        expect(layer.transform.position.x).toBeCloseTo(250, 1);
        expect(layer.transform.position.y).toBeCloseTo(150, 1);
      }
    });

    it('should interpolate rotation linearly', () => {
      // Frame 40 should be 50% of rotation (180 degrees)
      const frame40 = motionEngine.evaluate(40, project, null, null);

      const layer = frame40.layers.find(l => l.id === 'test-layer-1');
      expect(layer).toBeDefined();

      if (layer) {
        // Rotation at frame 0: 0, frame 80: 360
        // Frame 40 (50%): 180
        expect(layer.transform.rotation).toBeCloseTo(180, 1);
      }
    });
  });

  describe('Multiple Instances', () => {
    it('should produce identical results from separate engine instances', () => {
      const engine1 = new MotionEngine();
      const engine2 = new MotionEngine();

      const frames = [0, 20, 40, 60, 80];

      for (const frame of frames) {
        const result1 = engine1.evaluate(frame, project, null, null);
        const result2 = engine2.evaluate(frame, project, null, null);

        expect(frameStatesEqual(result1, result2)).toBe(true);
      }
    });
  });
});

// ============================================================================
// FULL PIPELINE DETERMINISM (Future Integration)
// ============================================================================

describe('Full Pipeline Determinism', () => {
  it('should maintain determinism through complete evaluation chain', () => {
    const motionEngine = new MotionEngine();
    const project = createTestProject();

    // Simulate full pipeline: evaluate → apply → re-evaluate
    const targetFrames = [10, 30, 50, 70];
    const results: FrameState[] = [];

    // First pass
    for (const frame of targetFrames) {
      results.push(motionEngine.evaluate(frame, project, null, null));
    }

    // Second pass (different order)
    for (let i = targetFrames.length - 1; i >= 0; i--) {
      const frame = targetFrames[i];
      const newResult = motionEngine.evaluate(frame, project, null, null);
      expect(frameStatesEqual(newResult, results[i])).toBe(true);
    }
  });
});
