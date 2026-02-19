/**
 * Property-Based Tests for Timewarp, Text Animator, and Audio Keyframes
 *
 * Tests keyframe operations for:
 * - Timewarp speed ramp presets
 * - Text animator keyframes
 * - Audio amplitude keyframes
 *
 * Verifies deterministic ID generation, sorting, interpolation, and edge cases.
 *
 * @audit P0 CRITICAL - Keyframe system integrity for specialized systems
 */

import { describe, expect, beforeEach } from "vitest";
import { test } from "@fast-check/vitest";
import * as fc from "fast-check";
import { setActivePinia, createPinia } from "pinia";
import { useProjectStore } from "@/stores/projectStore";
import { useCompositionStore } from "@/stores/compositionStore";
import { useLayerStore } from "@/stores/layerStore";
import { createLayer } from "@/stores/layerStore/crud";
import { generateKeyframeId } from "@/utils/uuid5";
import { createSpeedRampPreset } from "@/services/timewarp";
import type { Layer } from "@/types/project";
import { createTextAnimator, createAnimatablePropWithKeyframes } from "@/services/textAnimator";
import { createAmplitudeProperty } from "@/stores/audioKeyframeStore";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

const positiveFrame = fc.integer({ min: 0, max: 1000 });
const durationArb = fc.integer({ min: 30, max: 300 });

// ════════════════════════════════════════════════════════════════════════════
//                                                           // test // helpers
// ════════════════════════════════════════════════════════════════════════════

function createTestLayer(type: Layer["type"]): Layer {
  const projectStore = useProjectStore();
  const compositionStore = useCompositionStore();

  if (!projectStore.activeCompositionId) {
    compositionStore.createComposition("Test Comp", {
      width: 1920,
      height: 1080,
      fps: 30,
      frameCount: 300,
    });
  }

  return createLayer(type, `Test ${type} Layer`);
}

// ════════════════════════════════════════════════════════════════════════════
//                                                         // property // tests
// ════════════════════════════════════════════════════════════════════════════

describe("Keyframe Store Property Tests - Timewarp Speed Ramps", () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    const projectStore = useProjectStore();
    projectStore.project.compositions = {};
    projectStore.activeCompositionId = "";
  });

  test.prop([
    fc.constantFrom("slow-fast", "fast-slow", "slow-fast-slow", "impact", "rewind"),
    positiveFrame,
    durationArb,
  ])("timewarp speed ramp preset keyframes use deterministic IDs", (preset, startFrame, duration) => {
    const layer = createTestLayer("video");
    const property = createSpeedRampPreset(preset, layer.id, startFrame, duration, 30);

    expect(property.keyframes.length).toBeGreaterThan(0);
    
    // Verify all keyframes have deterministic IDs
    for (const kf of property.keyframes) {
      const valueStr = String(kf.value);
      const propertyPath = "timewarp.speed";
      const expectedId = generateKeyframeId(layer.id, propertyPath, kf.frame, valueStr);
      expect(kf.id).toBe(expectedId);
    }
  });

  test.prop([
    fc.constantFrom("slow-fast", "fast-slow", "slow-fast-slow", "impact", "rewind"),
    positiveFrame,
    durationArb,
  ])("timewarp speed ramp preset keyframes are sorted", (preset, startFrame, duration) => {
    const layer = createTestLayer("video");
    const property = createSpeedRampPreset(preset, layer.id, startFrame, duration, 30);

    const frames = property.keyframes.map((kf) => kf.frame);
    
    // Should be sorted
    for (let i = 1; i < frames.length; i++) {
      expect(frames[i]).toBeGreaterThanOrEqual(frames[i - 1]);
    }
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                         // property // tests
// ════════════════════════════════════════════════════════════════════════════

describe("Keyframe Store Property Tests - Text Animator", () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    const projectStore = useProjectStore();
    projectStore.project.compositions = {};
    projectStore.activeCompositionId = "";
  });

  test.prop([
    fc.string({ minLength: 1 }),
    positiveFrame,
    positiveFrame,
  ])("text animator keyframes use deterministic IDs when layerId provided", (animatorName, frame1, frame2) => {
    fc.pre(frame1 !== frame2);

    const layer = createTestLayer("text");
    const animator = createTextAnimator(animatorName, layer.id);
    const property = createAnimatablePropWithKeyframes(
      0,
      "Start",
      [
        { frame: frame1, value: 0 },
        { frame: frame2, value: 100 },
      ],
      "number",
      layer.id,
      animator.id,
    );

    expect(property.keyframes.length).toBeGreaterThan(0);
    
    // Verify all keyframes have deterministic IDs
    for (const kf of property.keyframes) {
      const valueStr = String(kf.value);
      const propertyPath = `textAnimator.${animator.id}.Start`;
      const expectedId = generateKeyframeId(layer.id, propertyPath, kf.frame, valueStr);
      expect(kf.id).toBe(expectedId);
    }
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                         // property // tests
// ════════════════════════════════════════════════════════════════════════════

describe("Keyframe Store Property Tests - Audio Keyframes", () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    const projectStore = useProjectStore();
    projectStore.project.compositions = {};
    projectStore.activeCompositionId = "";
  });

  test.prop([
    fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: 1, maxLength: 100 }),
    fc.double({ min: 1, max: 200, noNaN: true, noDefaultInfinity: true }),
  ])("audio amplitude keyframes use deterministic IDs", (amplitudes, scale) => {
    const layer = createTestLayer("null");
    const property = createAmplitudeProperty("Test Channel", amplitudes, scale, layer.id);

    expect(property.keyframes.length).toBe(amplitudes.length);
    
    // Verify all keyframes have deterministic IDs
    for (let i = 0; i < property.keyframes.length; i++) {
      const kf = property.keyframes[i];
      const valueStr = String(kf.value);
      const propertyPath = `audioAmplitude.Test Channel`;
      const expectedId = generateKeyframeId(layer.id, propertyPath, kf.frame, valueStr);
      expect(kf.id).toBe(expectedId);
    }
  });

  test.prop([
    fc.array(fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }), { minLength: 1, maxLength: 100 }),
    fc.double({ min: 1, max: 200, noNaN: true, noDefaultInfinity: true }),
  ])("audio amplitude keyframes are sorted", (amplitudes, scale) => {
    const layer = createTestLayer("null");
    const property = createAmplitudeProperty("Test Channel", amplitudes, scale, layer.id);

    const frames = property.keyframes.map((kf) => kf.frame);
    
    // Should be sorted (frame = index)
    for (let i = 1; i < frames.length; i++) {
      expect(frames[i]).toBeGreaterThanOrEqual(frames[i - 1]);
    }
  });
});
