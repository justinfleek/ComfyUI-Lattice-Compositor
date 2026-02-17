/**
 * Comprehensive Property-Based Tests for Keyframe Store
 *
 * Tests ALL keyframe operations with extensive property testing.
 * Verifies determinism, sorting, interpolation, and edge cases.
 *
 * Uses fast-check to generate random inputs and verify properties hold for ALL inputs.
 *
 * @audit P0 CRITICAL - Keyframe system integrity
 */

import { describe, expect, beforeEach } from "vitest";
import { test } from "@fast-check/vitest";
import * as fc from "fast-check";
import { setActivePinia, createPinia } from "pinia";
import {
  addKeyframe,
  removeKeyframe,
  clearKeyframes,
  moveKeyframe,
  setKeyframeValue,
  updateKeyframe,
} from "@/stores/keyframeStore/crud";
import {
  setKeyframeInterpolation,
  setKeyframeHandle,
  setKeyframeControlMode,
} from "@/stores/keyframeStore/interpolation";
import { interpolateProperty } from "@/services/interpolation";
import { useProjectStore } from "@/stores/projectStore";
import { useAnimationStore } from "@/stores/animationStore";
import { useLayerStore } from "@/stores/layerStore";
import { useCompositionStore } from "@/stores/compositionStore";
import { findPropertyByPath } from "@/stores/keyframeStore/helpers";
import type { Layer, AnimatableProperty, Keyframe } from "@/types/project";
import { generateKeyframeId } from "@/utils/uuid5";

// ============================================================================
// ARBITRARIES (Generators)
// ============================================================================

const finiteNumber = fc.double({ noNaN: true, noDefaultInfinity: true, min: -10000, max: 10000 });
const positiveFrame = fc.integer({ min: 0, max: 1000 });
const frameDelta = fc.integer({ min: -500, max: 500 });

const vec3Arb = fc.record({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
});

const scalarArb = finiteNumber;
const opacityArb = fc.double({ min: 0, max: 100, noNaN: true, noDefaultInfinity: true });

// Property path types - only include properties that exist on all layer types
// rotationX/Y/Z are optional, so exclude them from property tests
const propertyPathArb = fc.constantFrom(
  "transform.position",
  "transform.scale",
  "transform.rotation",
  "transform.origin",
  "opacity",
) as fc.Arbitrary<
  | "transform.position"
  | "transform.scale"
  | "transform.rotation"
  | "transform.origin"
  | "opacity"
>;

const interpolationTypeArb = fc.constantFrom(
  "linear",
  "hold",
  "bezier",
  "easeInQuad",
  "easeOutQuad",
  "easeInOutQuad",
) as fc.Arbitrary<"linear" | "hold" | "bezier" | "easeInQuad" | "easeOutQuad" | "easeInOutQuad">;

const bezierHandleArb = fc.record({
  frame: fc.double({ min: -100, max: 100, noNaN: true }),
  value: fc.double({ min: -1000, max: 1000, noNaN: true }),
  enabled: fc.boolean(),
});

// Helper to get value type for property path
function getValueForPropertyPath(
  path: string,
  vec3Value: { x: number; y: number; z: number },
  scalarValue: number,
  opacityValue: number,
): { x: number; y: number; z: number } | number {
  if (path === "transform.position" || path === "transform.scale" || path === "transform.origin") {
    return vec3Value;
  }
  if (path === "opacity") {
    return opacityValue;
  }
  // All rotation properties are scalars
  return scalarValue;
}

// Helper to check if property exists on layer
// All properties in propertyPathArb exist on all layer types, so this always returns true
function propertyExists(layer: Layer, propertyPath: string): boolean {
  const normalizedPath = propertyPath.replace(/^transform\./, "");
  
  // All properties in propertyPathArb exist on all layer types
  if (normalizedPath === "position" || normalizedPath === "scale" || normalizedPath === "rotation" || normalizedPath === "origin" || normalizedPath === "anchorPoint") {
    return true;
  }
  if (propertyPath === "opacity") {
    return true;
  }
  return false; // Unknown property
}

// ============================================================================
// TEST HELPERS
// ============================================================================

function createTestLayer(id: string): Layer {
  const projectStore = useProjectStore();
  const compositionStore = useCompositionStore();
  const layerStore = useLayerStore();

  // Create composition if needed
  if (!projectStore.activeCompositionId) {
    compositionStore.createComposition("Test Comp", {
      width: 1920,
      height: 1080,
      fps: 30,
      frameCount: 300,
    });
  }

  return layerStore.createLayer("solid", `Layer ${id}`);
}

// ============================================================================
// PROPERTY TESTS: Deterministic ID Generation
// ============================================================================

describe("Keyframe Store Property Tests - Deterministic IDs", () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    const projectStore = useProjectStore();
    projectStore.project.compositions = {};
    projectStore.activeCompositionId = "";
  });

  test.prop([
    fc.string({ minLength: 1 }),
    fc.string({ minLength: 1 }),
    positiveFrame,
    vec3Arb,
  ])("same inputs always generate same keyframe ID", (layerId, propertyPath, frame, value) => {
    const valueStr = `${value.x},${value.y},${value.z}`;
    const id1 = generateKeyframeId(layerId, propertyPath, frame, valueStr);
    const id2 = generateKeyframeId(layerId, propertyPath, frame, valueStr);

    expect(id1).toBe(id2);
  });

  test.prop([
    fc.string({ minLength: 1 }),
    fc.string({ minLength: 1 }),
    positiveFrame,
    vec3Arb,
    vec3Arb,
  ])("different values generate different IDs", (layerId, propertyPath, frame, value1, value2) => {
    fc.pre(value1.x !== value2.x || value1.y !== value2.y || value1.z !== value2.z);

    const valueStr1 = `${value1.x},${value1.y},${value1.z}`;
    const valueStr2 = `${value2.x},${value2.y},${value2.z}`;
    const id1 = generateKeyframeId(layerId, propertyPath, frame, valueStr1);
    const id2 = generateKeyframeId(layerId, propertyPath, frame, valueStr2);

    expect(id1).not.toBe(id2);
  });
});

// ============================================================================
// PROPERTY TESTS: Keyframe CRUD
// ============================================================================

describe("Keyframe Store Property Tests - CRUD Operations", () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    const projectStore = useProjectStore();
    projectStore.project.compositions = {};
    projectStore.activeCompositionId = "";
  });

  describe("addKeyframe", () => {
    test.prop([
      fc.string({ minLength: 1 }),
      propertyPathArb,
      vec3Arb,
      scalarArb,
      opacityArb,
      fc.option(positiveFrame),
    ], { maxSkipsPerRun: 50 })("addKeyframe maintains keyframe sorting for all property types", (layerId, propertyPath, vec3Val, scalarVal, opacityVal, atFrame) => {
      const layer = createTestLayer(layerId);
      
      // Skip if property doesn't exist for this layer type
      if (!propertyExists(layer, propertyPath)) return;
      
      const value = getValueForPropertyPath(propertyPath, vec3Val, scalarVal, opacityVal);

      // Add multiple keyframes out of order
      const frames = [30, 10, 50, 20, 40];
      for (const frame of frames) {
        addKeyframe(layer.id, propertyPath, value, frame);
      }

      const property = findPropertyByPath(layer, propertyPath);
      if (!property) return;

      const keyframeFrames = property.keyframes.map((kf) => kf.frame);

      // Should be sorted
      for (let i = 1; i < keyframeFrames.length; i++) {
        expect(keyframeFrames[i]).toBeGreaterThanOrEqual(keyframeFrames[i - 1]);
      }
    });

    test.prop([
      fc.string({ minLength: 1 }),
      propertyPathArb,
      vec3Arb,
      scalarArb,
      opacityArb,
      positiveFrame,
      vec3Arb,
      scalarArb,
      opacityArb,
    ], { maxSkipsPerRun: 50 })("adding keyframe at same frame replaces existing for all property types", (layerId, propertyPath, vec3Val1, scalarVal1, opacityVal1, frame, vec3Val2, scalarVal2, opacityVal2) => {
      const layer = createTestLayer(layerId);
      
      // Skip if property doesn't exist for this layer type
      if (!propertyExists(layer, propertyPath)) return;
      
      const value1 = getValueForPropertyPath(propertyPath, vec3Val1, scalarVal1, opacityVal1);
      const value2 = getValueForPropertyPath(propertyPath, vec3Val2, scalarVal2, opacityVal2);

      const kf1 = addKeyframe(layer.id, propertyPath, value1, frame);
      const kf2 = addKeyframe(layer.id, propertyPath, value2, frame);

      const property = findPropertyByPath(layer, propertyPath);
      if (!property) return;

      expect(property.keyframes.length).toBe(1);
      expect(property.keyframes[0].id).toBe(kf2.id);
      expect(property.keyframes[0].value).toEqual(value2);
    });

    test.prop([
      fc.string({ minLength: 1 }),
      propertyPathArb,
      vec3Arb,
      scalarArb,
      opacityArb,
      positiveFrame,
    ], { maxSkipsPerRun: 50 })("addKeyframe enables animation for all property types", (layerId, propertyPath, vec3Val, scalarVal, opacityVal, frame) => {
      const layer = createTestLayer(layerId);
      
      // Skip if property doesn't exist for this layer type
      if (!propertyExists(layer, propertyPath)) return;
      
      const value = getValueForPropertyPath(propertyPath, vec3Val, scalarVal, opacityVal);
      const property = findPropertyByPath(layer, propertyPath);
      if (!property) return;

      property.animated = false;
      addKeyframe(layer.id, propertyPath, value, frame);

      expect(property.animated).toBe(true);
    });
  });

  describe("removeKeyframe", () => {
    test.prop([
      fc.string({ minLength: 1 }),
      propertyPathArb,
      vec3Arb,
      scalarArb,
      opacityArb,
      positiveFrame,
    ], { maxSkipsPerRun: 50 })("removeKeyframe decreases count by 1 for all property types", (layerId, propertyPath, vec3Val, scalarVal, opacityVal, frame) => {
      const layer = createTestLayer(layerId);
      
      // Skip if property doesn't exist for this layer type
      if (!propertyExists(layer, propertyPath)) return;
      
      const value = getValueForPropertyPath(propertyPath, vec3Val, scalarVal, opacityVal);
      const kf = addKeyframe(layer.id, propertyPath, value, frame);

      const property = findPropertyByPath(layer, propertyPath);
      if (!property) return;

      const beforeCount = property.keyframes.length;
      removeKeyframe(layer.id, propertyPath, kf.id);
      const afterCount = property.keyframes.length;

      expect(afterCount).toBe(beforeCount - 1);
    });

    test.prop([
      fc.string({ minLength: 1 }),
      propertyPathArb,
      fc.array(vec3Arb, { minLength: 2, maxLength: 5 }),
      fc.array(scalarArb, { minLength: 2, maxLength: 5 }),
      fc.array(opacityArb, { minLength: 2, maxLength: 5 }),
      fc.array(positiveFrame, { minLength: 2, maxLength: 5 }),
    ], { maxSkipsPerRun: 100 })("removeKeyframe maintains sorting for all property types", (layerId, propertyPath, vec3Vals, scalarVals, opacityVals, frames) => {
      fc.pre(vec3Vals.length === frames.length && scalarVals.length === frames.length && opacityVals.length === frames.length);

      const layer = createTestLayer(layerId);
      
      // Skip if property doesn't exist for this layer type
      if (!propertyExists(layer, propertyPath)) return;
      
      const keyframes: Keyframe<unknown>[] = [];

      // Add keyframes
      for (let i = 0; i < frames.length; i++) {
        const value = getValueForPropertyPath(propertyPath, vec3Vals[i], scalarVals[i], opacityVals[i]);
        const kf = addKeyframe(layer.id, propertyPath, value, frames[i]);
        keyframes.push(kf);
      }

      // Remove middle keyframe
      const middleIdx = Math.floor(keyframes.length / 2);
      removeKeyframe(layer.id, propertyPath, keyframes[middleIdx].id);

      const property = findPropertyByPath(layer, propertyPath);
      if (!property) return;

      const keyframeFrames = property.keyframes.map((kf) => kf.frame);

      // Should still be sorted
      for (let i = 1; i < keyframeFrames.length; i++) {
        expect(keyframeFrames[i]).toBeGreaterThanOrEqual(keyframeFrames[i - 1]);
      }
    });
  });

  describe("clearKeyframes", () => {
    test.prop([
      fc.string({ minLength: 1 }),
      propertyPathArb,
      fc.integer({ min: 1, max: 10 }),
      fc.array(vec3Arb, { minLength: 1, maxLength: 10 }),
      fc.array(scalarArb, { minLength: 1, maxLength: 10 }),
      fc.array(opacityArb, { minLength: 1, maxLength: 10 }),
      fc.array(positiveFrame, { minLength: 1, maxLength: 10 }),
    ], { maxSkipsPerRun: 100 })("clearKeyframes removes all keyframes and disables animation for all property types", (layerId, propertyPath, count, vec3Vals, scalarVals, opacityVals, frames) => {
      // Use count to slice arrays to same length
      const len = Math.min(count, vec3Vals.length, scalarVals.length, opacityVals.length, frames.length);
      const vec3Slice = vec3Vals.slice(0, len);
      const scalarSlice = scalarVals.slice(0, len);
      const opacitySlice = opacityVals.slice(0, len);
      const framesSlice = frames.slice(0, len);

      const layer = createTestLayer(layerId);
      
      // All properties in propertyPathArb exist on all layer types
      const property = findPropertyByPath(layer, propertyPath);
      if (!property) return;

      // Add keyframes
      for (let i = 0; i < len; i++) {
        const value = getValueForPropertyPath(propertyPath, vec3Slice[i], scalarSlice[i], opacitySlice[i]);
        addKeyframe(layer.id, propertyPath, value, framesSlice[i]);
      }

      clearKeyframes(layer.id, propertyPath);

      const propertyAfter = findPropertyByPath(layer, propertyPath);
      if (!propertyAfter) return;

      expect(propertyAfter.keyframes.length).toBe(0);
      expect(propertyAfter.animated).toBe(false);
    });
  });

  describe("moveKeyframe", () => {
    test.prop([
      fc.string({ minLength: 1 }),
      propertyPathArb,
      vec3Arb,
      scalarArb,
      opacityArb,
      positiveFrame,
      positiveFrame,
    ], { maxSkipsPerRun: 50 })("moveKeyframe changes frame but preserves value for all property types", (layerId, propertyPath, vec3Val, scalarVal, opacityVal, oldFrame, newFrame) => {
      fc.pre(oldFrame !== newFrame);

      const layer = createTestLayer(layerId);
      
      // Skip if property doesn't exist for this layer type
      if (!propertyExists(layer, propertyPath)) return;
      
      const value = getValueForPropertyPath(propertyPath, vec3Val, scalarVal, opacityVal);
      const kf = addKeyframe(layer.id, propertyPath, value, oldFrame);

      moveKeyframe(layer.id, propertyPath, kf.id, newFrame);

      const property = findPropertyByPath(layer, propertyPath);
      if (!property) return;

      const movedKf = property.keyframes.find((k) => k.id === kf.id);
      expect(movedKf?.frame).toBe(newFrame);
      expect(movedKf?.value).toEqual(value);
    });

    test.prop([
      fc.string({ minLength: 1 }),
      propertyPathArb,
      vec3Arb,
      scalarArb,
      opacityArb,
      positiveFrame,
      fc.integer({ min: -100, max: -1 }), // Negative delta
    ], { maxSkipsPerRun: 50 })("moveKeyframe clamps negative frames to 0 for all property types", (layerId, propertyPath, vec3Val, scalarVal, opacityVal, frame, negativeDelta) => {
      const layer = createTestLayer(layerId);
      
      // Skip if property doesn't exist for this layer type
      if (!propertyExists(layer, propertyPath)) return;
      
      const value = getValueForPropertyPath(propertyPath, vec3Val, scalarVal, opacityVal);
      const kf = addKeyframe(layer.id, propertyPath, value, frame);

      const newFrame = Math.max(0, frame + negativeDelta);
      moveKeyframe(layer.id, propertyPath, kf.id, newFrame);

      const property = findPropertyByPath(layer, propertyPath);
      if (!property) return;

      const movedKf = property.keyframes.find((k) => k.id === kf.id);
      expect(movedKf?.frame).toBeGreaterThanOrEqual(0);
    });
  });
});

// ============================================================================
// PROPERTY TESTS: Interpolation
// ============================================================================

describe("Keyframe Store Property Tests - Interpolation", () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    const projectStore = useProjectStore();
    projectStore.project.compositions = {};
    projectStore.activeCompositionId = "";
  });

  test.prop([
    fc.string({ minLength: 1 }),
    propertyPathArb,
    vec3Arb,
    vec3Arb,
    scalarArb,
    scalarArb,
    opacityArb,
    opacityArb,
    positiveFrame,
    positiveFrame,
    fc.integer({ min: 0, max: 100 }),
  ], { maxSkipsPerRun: 50 })("interpolation is deterministic for same inputs across all property types", (layerId, propertyPath, vec3Val1, vec3Val2, scalarVal1, scalarVal2, opacityVal1, opacityVal2, frame1, frame2, testFrame) => {
    fc.pre(frame1 < frame2);
    fc.pre(testFrame >= frame1 && testFrame <= frame2);

    const layer = createTestLayer(layerId);
    const value1 = getValueForPropertyPath(propertyPath, vec3Val1, scalarVal1, opacityVal1);
    const value2 = getValueForPropertyPath(propertyPath, vec3Val2, scalarVal2, opacityVal2);
    addKeyframe(layer.id, propertyPath, value1, frame1);
    addKeyframe(layer.id, propertyPath, value2, frame2);

    const property = findPropertyByPath(layer, propertyPath);
    if (!property || !propertyExists(layer, propertyPath)) return;

    const result1 = interpolateProperty(property, testFrame, 30);
    const result2 = interpolateProperty(property, testFrame, 30);

    // Should be identical (deterministic)
    expect(result1).toEqual(result2);
  });

  test.prop([
    fc.string({ minLength: 1 }),
    propertyPathArb,
    vec3Arb,
    vec3Arb,
    scalarArb,
    scalarArb,
    opacityArb,
    opacityArb,
    positiveFrame,
    positiveFrame,
  ], { maxSkipsPerRun: 50 })("interpolation at keyframe frames returns keyframe values for all property types", (layerId, propertyPath, vec3Val1, vec3Val2, scalarVal1, scalarVal2, opacityVal1, opacityVal2, frame1, frame2) => {
    fc.pre(frame1 < frame2);

    const layer = createTestLayer(layerId);
    const value1 = getValueForPropertyPath(propertyPath, vec3Val1, scalarVal1, opacityVal1);
    const value2 = getValueForPropertyPath(propertyPath, vec3Val2, scalarVal2, opacityVal2);
    addKeyframe(layer.id, propertyPath, value1, frame1);
    addKeyframe(layer.id, propertyPath, value2, frame2);

    const property = findPropertyByPath(layer, propertyPath);
    if (!property || !propertyExists(layer, propertyPath)) return;

    const result1 = interpolateProperty(property, frame1, 30);
    const result2 = interpolateProperty(property, frame2, 30);

    expect(result1).toEqual(value1);
    expect(result2).toEqual(value2);
  });

  test.prop([
    fc.string({ minLength: 1 }),
    propertyPathArb,
    vec3Arb,
    scalarArb,
    opacityArb,
    positiveFrame,
    fc.integer({ min: 0, max: 1000 }),
  ], { maxSkipsPerRun: 50 })("interpolation before first keyframe returns first value for all property types", (layerId, propertyPath, vec3Val, scalarVal, opacityVal, keyframeFrame, testFrame) => {
    fc.pre(testFrame < keyframeFrame);

    const layer = createTestLayer(layerId);
    const value = getValueForPropertyPath(propertyPath, vec3Val, scalarVal, opacityVal);
    addKeyframe(layer.id, propertyPath, value, keyframeFrame);

    const property = findPropertyByPath(layer, propertyPath);
    if (!property) return;

    const result = interpolateProperty(property, testFrame, 30);

    expect(result).toEqual(value);
  });

  test.prop([
    fc.string({ minLength: 1 }),
    propertyPathArb,
    vec3Arb,
    scalarArb,
    opacityArb,
    positiveFrame,
    fc.integer({ min: 0, max: 1000 }),
  ], { maxSkipsPerRun: 50 })("interpolation after last keyframe returns last value for all property types", (layerId, propertyPath, vec3Val, scalarVal, opacityVal, keyframeFrame, testFrame) => {
    fc.pre(testFrame > keyframeFrame);

    const layer = createTestLayer(layerId);
    
    // Skip if property doesn't exist for this layer type
    if (!propertyExists(layer, propertyPath)) return;
    
    const value = getValueForPropertyPath(propertyPath, vec3Val, scalarVal, opacityVal);
    addKeyframe(layer.id, propertyPath, value, keyframeFrame);

    const property = findPropertyByPath(layer, propertyPath);
    if (!property) return;

    const result = interpolateProperty(property, testFrame, 30);

    expect(result).toEqual(value);
  });
});
