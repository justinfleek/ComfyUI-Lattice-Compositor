/**
 * Property-Based Tests for keyframeActions.ts
 *
 * Tests the invariants and contracts of keyframe manipulation functions.
 * Uses fast-check to generate random inputs and verify properties hold for ALL inputs.
 *
 * @audit P0 CRITICAL - Animation integrity
 */
import { describe, expect, beforeEach, it } from "vitest";
import { test } from "@fast-check/vitest";
import * as fc from "fast-check";
import { moveKeyframes, moveKeyframe, addKeyframe, clearKeyframes } from "@/stores/keyframeStore/crud";
import type { KeyframeStoreAccess as KeyframeStore } from "@/stores/keyframeStore/types";
import {
  separatePositionDimensions,
  linkPositionDimensions,
  separateScaleDimensions,
  linkScaleDimensions,
} from "@/types/transform";
import type {
  Layer,
  AnimatableProperty,
  Keyframe,
  Composition,
} from "@/types/project";

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

const interpolationTypeArb = fc.constantFrom(
  "linear",
  "hold",
  "bezier",
) as fc.Arbitrary<"linear" | "hold" | "bezier">;

const bezierHandleArb = fc.record({
  frame: fc.double({ min: -100, max: 100, noNaN: true }),
  value: fc.double({ min: -1000, max: 1000, noNaN: true }),
  enabled: fc.boolean(),
});

function keyframeArb<T>(valueArb: fc.Arbitrary<T>): fc.Arbitrary<Keyframe<T>> {
  return fc.record({
    id: fc.uuid(),
    frame: positiveFrame,
    value: valueArb,
    interpolation: interpolationTypeArb,
    outHandle: bezierHandleArb,
    inHandle: bezierHandleArb,
    controlMode: fc.constantFrom("smooth", "corner", "symmetric") as fc.Arbitrary<"smooth" | "corner" | "symmetric">,
  });
}

// Generate sorted keyframes with unique frames
function sortedKeyframesArb<T>(
  valueArb: fc.Arbitrary<T>,
  minCount: number = 0,
  maxCount: number = 10,
): fc.Arbitrary<Keyframe<T>[]> {
  return fc
    .array(keyframeArb(valueArb), { minLength: minCount, maxLength: maxCount })
    .map((kfs) => {
      // Sort by frame and ensure no duplicates
      const sorted = [...kfs].sort((a, b) => a.frame - b.frame);
      const seen = new Set<number>();
      return sorted.filter((kf) => {
        if (seen.has(kf.frame)) return false;
        seen.add(kf.frame);
        return true;
      });
    });
}

// ============================================================================
// TEST HELPERS
// ============================================================================

function createAnimatableProperty<T>(
  name: string,
  value: T,
  keyframes: Keyframe<T>[] = [],
): AnimatableProperty<T> {
  return {
    id: `prop-${name}`,
    name,
    type: "number" as any,
    value,
    animated: keyframes.length > 0,
    keyframes,
  };
}

function createMockLayer(
  id: string,
  positionKeyframes: Keyframe<{ x: number; y: number; z: number }>[] = [],
  scaleKeyframes: Keyframe<{ x: number; y: number; z: number }>[] = [],
): Layer {
  // Use unknown intermediate to avoid TypeScript strict checks on optional fields
  const layer = {
    id,
    name: `Layer ${id}`,
    type: "solid" as const,
    visible: true,
    locked: false,
    solo: false,
    shy: false,
    startFrame: 0,
    endFrame: 1000,
    inPoint: 0,
    outPoint: 1000,
    blendMode: "normal" as const,
    threeD: false,
    opacity: createAnimatableProperty("Opacity", 100),
    transform: {
      position: createAnimatableProperty("Position", { x: 0, y: 0, z: 0 }, positionKeyframes),
      scale: createAnimatableProperty("Scale", { x: 100, y: 100, z: 100 }, scaleKeyframes),
      rotation: createAnimatableProperty("Rotation", 0),
      origin: createAnimatableProperty("Origin", { x: 0, y: 0, z: 0 }),
    },
    effects: [],
    properties: [],
    parentId: null,
    data: { color: "#ff0000", width: 1920, height: 1080 },
  };
  return layer as unknown as Layer;
}

function createMockStore(layers: Layer[]): KeyframeStore {
  const comp: Composition = {
    id: "main",
    name: "Main Comp",
    settings: {
      width: 1920,
      height: 1080,
      frameCount: 300,
      fps: 30,
      duration: 10,
      backgroundColor: "#000000",
      autoResizeToContent: false,
      frameBlendingEnabled: false,
    },
    layers,
    currentFrame: 0,
    isNestedComp: false,
    markers: [],
  };

  return {
    project: {
      id: "test-project",
      name: "Test Project",
      version: "1.0.0",
      meta: {
        created: new Date().toISOString(),
        modified: new Date().toISOString(),
        author: "test",
        description: "Test project",
      },
      assets: [],
      compositions: [comp],
      activeCompositionId: "main",
    },
    currentFrame: 0,
    selectedLayerIds: [],
    getActiveComp() {
      return comp;
    },
    getActiveCompLayers() {
      return layers;
    },
    getLayerById(id: string) {
      return layers.find((l) => l.id === id) || null;
    },
    pushHistory() {},
  } as KeyframeStore;
}

// ============================================================================
// PROPERTY TESTS: moveKeyframes (bulk)
// ============================================================================

describe("moveKeyframes Property Tests", () => {
  describe("Invariant: Relative positions preserved", () => {
    test.prop([
      // Generate 2-5 keyframes
      sortedKeyframesArb(vec3Arb, 2, 5),
      frameDelta,
    ])("moving keyframes preserves relative frame distances (when not hitting floor)", (keyframes, delta) => {
      fc.pre(keyframes.length >= 2);

      // Only test when no keyframes would hit the floor (frame 0)
      // When keyframes clamp to 0, relative distances collapse - that's expected behavior
      const minFrame = Math.min(...keyframes.map(kf => kf.frame));
      fc.pre(minFrame + delta >= 0);

      const layer = createMockLayer("layer1", keyframes);
      const store = createMockStore([layer]);

      // Record original relative positions
      const originalRelatives: number[] = [];
      for (let i = 1; i < keyframes.length; i++) {
        originalRelatives.push(keyframes[i].frame - keyframes[i - 1].frame);
      }

      // Build keyframes array for bulk move
      const keyframesToMove = keyframes.map((kf) => ({
        layerId: "layer1",
        propertyPath: "transform.position",
        keyframeId: kf.id,
      }));

      // Move all keyframes
      moveKeyframes(store, keyframesToMove, delta);

      // Get updated keyframes
      const updatedKeyframes = layer.transform.position.keyframes;

      // Verify relative positions are preserved
      const newRelatives: number[] = [];
      for (let i = 1; i < updatedKeyframes.length; i++) {
        newRelatives.push(updatedKeyframes[i].frame - updatedKeyframes[i - 1].frame);
      }

      // Relative distances should be unchanged
      for (let i = 0; i < originalRelatives.length && i < newRelatives.length; i++) {
        expect(newRelatives[i]).toBe(originalRelatives[i]);
      }
    });
  });

  describe("Invariant: Floor clamping behavior", () => {
    test.prop([
      sortedKeyframesArb(vec3Arb, 2, 5),
      fc.integer({ min: -2000, max: -1 }), // Always negative delta
    ])("when keyframes hit floor, they clamp to 0 without going negative", (keyframes, delta) => {
      fc.pre(keyframes.length >= 2);

      // Ensure at least one keyframe would go below 0
      const minFrame = Math.min(...keyframes.map(kf => kf.frame));
      fc.pre(minFrame + delta < 0);

      const layer = createMockLayer("layer1", keyframes);
      const store = createMockStore([layer]);

      const keyframesToMove = keyframes.map((kf) => ({
        layerId: "layer1",
        propertyPath: "transform.position",
        keyframeId: kf.id,
      }));

      moveKeyframes(store, keyframesToMove, delta);

      const updatedKeyframes = layer.transform.position.keyframes;

      // All frames should be >= 0
      for (const kf of updatedKeyframes) {
        expect(kf.frame).toBeGreaterThanOrEqual(0);
      }

      // At least one keyframe should be at 0 (the one that hit the floor)
      const framesAt0 = updatedKeyframes.filter(kf => kf.frame === 0);
      expect(framesAt0.length).toBeGreaterThan(0);
    });
  });

  describe("Invariant: Values unchanged", () => {
    test.prop([
      sortedKeyframesArb(vec3Arb, 1, 5),
      frameDelta,
    ])("moving keyframes does not change their values", (keyframes, delta) => {
      fc.pre(keyframes.length >= 1);

      // Verify unique frames in input (generator should ensure this, but fast-check shrinking can violate)
      const inputFrames = keyframes.map((kf) => kf.frame);
      fc.pre(new Set(inputFrames).size === inputFrames.length);

      const layer = createMockLayer("layer1", keyframes);
      const store = createMockStore([layer]);

      // Record original values by keyframe ID (not position, since order/presence can change after collisions)
      const originalValuesById = new Map<string, { x: number; y: number; z: number }>();
      for (const kf of keyframes) {
        originalValuesById.set(kf.id, { x: kf.value.x, y: kf.value.y, z: kf.value.z });
      }

      // Build keyframes array for bulk move
      const keyframesToMove = keyframes.map((kf) => ({
        layerId: "layer1",
        propertyPath: "transform.position",
        keyframeId: kf.id,
      }));

      // Move all keyframes
      moveKeyframes(store, keyframesToMove, delta);

      // Get updated keyframes
      const updatedKeyframes = layer.transform.position.keyframes;

      // Values of surviving keyframes should be unchanged (lookup by ID)
      for (const kf of updatedKeyframes) {
        const originalValue = originalValuesById.get(kf.id);
        if (originalValue) {
          // Use closeTo to handle -0 vs +0 floating point edge cases
          expect(kf.value.x).toBeCloseTo(originalValue.x, 10);
          expect(kf.value.y).toBeCloseTo(originalValue.y, 10);
          expect(kf.value.z).toBeCloseTo(originalValue.z, 10);
        }
      }
    });
  });

  describe("Invariant: Frame non-negative", () => {
    test.prop([
      sortedKeyframesArb(vec3Arb, 1, 5),
      fc.integer({ min: -2000, max: 2000 }),
    ])("keyframe frames are always >= 0 after move", (keyframes, delta) => {
      fc.pre(keyframes.length >= 1);

      const layer = createMockLayer("layer1", keyframes);
      const store = createMockStore([layer]);

      const keyframesToMove = keyframes.map((kf) => ({
        layerId: "layer1",
        propertyPath: "transform.position",
        keyframeId: kf.id,
      }));

      moveKeyframes(store, keyframesToMove, delta);

      const updatedKeyframes = layer.transform.position.keyframes;

      // All frames should be non-negative
      for (const kf of updatedKeyframes) {
        expect(kf.frame).toBeGreaterThanOrEqual(0);
      }
    });
  });

  describe("Invariant: Keyframes remain sorted", () => {
    test.prop([
      sortedKeyframesArb(vec3Arb, 2, 10),
      frameDelta,
    ])("keyframes remain sorted by frame after move", (keyframes, delta) => {
      fc.pre(keyframes.length >= 2);

      const layer = createMockLayer("layer1", keyframes);
      const store = createMockStore([layer]);

      const keyframesToMove = keyframes.map((kf) => ({
        layerId: "layer1",
        propertyPath: "transform.position",
        keyframeId: kf.id,
      }));

      moveKeyframes(store, keyframesToMove, delta);

      const updatedKeyframes = layer.transform.position.keyframes;

      // Keyframes should be sorted by frame
      for (let i = 1; i < updatedKeyframes.length; i++) {
        expect(updatedKeyframes[i].frame).toBeGreaterThanOrEqual(updatedKeyframes[i - 1].frame);
      }
    });
  });

  describe("Invariant: Delta of 0 is identity", () => {
    test.prop([sortedKeyframesArb(vec3Arb, 1, 5)])("moving by 0 does not change keyframes", (keyframes) => {
      fc.pre(keyframes.length >= 1);

      const layer = createMockLayer("layer1", keyframes);
      const store = createMockStore([layer]);

      // Record original frames
      const originalFrames = keyframes.map((kf) => kf.frame);

      const keyframesToMove = keyframes.map((kf) => ({
        layerId: "layer1",
        propertyPath: "transform.position",
        keyframeId: kf.id,
      }));

      // Move by 0
      moveKeyframes(store, keyframesToMove, 0);

      const updatedKeyframes = layer.transform.position.keyframes;

      // Frames should be unchanged
      for (let i = 0; i < originalFrames.length && i < updatedKeyframes.length; i++) {
        expect(updatedKeyframes[i].frame).toBe(originalFrames[i]);
      }
    });
  });

  describe("Invariant: Keyframe count and collision handling", () => {
    test.prop([
      sortedKeyframesArb(vec3Arb, 0, 10),
      frameDelta,
    ])("count preserved when no collisions occur", (keyframes, delta) => {
      // Skip empty arrays
      fc.pre(keyframes.length >= 1);

      // Verify unique frames in input (generator should ensure this, but fast-check shrinking can violate)
      const inputFrames = keyframes.map((kf) => kf.frame);
      const uniqueInputFrames = new Set(inputFrames);
      fc.pre(uniqueInputFrames.size === inputFrames.length);

      // Calculate target frames and check for collisions
      const targetFrames = keyframes.map((kf) => Math.max(0, kf.frame + delta));
      const uniqueTargetFrames = new Set(targetFrames);

      // Only expect count preservation if target frames are also unique
      // (collisions can happen when negative delta clamps multiple frames to 0)
      const expectCollisions = uniqueTargetFrames.size < targetFrames.length;

      const layer = createMockLayer("layer1", keyframes);
      const store = createMockStore([layer]);

      const keyframesToMove = keyframes.map((kf) => ({
        layerId: "layer1",
        propertyPath: "transform.position",
        keyframeId: kf.id,
      }));

      moveKeyframes(store, keyframesToMove, delta);

      if (expectCollisions) {
        // When collisions occur, count should equal number of unique target frames
        expect(layer.transform.position.keyframes.length).toBe(uniqueTargetFrames.size);
      } else {
        // When no collisions, count should be preserved
        expect(layer.transform.position.keyframes.length).toBe(keyframes.length);
      }
    });

    test.prop([
      sortedKeyframesArb(vec3Arb, 2, 5),
      fc.integer({ min: -1000, max: -1 }),  // Always negative delta
    ])("negative delta can cause collisions at frame 0", (keyframes, negativeDelta) => {
      fc.pre(keyframes.length >= 2);

      // Verify unique frames in input
      const inputFrames = keyframes.map((kf) => kf.frame);
      fc.pre(new Set(inputFrames).size === inputFrames.length);

      // Find keyframes that would clamp to 0
      const clampsToZero = keyframes.filter((kf) => kf.frame + negativeDelta < 0);

      // If multiple keyframes clamp to 0, we expect collision
      const expectedCollisions = clampsToZero.length > 1;

      const layer = createMockLayer("layer1", keyframes);
      const store = createMockStore([layer]);

      const keyframesToMove = keyframes.map((kf) => ({
        layerId: "layer1",
        propertyPath: "transform.position",
        keyframeId: kf.id,
      }));

      moveKeyframes(store, keyframesToMove, negativeDelta);

      if (expectedCollisions) {
        // Count should decrease due to frame 0 collisions
        expect(layer.transform.position.keyframes.length).toBeLessThan(keyframes.length);
      }

      // Invariant: all resulting frames must be unique and sorted
      const resultFrames = layer.transform.position.keyframes.map((kf: Keyframe<any>) => kf.frame);
      const uniqueResultFrames = new Set(resultFrames);
      expect(uniqueResultFrames.size).toBe(resultFrames.length);

      // Verify sorted order
      for (let i = 1; i < resultFrames.length; i++) {
        expect(resultFrames[i]).toBeGreaterThan(resultFrames[i - 1]);
      }
    });
  });
});

// ============================================================================
// PROPERTY TESTS: Dimension Separation
// ============================================================================

describe("Dimension Separation Property Tests", () => {
  describe("Position Separation Invariants", () => {
    test.prop([vec3Arb, sortedKeyframesArb(vec3Arb, 0, 5)])(
      "separating position creates X, Y, Z properties with correct current values",
      (currentValue, keyframes) => {
        const layer = createMockLayer("layer1", keyframes);
        layer.transform.position.value = currentValue;

        separatePositionDimensions(layer.transform);

        expect(layer.transform.separateDimensions?.position).toBe(true);
        expect(layer.transform.positionX).toBeDefined();
        expect(layer.transform.positionY).toBeDefined();
        expect(layer.transform.positionZ).toBeDefined();
        expect(layer.transform.positionX!.value).toBe(currentValue.x);
        expect(layer.transform.positionY!.value).toBe(currentValue.y);
        expect(layer.transform.positionZ!.value).toBe(currentValue.z);
      }
    );

    test.prop([vec3Arb, sortedKeyframesArb(vec3Arb, 1, 5)])(
      "separating position distributes keyframes to X, Y, Z",
      (currentValue, keyframes) => {
        fc.pre(keyframes.length >= 1);

        const layer = createMockLayer("layer1", keyframes);
        layer.transform.position.value = currentValue;
        const originalKeyframeCount = keyframes.length;

        separatePositionDimensions(layer.transform);

        // Each dimension should have the same number of keyframes
        expect(layer.transform.positionX!.keyframes.length).toBe(originalKeyframeCount);
        expect(layer.transform.positionY!.keyframes.length).toBe(originalKeyframeCount);
        expect(layer.transform.positionZ!.keyframes.length).toBe(originalKeyframeCount);

        // Verify keyframe values are correctly extracted
        for (let i = 0; i < originalKeyframeCount; i++) {
          const original = keyframes[i];
          expect(layer.transform.positionX!.keyframes[i].value).toBe(original.value.x);
          expect(layer.transform.positionY!.keyframes[i].value).toBe(original.value.y);
          expect(layer.transform.positionZ!.keyframes[i].value).toBe(original.value.z);
        }
      }
    );

    test.prop([vec3Arb, sortedKeyframesArb(vec3Arb, 1, 5)])(
      "linking position merges X, Y, Z back into combined property",
      (currentValue, keyframes) => {
        fc.pre(keyframes.length >= 1);

        const layer = createMockLayer("layer1", keyframes);
        layer.transform.position.value = currentValue;

        // Separate
        separatePositionDimensions(layer.transform);

        // Verify separated
        expect(layer.transform.separateDimensions?.position).toBe(true);

        // Link back
        linkPositionDimensions(layer.transform);

        // Should be combined again
        expect(layer.transform.separateDimensions?.position).toBe(false);
        expect(layer.transform.positionX).toBeUndefined();
        expect(layer.transform.positionY).toBeUndefined();
        expect(layer.transform.positionZ).toBeUndefined();

        // Current value should match last separated values
        expect(layer.transform.position.value.x).toBe(currentValue.x);
        expect(layer.transform.position.value.y).toBe(currentValue.y);
        expect(layer.transform.position.value.z).toBe(currentValue.z);
      }
    );

    test.prop([vec3Arb])(
      "separate then link is identity for current value (no keyframes)",
      (currentValue) => {
        const layer = createMockLayer("layer1");
        layer.transform.position.value = currentValue;

        const originalX = currentValue.x;
        const originalY = currentValue.y;
        const originalZ = currentValue.z;

        separatePositionDimensions(layer.transform);
        linkPositionDimensions(layer.transform);

        expect(layer.transform.position.value.x).toBe(originalX);
        expect(layer.transform.position.value.y).toBe(originalY);
        expect(layer.transform.position.value.z).toBe(originalZ);
      }
    );
  });

  describe("Scale Separation Invariants", () => {
    test.prop([vec3Arb, sortedKeyframesArb(vec3Arb, 0, 5)])(
      "separating scale creates X, Y, Z properties with correct current values",
      (currentValue, keyframes) => {
        const layer = createMockLayer("layer1", [], keyframes);
        layer.transform.scale.value = currentValue;

        separateScaleDimensions(layer.transform);

        expect(layer.transform.separateDimensions?.scale).toBe(true);
        expect(layer.transform.scaleX).toBeDefined();
        expect(layer.transform.scaleY).toBeDefined();
        expect(layer.transform.scaleZ).toBeDefined();
        expect(layer.transform.scaleX!.value).toBe(currentValue.x);
        expect(layer.transform.scaleY!.value).toBe(currentValue.y);
        expect(layer.transform.scaleZ!.value).toBe(currentValue.z);
      }
    );

    test.prop([vec3Arb])(
      "separate then link scale is identity for current value",
      (currentValue) => {
        const layer = createMockLayer("layer1");
        layer.transform.scale.value = currentValue;

        const originalX = currentValue.x;
        const originalY = currentValue.y;
        const originalZ = currentValue.z;

        separateScaleDimensions(layer.transform);
        linkScaleDimensions(layer.transform);

        expect(layer.transform.scale.value.x).toBe(originalX);
        expect(layer.transform.scale.value.y).toBe(originalY);
        expect(layer.transform.scale.value.z).toBe(originalZ);
      }
    );
  });

  describe("Independence of Position and Scale Separation", () => {
    test.prop([vec3Arb, vec3Arb])(
      "separating position does not affect scale",
      (positionValue, scaleValue) => {
        const layer = createMockLayer("layer1");
        layer.transform.position.value = positionValue;
        layer.transform.scale.value = scaleValue;

        separatePositionDimensions(layer.transform);

        // Scale should be unchanged
        expect(layer.transform.separateDimensions?.scale).toBeFalsy();
        expect(layer.transform.scaleX).toBeUndefined();
        expect(layer.transform.scale.value).toEqual(scaleValue);
      }
    );

    test.prop([vec3Arb, vec3Arb])(
      "separating scale does not affect position",
      (positionValue, scaleValue) => {
        const layer = createMockLayer("layer1");
        layer.transform.position.value = positionValue;
        layer.transform.scale.value = scaleValue;

        separateScaleDimensions(layer.transform);

        // Position should be unchanged
        expect(layer.transform.separateDimensions?.position).toBeFalsy();
        expect(layer.transform.positionX).toBeUndefined();
        expect(layer.transform.position.value).toEqual(positionValue);
      }
    );

    test.prop([vec3Arb, vec3Arb])(
      "can separate both position and scale independently",
      (positionValue, scaleValue) => {
        const layer = createMockLayer("layer1");
        layer.transform.position.value = positionValue;
        layer.transform.scale.value = scaleValue;

        separatePositionDimensions(layer.transform);
        separateScaleDimensions(layer.transform);

        expect(layer.transform.separateDimensions?.position).toBe(true);
        expect(layer.transform.separateDimensions?.scale).toBe(true);
        expect(layer.transform.positionX!.value).toBe(positionValue.x);
        expect(layer.transform.scaleX!.value).toBe(scaleValue.x);
      }
    );
  });
});
