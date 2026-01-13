/**
 * Keyframe Timing Operations
 *
 * Scale, reverse, insert, and roving keyframe operations.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { Keyframe } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useLayerStore } from "@/stores/layerStore";
import { addKeyframe } from "./crud";
import { findPropertyByPath } from "./helpers";
import { findSurroundingKeyframes } from "./query";
import type { KeyframeStoreAccess, RovingKeyframeStoreAccess } from "./types";

// ============================================================================
// KEYFRAME TIMING SCALE
// ============================================================================

/**
 * Scale keyframe timing by a factor.
 * Used for Alt+drag last keyframe to scale all keyframes proportionally.
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param propertyPath - Property path (or undefined for all transform properties)
 * @param scaleFactor - Factor to scale by (e.g., 2.0 = twice as long, 0.5 = half)
 * @param anchorFrame - Frame to anchor scaling from (default: 0)
 */
export function scaleKeyframeTiming(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string | undefined,
  scaleFactor: number,
  anchorFrame: number = 0,
): number {
  // Validate numeric parameters
  if (!Number.isFinite(scaleFactor) || !Number.isFinite(anchorFrame)) {
    storeLogger.warn("scaleKeyframeTiming: Invalid parameters:", {
      scaleFactor,
      anchorFrame,
    });
    return 0;
  }

  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(store, layerId);
  if (!layer) return 0;

  // Determine which properties to scale
  const propertiesToScale: string[] = propertyPath
    ? [propertyPath]
    : ["position", "scale", "rotation", "opacity", "origin"];

  let scaledCount = 0;

  for (const propPath of propertiesToScale) {
    // findPropertyByPath already handles path normalization
    const property = findPropertyByPath(layer, propPath);

    if (property?.keyframes && property.keyframes.length > 0) {
      // Scale each keyframe's frame number relative to anchor
      for (const kf of property.keyframes) {
        const relativeFrame = kf.frame - anchorFrame;
        kf.frame = Math.round(anchorFrame + relativeFrame * scaleFactor);
      }
      // Re-sort keyframes to maintain order
      property.keyframes.sort((a, b) => a.frame - b.frame);
      scaledCount += property.keyframes.length;
    }
  }

  if (scaledCount > 0) {
    markLayerDirty(layerId);
    store.project.meta.modified = new Date().toISOString();
    store.pushHistory();
  }

  return scaledCount;
}

// ============================================================================
// KEYFRAME TIME REVERSE
// ============================================================================

/**
 * Reverse keyframe timing (values stay at same frames, but values swap).
 * This creates the effect of playing the animation backward.
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param propertyPath - Property path (or undefined for all transform properties)
 */
export function timeReverseKeyframes(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath?: string,
): number {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(store, layerId);
  if (!layer) return 0;

  // Determine which properties to reverse
  const propertiesToReverse: string[] = propertyPath
    ? [propertyPath]
    : ["position", "scale", "rotation", "opacity", "origin"];

  let reversedCount = 0;

  for (const propPath of propertiesToReverse) {
    const property = findPropertyByPath(layer, propPath);

    if (property?.keyframes && property.keyframes.length >= 2) {
      // Collect values in order
      const values = property.keyframes.map((kf) => kf.value);
      // Reverse the values
      values.reverse();
      // Assign reversed values back to keyframes (frames stay same)
      for (let i = 0; i < property.keyframes.length; i++) {
        property.keyframes[i].value = values[i];
      }
      reversedCount += property.keyframes.length;
    }
  }

  if (reversedCount > 0) {
    markLayerDirty(layerId);
    store.project.meta.modified = new Date().toISOString();
    store.pushHistory();
  }

  return reversedCount;
}

// ============================================================================
// INSERT KEYFRAME ON PATH
// ============================================================================

/**
 * Insert a keyframe at a specific position along a motion path.
 * Used for Pen tool click on path to add control point.
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param frame - Frame number to insert at
 * @returns The created keyframe ID or null
 */
export function insertKeyframeOnPath(
  store: KeyframeStoreAccess,
  layerId: string,
  frame: number,
): string | null {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(store, layerId);
  if (!layer) return null;

  const positionProp = findPropertyByPath(layer, "transform.position");
  if (
    !positionProp ||
    !positionProp.animated ||
    !positionProp.keyframes ||
    positionProp.keyframes.length < 2
  ) {
    return null;
  }

  // Check if keyframe already exists at this frame
  const existing = positionProp.keyframes.find((kf) => kf.frame === frame);
  if (existing) return existing.id;

  // Find surrounding keyframes
  const { before, after } = findSurroundingKeyframes(positionProp, frame);
  if (!before || !after) return null;

  // Guard against division by zero (identical frames)
  const frameDiff = after.frame - before.frame;
  if (frameDiff === 0) return null;

  // Interpolate the value at this frame
  const t = (frame - before.frame) / frameDiff;
  const beforeVal = before.value as { x: number; y: number; z?: number };
  const afterVal = after.value as { x: number; y: number; z?: number };

  const interpolatedValue = {
    x: beforeVal.x + (afterVal.x - beforeVal.x) * t,
    y: beforeVal.y + (afterVal.y - beforeVal.y) * t,
    z: (beforeVal.z ?? 0) + ((afterVal.z ?? 0) - (beforeVal.z ?? 0)) * t,
  };

  // Create the keyframe
  const newKf = addKeyframe(
    store,
    layerId,
    "transform.position",
    interpolatedValue,
    frame,
  );

  return newKf?.id ?? null;
}

// ============================================================================
// ROVING KEYFRAMES
// ============================================================================

/**
 * Apply roving keyframes to a position property.
 * Redistributes intermediate keyframe timing for constant velocity.
 *
 * @param store - Store with layer access
 * @param layerId - Target layer ID
 * @returns true if roving was applied successfully
 */
export function applyRovingToPosition(
  store: RovingKeyframeStoreAccess,
  layerId: string,
): boolean {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(store, layerId);
  if (!layer) {
    storeLogger.debug("applyRovingToPosition: layer not found");
    return false;
  }

  const positionProp = findPropertyByPath(layer, "transform.position");
  if (!positionProp || !positionProp.animated || !positionProp.keyframes) {
    storeLogger.debug("applyRovingToPosition: no animated position keyframes");
    return false;
  }

  if (positionProp.keyframes.length < 3) {
    storeLogger.debug(
      "applyRovingToPosition: need at least 3 keyframes for roving",
    );
    return false;
  }

  // Import and apply roving
  // Note: Using dynamic import to avoid circular dependency
  import("@/services/rovingKeyframes").then(({ applyRovingKeyframes }) => {
    const result = applyRovingKeyframes(
      positionProp.keyframes as Keyframe<number[]>[],
    );

    if (result.success) {
      // Update keyframe frames in place
      result.keyframes.forEach((newKf, index) => {
        if (positionProp.keyframes?.[index]) {
          positionProp.keyframes[index].frame = newKf.frame;
        }
      });

      // Mark layer as dirty
      markLayerDirty(layerId);

      // Update modified timestamp
      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      storeLogger.info("applyRovingToPosition: applied roving keyframes", {
        layerId,
        totalLength: result.totalLength,
        keyframeCount: result.keyframes.length,
      });
    } else {
      storeLogger.warn("applyRovingToPosition: roving failed", result.error);
    }
  });

  return true;
}

/**
 * Check if roving would significantly change keyframe timing.
 *
 * @param store - Store with layer access
 * @param layerId - Target layer ID
 * @returns true if roving would make significant changes
 */
export function checkRovingImpact(
  store: RovingKeyframeStoreAccess,
  layerId: string,
): boolean {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(store, layerId);
  if (!layer) return false;

  const positionProp = findPropertyByPath(layer, "transform.position");
  if (!positionProp || !positionProp.animated || !positionProp.keyframes) {
    return false;
  }

  // Roving requires at least 3 keyframes
  return positionProp.keyframes.length >= 3;
}
