/**
 * Keyframe Timing Operations
 *
 * Scale, reverse, insert, and roving keyframe operations.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import { isFiniteNumber } from "@/utils/typeGuards";
import type { Keyframe } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { addKeyframe } from "./crud";
import { findPropertyByPath } from "./helpers";
import { findSurroundingKeyframes } from "./query";
import { useProjectStore } from "../projectStore";
import { useLayerStore } from "../layerStore";
import { generateKeyframeId } from "@/utils/uuid5";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                               // keyframe // timing // scale
// ════════════════════════════════════════════════════════════════════════════

/**
 * Scale keyframe timing by a factor.
 * Used for Alt+drag last keyframe to scale all keyframes proportionally.
 *
 * @param layerId - Layer ID
 * @param propertyPath - Property path (or undefined for all transform properties)
 * @param scaleFactor - Factor to scale by (e.g., 2.0 = twice as long, 0.5 = half)
 * @param anchorFrame - Frame to anchor scaling from (default: 0)
 */
export function scaleKeyframeTiming(
  layerId: string,
  propertyPath: string | undefined,
  scaleFactor: number,
  anchorFrame: number = 0,
): number {
  const projectStore = useProjectStore();
  const layerStore = useLayerStore();
  // Validate numeric parameters
  if (!Number.isFinite(scaleFactor) || !Number.isFinite(anchorFrame)) {
    storeLogger.warn("scaleKeyframeTiming: Invalid parameters:", {
      scaleFactor,
      anchorFrame,
    });
    return 0;
  }

  const layer = layerStore.getLayerById(layerId);
  if (!layer) return 0;

  // Determine which properties to scale
  const propertiesToScale: string[] = propertyPath
    ? [propertyPath]
    : ["position", "scale", "rotation", "opacity", "origin"];

  let scaledCount = 0;

  for (const propPath of propertiesToScale) {
    // findPropertyByPath already handles path normalization
    const property = findPropertyByPath(layer, propPath);

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const propertyKeyframes = (property != null && typeof property === "object" && "keyframes" in property && property.keyframes != null && Array.isArray(property.keyframes)) ? property.keyframes : undefined;
    if (propertyKeyframes != null && propertyKeyframes.length > 0) {
      // Scale each keyframe's frame number relative to anchor and regenerate IDs
      for (const kf of propertyKeyframes) {
        const relativeFrame = kf.frame - anchorFrame;
        const newFrame = Math.round(anchorFrame + relativeFrame * scaleFactor);
        // Regenerate keyframe ID based on new frame number for determinism
        // Same layer/property/frame/value should always produce same ID
        // Explicit check: kf.value is PropertyValue (never null/undefined per type system)
        const kfValue = kf.value;
        const valueStr = typeof kfValue === "object" && kfValue !== null && "x" in kfValue && "y" in kfValue
          ? `${(kfValue as { x: number; y: number }).x},${(kfValue as { x: number; y: number }).y}${"z" in kfValue ? `,${(kfValue as { x: number; y: number; z?: number }).z}` : ""}`
          : String(kfValue);
        kf.id = generateKeyframeId(layerId, propPath, newFrame, valueStr);
        kf.frame = newFrame;
      }
      // Re-sort keyframes to maintain order
      propertyKeyframes.sort((a, b) => a.frame - b.frame);
      scaledCount += propertyKeyframes.length;
    }
  }

  if (scaledCount > 0) {
    markLayerDirty(layerId);
    projectStore.project.meta.modified = new Date().toISOString();
    projectStore.pushHistory();
  }

  return scaledCount;
}

// ════════════════════════════════════════════════════════════════════════════
//                                               // keyframe // time // reverse
// ════════════════════════════════════════════════════════════════════════════

/**
 * Reverse keyframe timing (values stay at same frames, but values swap).
 * This creates the effect of playing the animation backward.
 *
 * @param layerId - Layer ID
 * @param propertyPath - Property path (or undefined for all transform properties)
 */
export function timeReverseKeyframes(
  layerId: string,
  propertyPath?: string,
): number {
  const projectStore = useProjectStore();
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(layerId);
  if (!layer) return 0;

  // Determine which properties to reverse
  const propertiesToReverse: string[] = propertyPath
    ? [propertyPath]
    : ["position", "scale", "rotation", "opacity", "origin"];

  let reversedCount = 0;

  for (const propPath of propertiesToReverse) {
    const property = findPropertyByPath(layer, propPath);

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const propertyKeyframes = (property != null && typeof property === "object" && "keyframes" in property && property.keyframes != null && Array.isArray(property.keyframes)) ? property.keyframes : undefined;
    if (propertyKeyframes != null && propertyKeyframes.length >= 2) {
      // Collect values in order
      const values = propertyKeyframes.map((kf) => kf.value);
      // Reverse the values
      values.reverse();
      // Assign reversed values back to keyframes and regenerate IDs (frames stay same, values change)
      for (let i = 0; i < propertyKeyframes.length; i++) {
        const kf = propertyKeyframes[i];
        kf.value = values[i];
        // Regenerate keyframe ID based on new value for determinism
        // Same layer/property/frame but different value should produce different ID
        // Explicit check: kf.value is PropertyValue (never null/undefined per type system)
        const kfValue = kf.value;
        const valueStr = typeof kfValue === "object" && kfValue !== null && "x" in kfValue && "y" in kfValue
          ? `${(kfValue as { x: number; y: number }).x},${(kfValue as { x: number; y: number }).y}${"z" in kfValue ? `,${(kfValue as { x: number; y: number; z?: number }).z}` : ""}`
          : String(kfValue);
        kf.id = generateKeyframeId(layerId, propPath, kf.frame, valueStr);
      }
      reversedCount += propertyKeyframes.length;
    }
  }

  if (reversedCount > 0) {
    markLayerDirty(layerId);
    projectStore.project.meta.modified = new Date().toISOString();
    projectStore.pushHistory();
  }

  return reversedCount;
}

// ════════════════════════════════════════════════════════════════════════════
//                                          // insert // keyframe // on // path
// ════════════════════════════════════════════════════════════════════════════

/**
 * Insert a keyframe at a specific position along a motion path.
 * Used for Pen tool click on path to add control point.
 *
 * @param layerId - Layer ID
 * @param frame - Frame number to insert at
 * @returns The created keyframe ID or null
 */
export function insertKeyframeOnPath(
  layerId: string,
  frame: number,
): string | null {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(layerId);
  if (!layer) {
    throw new Error(`[KeyframeStore] Cannot insert keyframe on path: Layer "${layerId}" not found`);
  }

  const positionProp = findPropertyByPath(layer, "transform.position");
  if (
    !positionProp ||
    !positionProp.animated ||
    !positionProp.keyframes ||
    positionProp.keyframes.length < 2
  ) {
    throw new Error(`[KeyframeStore] Cannot insert keyframe on path: Property "transform.position" is not animated or has fewer than 2 keyframes on layer "${layerId}"`);
  }

  // Check if keyframe already exists at this frame
  const existing = positionProp.keyframes.find((kf) => kf.frame === frame);
  if (existing) return existing.id;

  // Find surrounding keyframes
  const { before, after } = findSurroundingKeyframes(positionProp, frame);
  if (!before || !after) {
    throw new Error(`[KeyframeStore] Cannot insert keyframe on path: No surrounding keyframes found at frame ${frame} for layer "${layerId}"`);
  }

  // Guard against division by zero (identical frames)
  const frameDiff = after.frame - before.frame;
  if (frameDiff === 0) {
    throw new Error(`[KeyframeStore] Cannot insert keyframe on path: Surrounding keyframes have identical frames (${before.frame})`);
  }

  // Interpolate the value at this frame
  const t = (frame - before.frame) / frameDiff;
  const beforeVal = before.value as { x: number; y: number; z?: number };
  const afterVal = after.value as { x: number; y: number; z?: number };

  // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
  const beforeZValue = beforeVal.z;
  const beforeZ = isFiniteNumber(beforeZValue) ? beforeZValue : 0;
  const afterZValue = afterVal.z;
  const afterZ = isFiniteNumber(afterZValue) ? afterZValue : 0;
  const interpolatedValue = {
    x: beforeVal.x + (afterVal.x - beforeVal.x) * t,
    y: beforeVal.y + (afterVal.y - beforeVal.y) * t,
    z: beforeZ + (afterZ - beforeZ) * t,
  };

  // Create the keyframe
  const newKf = addKeyframe(
    layerId,
    "transform.position",
    interpolatedValue,
    frame,
  );

  // Type proof: newKf?.id ∈ string | undefined → string | null
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const newKfId = (newKf != null && typeof newKf === "object" && "id" in newKf && typeof newKf.id === "string") ? newKf.id : undefined;
  return typeof newKfId === "string" ? newKfId : null;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // roving // keyframes
// ════════════════════════════════════════════════════════════════════════════

/**
 * Apply roving keyframes to a position property.
 * Redistributes intermediate keyframe timing for constant velocity.
 *
 * @param layerId - Target layer ID
 * @returns true if roving was applied successfully
 */
export function applyRovingToPosition(
  layerId: string,
): boolean {
  const projectStore = useProjectStore();
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(layerId);
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
    // Position keyframes can be {x, y, z?} or number[] - applyRovingKeyframes accepts both via PositionValue
    const positionKeyframes = positionProp.keyframes as Keyframe<import("@/services/rovingKeyframes").PositionValue>[];
    const result = applyRovingKeyframes(positionKeyframes);

    if (result.success) {
      // Update keyframe frames and regenerate IDs for determinism
      result.keyframes.forEach((newKf, index) => {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const positionPropKeyframes = (positionProp != null && typeof positionProp === "object" && "keyframes" in positionProp && positionProp.keyframes != null && Array.isArray(positionProp.keyframes)) ? positionProp.keyframes : undefined;
        if (positionPropKeyframes != null && index >= 0 && index < positionPropKeyframes.length) {
          const kf = positionPropKeyframes[index];
          // Regenerate keyframe ID based on new frame number for determinism
          // Same layer/property/frame/value should always produce same ID
          // Explicit check: kf.value is PropertyValue (never null/undefined per type system)
          const kfValue = kf.value;
          const valueStr = typeof kfValue === "object" && kfValue !== null && "x" in kfValue && "y" in kfValue
            ? `${(kfValue as { x: number; y: number }).x},${(kfValue as { x: number; y: number }).y}${"z" in kfValue ? `,${(kfValue as { x: number; y: number; z?: number }).z}` : ""}`
            : String(kfValue);
          kf.id = generateKeyframeId(layerId, "transform.position", newKf.frame, valueStr);
          kf.frame = newKf.frame;
        }
      });

      // Mark layer as dirty
      markLayerDirty(layerId);

      // Update modified timestamp
      projectStore.project.meta.modified = new Date().toISOString();
      projectStore.pushHistory();

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
 * @param layerId - Target layer ID
 * @returns true if roving would make significant changes
 */
export function checkRovingImpact(
  layerId: string,
): boolean {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(layerId);
  if (!layer) return false;

  const positionProp = findPropertyByPath(layer, "transform.position");
  if (!positionProp || !positionProp.animated || !positionProp.keyframes) {
    return false;
  }

  // Roving requires at least 3 keyframes
  return positionProp.keyframes.length >= 3;
}
