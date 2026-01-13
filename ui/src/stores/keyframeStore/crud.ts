/**
 * Keyframe CRUD Operations
 *
 * Add, remove, clear, move, and update keyframe operations.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type {
  AnimatableProperty,
  Keyframe,
  Layer,
} from "@/types/project";
import type { PropertyValue } from "@/types/animation";
import { storeLogger } from "@/utils/logger";
import { findPropertyByPath, safeFrame } from "./helpers";
import type { KeyframeStoreAccess } from "./types";

// ============================================================================
// KEYFRAME CREATION
// ============================================================================

/**
 * Add a keyframe to a property at the specified frame.
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param propertyPath - Property path (e.g., 'position', 'transform.position')
 * @param value - The keyframe value
 * @param atFrame - Frame to add keyframe at (defaults to current frame)
 * @returns The created keyframe or null if failed
 */
export function addKeyframe<T>(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string,
  value: T,
  atFrame?: number,
): Keyframe<T> | null {
  const comp = store.getActiveComp();
  // Validate frame (nullish coalescing doesn't catch NaN)
  const frame = safeFrame(atFrame ?? comp?.currentFrame, 0);

  storeLogger.debug("addKeyframe called:", {
    layerId,
    propertyPath,
    value,
    frame,
  });

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.debug("addKeyframe: layer not found");
    return null;
  }

  const property = findPropertyByPath(layer, propertyPath) as
    | AnimatableProperty<T>
    | undefined;
  if (!property) {
    storeLogger.debug("addKeyframe: property not found:", propertyPath);
    return null;
  }

  // Enable animation
  property.animated = true;

  // Create keyframe with default linear handles (disabled until graph editor enables them)
  const keyframe: Keyframe<T> = {
    id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    frame,
    value,
    interpolation: "linear",
    inHandle: { frame: 0, value: 0, enabled: false },
    outHandle: { frame: 0, value: 0, enabled: false },
    controlMode: "smooth",
  };

  // Check for existing keyframe at this frame
  const existingIndex = property.keyframes.findIndex((k) => k.frame === frame);
  if (existingIndex >= 0) {
    property.keyframes[existingIndex] = keyframe;
    storeLogger.debug(
      "addKeyframe: replaced existing keyframe at frame",
      frame,
    );
  } else {
    property.keyframes.push(keyframe);
    property.keyframes.sort((a, b) => a.frame - b.frame);
    storeLogger.debug(
      "addKeyframe: added new keyframe at frame",
      frame,
      "total keyframes:",
      property.keyframes.length,
    );
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
  return keyframe;
}

// ============================================================================
// KEYFRAME REMOVAL
// ============================================================================

/**
 * Remove a keyframe by ID.
 */
export function removeKeyframe(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const index = property.keyframes.findIndex((k) => k.id === keyframeId);
  if (index >= 0) {
    property.keyframes.splice(index, 1);

    // Disable animation if no keyframes left
    if (property.keyframes.length === 0) {
      property.animated = false;
    }
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Remove all keyframes from a property.
 */
export function clearKeyframes(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string,
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  property.keyframes = [];
  property.animated = false;

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// PROPERTY UPDATE
// ============================================================================

/**
 * Update an entire AnimatableProperty by path, including keyframes.
 * Used for batch operations like audio-reactive keyframe generation.
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param propertyPath - Path to property (e.g., 'transform.position', 'opacity')
 * @param propertyData - Full AnimatableProperty object to replace with
 * @returns true if successful
 */
export function updateLayerProperty(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string,
  propertyData: Partial<AnimatableProperty<any>>,
): boolean {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("updateLayerProperty: layer not found", layerId);
    return false;
  }

  // Normalize path - strip 'transform.' prefix if present
  const normalizedPath = propertyPath.replace(/^transform\./, "");

  // Get reference to the actual property object
  let property: AnimatableProperty<any> | undefined;

  // Check transform properties
  if (normalizedPath === "position") {
    property = layer.transform.position;
  } else if (normalizedPath === "scale") {
    property = layer.transform.scale;
  } else if (normalizedPath === "rotation") {
    property = layer.transform.rotation;
  } else if (normalizedPath === "anchorPoint") {
    property = layer.transform.anchorPoint;
  } else if (normalizedPath === "origin") {
    property = layer.transform.origin;
  } else if (propertyPath === "opacity") {
    property = layer.opacity as AnimatableProperty<any>;
  } else if (normalizedPath === "rotationX" && layer.transform.rotationX) {
    property = layer.transform.rotationX;
  } else if (normalizedPath === "rotationY" && layer.transform.rotationY) {
    property = layer.transform.rotationY;
  } else if (normalizedPath === "rotationZ" && layer.transform.rotationZ) {
    property = layer.transform.rotationZ;
  } else if (normalizedPath === "orientation" && layer.transform.orientation) {
    property = layer.transform.orientation;
  } else {
    // Check custom properties by name or id
    property = layer.properties.find(
      (p) => p.name === propertyPath || p.id === propertyPath,
    );
  }

  if (!property) {
    storeLogger.warn("updateLayerProperty: property not found", propertyPath);
    return false;
  }

  // Update the property with new data
  if (propertyData.value !== undefined) {
    property.value = propertyData.value;
  }
  if (propertyData.animated !== undefined) {
    property.animated = propertyData.animated;
  }
  if (propertyData.keyframes !== undefined) {
    // Ensure keyframes have valid structure
    property.keyframes = propertyData.keyframes.map((kf) => ({
      id:
        kf.id || `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
      frame: kf.frame,
      value: kf.value,
      interpolation: kf.interpolation || "linear",
      inHandle: kf.inHandle || { frame: 0, value: 0, enabled: false },
      outHandle: kf.outHandle || { frame: 0, value: 0, enabled: false },
      controlMode: kf.controlMode || "smooth",
      spatialInTangent: kf.spatialInTangent,
      spatialOutTangent: kf.spatialOutTangent,
    }));
    // Sort keyframes by frame
    property.keyframes.sort((a, b) => a.frame - b.frame);
  }
  if (propertyData.expression !== undefined) {
    // SECURITY: Block custom expressions from this API path
    // Custom expressions contain user code that must be validated asynchronously.
    // They can only enter through:
    // 1. Project load (pre-validates all expressions)
    // 2. Expression editor UI (validates before applying)
    const expr = propertyData.expression;
    if (expr?.type === "custom" && expr?.params?.code) {
      storeLogger.error(
        "updateLayerProperty: Custom expressions must be applied through expression editor (requires async validation)",
      );
      return false;
    }
    property.expression = propertyData.expression;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.debug(
    "updateLayerProperty: Updated",
    propertyPath,
    "on layer",
    layerId,
  );
  return true;
}

// ============================================================================
// KEYFRAME MOVEMENT
// ============================================================================

/**
 * Move a keyframe to a new frame position.
 */
export function moveKeyframe(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  newFrame: number,
): void {
  // Validate frame before processing
  if (!Number.isFinite(newFrame)) {
    storeLogger.warn("moveKeyframe: Invalid frame value:", newFrame);
    return;
  }

  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find((kf) => kf.id === keyframeId);
  if (!keyframe) return;

  // Check if there's already a keyframe at the target frame
  const existingAtTarget = property.keyframes.find(
    (kf) => kf.frame === newFrame && kf.id !== keyframeId,
  );
  if (existingAtTarget) {
    // Remove the existing keyframe at target
    property.keyframes = property.keyframes.filter(
      (kf) => kf.id !== existingAtTarget.id,
    );
  }

  keyframe.frame = newFrame;

  // Re-sort keyframes by frame
  property.keyframes.sort((a, b) => a.frame - b.frame);

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Move multiple keyframes by a frame delta (for marquee selection bulk moves).
 *
 * IMPORTANT: This function handles two types of collisions:
 * 1. Collisions with NON-SELECTED keyframes at target frames (removes them)
 * 2. Collisions between SELECTED keyframes that end up at same frame (keeps one with larger original frame)
 *
 * The interpolation system uses binary search and REQUIRES sorted keyframes with unique frames.
 * Violating this invariant breaks ALL animation evaluation, exports, and rendering.
 *
 * @see interpolation.ts - findKeyframeIndex() assumes sorted, unique frames
 * @see layerEvaluationCache.ts - evaluateLayerCached() calls interpolateProperty
 */
export function moveKeyframes(
  store: KeyframeStoreAccess,
  keyframes: Array<{
    layerId: string;
    propertyPath: string;
    keyframeId: string;
  }>,
  frameDelta: number,
): void {
  // Validate frameDelta
  if (!Number.isFinite(frameDelta)) {
    storeLogger.warn("moveKeyframes: Invalid frameDelta:", frameDelta);
    return;
  }

  // Group keyframes by layer+property for efficient collision handling
  const grouped = new Map<
    string,
    {
      layer: Layer;
      property: AnimatableProperty<unknown>;
      keyframeIds: Set<string>;
    }
  >();

  for (const kf of keyframes) {
    const layer = store.getActiveCompLayers().find((l) => l.id === kf.layerId);
    if (!layer) continue;

    const property = findPropertyByPath(layer, kf.propertyPath);
    if (!property) continue;

    const key = `${kf.layerId}:${kf.propertyPath}`;
    let group = grouped.get(key);
    if (!group) {
      group = {
        layer,
        property,
        keyframeIds: new Set(),
      };
      grouped.set(key, group);
    }
    group.keyframeIds.add(kf.keyframeId);
  }

  // Process each property group
  const layerIds = new Set<string>();
  for (const { layer, property, keyframeIds } of grouped.values()) {
    layerIds.add(layer.id);

    // Calculate target frames for all selected keyframes
    const moves: Array<{
      kf: Keyframe<unknown>;
      originalFrame: number;
      targetFrame: number;
    }> = [];
    for (const kf of property.keyframes) {
      if (keyframeIds.has(kf.id)) {
        const targetFrame = Math.max(0, kf.frame + frameDelta);
        moves.push({ kf, originalFrame: kf.frame, targetFrame });
      }
    }

    // Build map of target frame -> winning keyframe
    // Sort moves by original frame descending so later keyframes win on collision
    // (when two selected keyframes end up at same frame after move)
    const targetFrameMap = new Map<
      number,
      { kf: Keyframe<unknown>; originalFrame: number }
    >();
    moves.sort((a, b) => b.originalFrame - a.originalFrame);
    for (const move of moves) {
      if (!targetFrameMap.has(move.targetFrame)) {
        targetFrameMap.set(move.targetFrame, {
          kf: move.kf,
          originalFrame: move.originalFrame,
        });
      }
    }

    // Build set of selected keyframe IDs that will survive collisions
    const survivingIds = new Set<string>();
    for (const { kf } of targetFrameMap.values()) {
      survivingIds.add(kf.id);
    }

    // Remove:
    // 1. Non-selected keyframes at target frames (collision with moved keyframes)
    // 2. Selected keyframes that lost collision with other selected keyframes
    property.keyframes = property.keyframes.filter((kf: Keyframe<unknown>) => {
      if (!keyframeIds.has(kf.id)) {
        // Non-selected: keep unless at a target frame
        return !targetFrameMap.has(kf.frame);
      }
      // Selected: keep only if it won its target slot
      return survivingIds.has(kf.id);
    });

    // Apply new frame values
    for (const [targetFrame, { kf }] of targetFrameMap) {
      kf.frame = targetFrame;
    }

    // Re-sort keyframes by frame (maintains interpolation system invariant)
    property.keyframes.sort(
      (a: Keyframe<unknown>, b: Keyframe<unknown>) => a.frame - b.frame,
    );
  }

  // Mark all affected layers as dirty (invalidates evaluation cache)
  for (const layerId of layerIds) {
    markLayerDirty(layerId);
  }
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

// ============================================================================
// KEYFRAME VALUE UPDATES
// ============================================================================

/**
 * Update a keyframe's value.
 */
export function setKeyframeValue(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  newValue: PropertyValue,
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find((kf) => kf.id === keyframeId);
  if (!keyframe) return;

  // Handle vector values (Position X/Y are separated in graph editor)
  if (
    typeof keyframe.value === "object" &&
    keyframe.value !== null &&
    typeof newValue === "number"
  ) {
    storeLogger.warn(
      "setKeyframeValue: Cannot directly update vector keyframes with scalar. Use separate dimension curves.",
    );
    return;
  }

  keyframe.value = newValue;
  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Update keyframe frame position and/or value.
 */
export function updateKeyframe(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  updates: { frame?: number; value?: PropertyValue },
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return;

  const keyframe = property.keyframes.find((kf) => kf.id === keyframeId);
  if (!keyframe) return;

  if (updates.frame !== undefined && Number.isFinite(updates.frame)) {
    // Check for existing keyframe at target frame (same pattern as moveKeyframe)
    const existingAtTarget = property.keyframes.find(
      (kf) => kf.frame === updates.frame && kf.id !== keyframeId,
    );
    if (existingAtTarget) {
      // Remove the existing keyframe at target to prevent duplicates
      property.keyframes = property.keyframes.filter(
        (kf) => kf.id !== existingAtTarget.id,
      );
    }
    keyframe.frame = updates.frame;
    // Re-sort keyframes by frame
    property.keyframes.sort((a, b) => a.frame - b.frame);
  }

  if (updates.value !== undefined) {
    keyframe.value = updates.value;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}
