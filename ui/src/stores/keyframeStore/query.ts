/**
 * Keyframe Query Utilities
 *
 * Functions for querying keyframe state and navigation.
 */

import type { AnimatableProperty, Keyframe, LayerTransform, PropertyValue } from "@/types/project";
import type { KeyframeStoreAccess } from "./types";

// ============================================================================
// KEYFRAME QUERY UTILITIES
// ============================================================================

/**
 * Get keyframes at a specific frame across all animated properties of a layer.
 */
export function getKeyframesAtFrame(
  store: KeyframeStoreAccess,
  layerId: string,
  frame: number,
): Array<{ propertyPath: string; keyframe: Keyframe<PropertyValue> }> {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return [];

  const results: Array<{ propertyPath: string; keyframe: Keyframe<PropertyValue> }> = [];

  // Check transform properties
  const transformProps: Array<keyof LayerTransform> = ["position", "scale", "rotation", "anchorPoint"];
  for (const propName of transformProps) {
    const prop = layer.transform[propName] as AnimatableProperty<unknown> | undefined;
    if (prop && "animated" in prop && prop.animated && prop.keyframes) {
      const kf = prop.keyframes.find((k) => k.frame === frame);
      if (kf) {
        // Cast: keyframe values are always PropertyValue-compatible
        results.push({ propertyPath: propName, keyframe: kf as Keyframe<PropertyValue> });
      }
    }
  }

  // Check opacity
  if (layer.opacity?.animated && layer.opacity.keyframes) {
    const kf = layer.opacity.keyframes.find((k) => k.frame === frame);
    if (kf) {
      results.push({ propertyPath: "opacity", keyframe: kf });
    }
  }

  // Check 3D rotations
  const threeDProps: Array<keyof LayerTransform> = ["rotationX", "rotationY", "rotationZ", "orientation"];
  for (const propName of threeDProps) {
    const prop = layer.transform[propName] as AnimatableProperty<unknown> | undefined;
    if (prop && "animated" in prop && prop.animated && prop.keyframes) {
      const kf = prop.keyframes.find((k) => k.frame === frame);
      if (kf) {
        // Cast: keyframe values are always PropertyValue-compatible
        results.push({ propertyPath: propName, keyframe: kf as Keyframe<PropertyValue> });
      }
    }
  }

  // Check custom properties
  for (const prop of layer.properties) {
    if (prop.animated && prop.keyframes) {
      const kf = prop.keyframes.find((k) => k.frame === frame);
      if (kf) {
        results.push({ propertyPath: prop.name, keyframe: kf });
      }
    }
  }

  return results;
}

/**
 * Get all keyframe frames for a layer (for timeline display).
 */
export function getAllKeyframeFrames(
  store: KeyframeStoreAccess,
  layerId: string,
): number[] {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return [];

  const frames = new Set<number>();

  // Collect frames from transform properties
  const transformProps: Array<keyof LayerTransform> = ["position", "scale", "rotation", "anchorPoint"];
  for (const propName of transformProps) {
    const prop = layer.transform[propName] as AnimatableProperty<unknown> | undefined;
    if (prop && "animated" in prop && prop.animated && prop.keyframes) {
      for (const kf of prop.keyframes) {
        frames.add(kf.frame);
      }
    }
  }

  // Collect from opacity
  if (layer.opacity?.animated && layer.opacity.keyframes) {
    for (const kf of layer.opacity.keyframes) {
      frames.add(kf.frame);
    }
  }

  // Collect from 3D properties
  const threeDProps: Array<keyof LayerTransform> = ["rotationX", "rotationY", "rotationZ", "orientation"];
  for (const propName of threeDProps) {
    const prop = layer.transform[propName] as AnimatableProperty<unknown> | undefined;
    if (prop && "animated" in prop && prop.animated && prop.keyframes) {
      for (const kf of prop.keyframes) {
        frames.add(kf.frame);
      }
    }
  }

  // Collect from custom properties
  for (const prop of layer.properties) {
    if (prop.animated && prop.keyframes) {
      for (const kf of prop.keyframes) {
        frames.add(kf.frame);
      }
    }
  }

  return Array.from(frames).sort((a, b) => a - b);
}

/**
 * Find the next keyframe frame after the given frame.
 *
 * @param store - The keyframe store
 * @param currentFrame - The current frame
 * @param layerIds - Layer IDs to search (if empty, searches all layers)
 * @returns The next keyframe frame, or null if none found
 */
export function findNextKeyframeFrame(
  store: KeyframeStoreAccess,
  currentFrame: number,
  layerIds: string[],
): number | null {
  const layers = store.getActiveCompLayers();
  const searchLayerIds =
    layerIds.length > 0 ? layerIds : layers.map((l) => l.id);

  const frameSet = new Set<number>();
  for (const lid of searchLayerIds) {
    for (const frame of getAllKeyframeFrames(store, lid)) {
      frameSet.add(frame);
    }
  }

  const allFrames = Array.from(frameSet).sort((a, b) => a - b);
  return allFrames.find((f) => f > currentFrame) ?? null;
}

/**
 * Find the previous keyframe frame before the given frame.
 *
 * @param store - The keyframe store
 * @param currentFrame - The current frame
 * @param layerIds - Layer IDs to search (if empty, searches all layers)
 * @returns The previous keyframe frame, or null if none found
 */
export function findPrevKeyframeFrame(
  store: KeyframeStoreAccess,
  currentFrame: number,
  layerIds: string[],
): number | null {
  const layers = store.getActiveCompLayers();
  const searchLayerIds =
    layerIds.length > 0 ? layerIds : layers.map((l) => l.id);

  const frameSet = new Set<number>();
  for (const lid of searchLayerIds) {
    for (const frame of getAllKeyframeFrames(store, lid)) {
      frameSet.add(frame);
    }
  }

  const allFrames = Array.from(frameSet).sort((a, b) => a - b);
  const prevFrames = allFrames.filter((f) => f < currentFrame);
  return prevFrames.length > 0 ? prevFrames[prevFrames.length - 1] : null;
}

/**
 * Find the nearest keyframes before and after a given frame.
 */
export function findSurroundingKeyframes<T>(
  property: AnimatableProperty<T>,
  frame: number,
): { before: Keyframe<T> | null; after: Keyframe<T> | null } {
  if (!property.keyframes || property.keyframes.length === 0) {
    return { before: null, after: null };
  }

  let before: Keyframe<T> | null = null;
  let after: Keyframe<T> | null = null;

  for (const kf of property.keyframes) {
    if (kf.frame <= frame) {
      before = kf;
    } else if (kf.frame > frame && after === null) {
      after = kf;
      break;
    }
  }

  return { before, after };
}
