/**
 * Keyframe Query Utilities
 *
 * Functions for querying keyframe state and navigation.
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import type { AnimatableProperty, Keyframe, LayerTransform, PropertyValue } from "@/types/project";
import { useProjectStore } from "../projectStore";

// ============================================================================
// KEYFRAME QUERY UTILITIES
// ============================================================================

/**
 * Get keyframes at a specific frame across all animated properties of a layer.
 */
export function getKeyframesAtFrame(
  layerId: string,
  frame: number,
): Array<{ propertyPath: string; keyframe: Keyframe<PropertyValue> }> {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return [];

  const results: Array<{ propertyPath: string; keyframe: Keyframe<PropertyValue> }> = [];

  // Check transform properties
  const transformProps: Array<keyof LayerTransform> = ["position", "scale", "rotation", "anchorPoint"];
  for (const propName of transformProps) {
    const prop = layer.transform[propName] as AnimatableProperty<PropertyValue> | undefined;
    if (prop && "animated" in prop && prop.animated && prop.keyframes) {
      const kf = prop.keyframes.find((k) => k.frame === frame);
      if (kf) {
        // Cast: keyframe values are always PropertyValue-compatible
        results.push({ propertyPath: propName, keyframe: kf as Keyframe<PropertyValue> });
      }
    }
  }

  // Check opacity
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layerOpacity = (layer != null && typeof layer === "object" && "opacity" in layer && layer.opacity != null && typeof layer.opacity === "object") ? layer.opacity : undefined;
  const opacityAnimated = (layerOpacity != null && typeof layerOpacity === "object" && "animated" in layerOpacity && typeof layerOpacity.animated === "boolean" && layerOpacity.animated) ? true : false;
  const opacityKeyframes = (layerOpacity != null && typeof layerOpacity === "object" && "keyframes" in layerOpacity && layerOpacity.keyframes != null && Array.isArray(layerOpacity.keyframes)) ? layerOpacity.keyframes : undefined;
  if (opacityAnimated && opacityKeyframes != null) {
    const kf = opacityKeyframes.find((k) => k.frame === frame);
    if (kf) {
      results.push({ propertyPath: "opacity", keyframe: kf });
    }
  }

  // Check 3D rotations
  const threeDProps: Array<keyof LayerTransform> = ["rotationX", "rotationY", "rotationZ", "orientation"];
  for (const propName of threeDProps) {
    const prop = layer.transform[propName] as AnimatableProperty<PropertyValue> | undefined;
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
  layerId: string,
): number[] {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return [];

  const frames = new Set<number>();

  // Collect frames from transform properties
  const transformProps: Array<keyof LayerTransform> = ["position", "scale", "rotation", "anchorPoint"];
  for (const propName of transformProps) {
    const prop = layer.transform[propName] as AnimatableProperty<PropertyValue> | undefined;
    if (prop && "animated" in prop && prop.animated && prop.keyframes) {
      for (const kf of prop.keyframes) {
        frames.add(kf.frame);
      }
    }
  }

  // Collect from opacity
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layerOpacity = (layer != null && typeof layer === "object" && "opacity" in layer && layer.opacity != null && typeof layer.opacity === "object") ? layer.opacity : undefined;
  const opacityAnimated = (layerOpacity != null && typeof layerOpacity === "object" && "animated" in layerOpacity && typeof layerOpacity.animated === "boolean" && layerOpacity.animated) ? true : false;
  const opacityKeyframes = (layerOpacity != null && typeof layerOpacity === "object" && "keyframes" in layerOpacity && layerOpacity.keyframes != null && Array.isArray(layerOpacity.keyframes)) ? layerOpacity.keyframes : undefined;
  if (opacityAnimated && opacityKeyframes != null) {
    for (const kf of opacityKeyframes) {
      frames.add(kf.frame);
    }
  }

  // Collect from 3D properties
  const threeDProps: Array<keyof LayerTransform> = ["rotationX", "rotationY", "rotationZ", "orientation"];
  for (const propName of threeDProps) {
    const prop = layer.transform[propName] as AnimatableProperty<PropertyValue> | undefined;
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
 * @param currentFrame - The current frame
 * @param layerIds - Layer IDs to search (if empty, searches all layers)
 * @returns The next keyframe frame
 * @throws Error if no next keyframe found
 */
export function findNextKeyframeFrame(
  currentFrame: number,
  layerIds: string[],
): number {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  const searchLayerIds =
    layerIds.length > 0 ? layerIds : layers.map((l) => l.id);

  const frameSet = new Set<number>();
  for (const lid of searchLayerIds) {
    for (const frame of getAllKeyframeFrames(lid)) {
      frameSet.add(frame);
    }
  }

  const allFrames = Array.from(frameSet).sort((a, b) => a - b);
  // Type proof: Array.find() returns number | undefined → number (throws if not found)
  const foundFrame = allFrames.find((f) => f > currentFrame);
  if (isFiniteNumber(foundFrame) && Number.isInteger(foundFrame) && foundFrame >= 0) {
    return foundFrame;
  }
  throw new Error(`[KeyframeQuery] No next keyframe found after frame ${currentFrame} for layers: ${layerIds.join(", ")}`);
}

/**
 * Find the previous keyframe frame before the given frame.
 *
 * @param currentFrame - The current frame
 * @param layerIds - Layer IDs to search (if empty, searches all layers)
 * @returns The previous keyframe frame
 * @throws Error if no previous keyframe found
 */
export function findPrevKeyframeFrame(
  currentFrame: number,
  layerIds: string[],
): number {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  const searchLayerIds =
    layerIds.length > 0 ? layerIds : layers.map((l) => l.id);

  const frameSet = new Set<number>();
  for (const lid of searchLayerIds) {
    for (const frame of getAllKeyframeFrames(lid)) {
      frameSet.add(frame);
    }
  }

  const allFrames = Array.from(frameSet).sort((a, b) => a - b);
  const prevFrames = allFrames.filter((f) => f < currentFrame);
  if (prevFrames.length > 0) {
    return prevFrames[prevFrames.length - 1];
  }
  throw new Error(`[KeyframeQuery] No previous keyframe found before frame ${currentFrame} for layers: ${layerIds.join(", ")}`);
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
