/**
 * Auto Bezier Tangent Operations
 *
 * Auto-calculate bezier tangents for smooth keyframe curves.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { Keyframe, PropertyValue } from "@/types/project";
import { findPropertyByPath } from "./helpers";
import type { KeyframeStoreAccess } from "./types";

// ============================================================================
// AUTO BEZIER TANGENT CALCULATION
// ============================================================================

/**
 * Auto-calculate bezier tangents for a keyframe based on surrounding keyframes.
 * This creates smooth curves through keyframe values.
 *
 * Algorithm:
 * - For keyframes with both neighbors: tangent angle points from prev to next
 * - For first keyframe: tangent is horizontal
 * - For last keyframe: tangent is horizontal
 * - Tangent magnitude is proportional to segment length
 */
export function autoCalculateBezierTangents(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
): boolean {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || property.keyframes.length < 2) return false;

  // Sort keyframes by frame
  const sorted = [...property.keyframes].sort((a, b) => a.frame - b.frame);
  const kfIndex = sorted.findIndex((kf) => kf.id === keyframeId);
  if (kfIndex === -1) return false;

  const keyframe = sorted[kfIndex];
  const prevKf = kfIndex > 0 ? sorted[kfIndex - 1] : null;
  const nextKf = kfIndex < sorted.length - 1 ? sorted[kfIndex + 1] : null;

  const getValue = (kf: Keyframe<PropertyValue>) => {
    if (typeof kf.value === "number") return kf.value;
    if (Array.isArray(kf.value) && kf.value.length > 0 && typeof kf.value[0] === "number") {
      return kf.value[0];
    }
    return 0;
  };
  const currentValue = getValue(keyframe);

  // Calculate tangent direction (slope from prev to next)
  let slopeFrame = 0;
  let slopeValue = 0;

  if (prevKf && nextKf) {
    // Middle keyframe: slope from prev to next
    const prevValue = getValue(prevKf);
    const nextValue = getValue(nextKf);
    const frameDelta = nextKf.frame - prevKf.frame;
    const valueDelta = nextValue - prevValue;

    slopeFrame = frameDelta / 2;
    slopeValue = valueDelta / 2;
  } else if (prevKf) {
    // Last keyframe: use slope from previous segment
    const prevValue = getValue(prevKf);
    const frameDelta = keyframe.frame - prevKf.frame;
    const valueDelta = currentValue - prevValue;

    slopeFrame = frameDelta / 3;
    slopeValue = valueDelta / 3;
  } else if (nextKf) {
    // First keyframe: use slope to next segment
    const nextValue = getValue(nextKf);
    const frameDelta = nextKf.frame - keyframe.frame;
    const valueDelta = nextValue - currentValue;

    slopeFrame = frameDelta / 3;
    slopeValue = valueDelta / 3;
  }

  // Set handles with calculated tangents
  keyframe.inHandle = {
    frame: -slopeFrame,
    value: -slopeValue,
    enabled: true,
  };
  keyframe.outHandle = {
    frame: slopeFrame,
    value: slopeValue,
    enabled: true,
  };
  keyframe.interpolation = "bezier";
  keyframe.controlMode = "smooth";

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Auto-calculate bezier tangents for ALL keyframes on a property.
 * Useful when converting from linear to bezier interpolation.
 */
export function autoCalculateAllBezierTangents(
  store: KeyframeStoreAccess,
  layerId: string,
  propertyPath: string,
): number {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return 0;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || property.keyframes.length < 2) return 0;

  // Sort keyframes by frame
  const sorted = [...property.keyframes].sort((a, b) => a.frame - b.frame);
  let count = 0;

  for (let i = 0; i < sorted.length; i++) {
    const keyframe = sorted[i];
    const prevKf = i > 0 ? sorted[i - 1] : null;
    const nextKf = i < sorted.length - 1 ? sorted[i + 1] : null;

    const getValue = (kf: Keyframe<PropertyValue>) => {
      if (typeof kf.value === "number") return kf.value;
      if (Array.isArray(kf.value) && kf.value.length > 0 && typeof kf.value[0] === "number") {
        return kf.value[0];
      }
      return 0;
    };
    const currentValue = getValue(keyframe);

    let slopeFrame = 0;
    let slopeValue = 0;

    if (prevKf && nextKf) {
      const prevValue = getValue(prevKf);
      const nextValue = getValue(nextKf);
      const frameDelta = nextKf.frame - prevKf.frame;
      const valueDelta = nextValue - prevValue;

      slopeFrame = frameDelta / 4; // Less aggressive for all-at-once
      slopeValue = valueDelta / 4;
    } else if (prevKf) {
      const prevValue = getValue(prevKf);
      const frameDelta = keyframe.frame - prevKf.frame;
      const valueDelta = currentValue - prevValue;

      slopeFrame = frameDelta / 3;
      slopeValue = valueDelta / 3;
    } else if (nextKf) {
      const nextValue = getValue(nextKf);
      const frameDelta = nextKf.frame - keyframe.frame;
      const valueDelta = nextValue - currentValue;

      slopeFrame = frameDelta / 3;
      slopeValue = valueDelta / 3;
    }

    keyframe.inHandle = {
      frame: -slopeFrame,
      value: -slopeValue,
      enabled: true,
    };
    keyframe.outHandle = {
      frame: slopeFrame,
      value: slopeValue,
      enabled: true,
    };
    keyframe.interpolation = "bezier";
    keyframe.controlMode = "smooth";
    count++;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return count;
}
