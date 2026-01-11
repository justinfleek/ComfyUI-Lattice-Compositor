/**
 * Keyframe Velocity Operations
 *
 * Apply and retrieve velocity settings for keyframe handles.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import { findPropertyByPath } from "./helpers";
import type { VelocitySettings, VelocityStoreAccess } from "./types";

// ============================================================================
// KEYFRAME VELOCITY
// ============================================================================

/**
 * Apply velocity settings to a keyframe.
 * Converts velocity and influence to bezier handle values.
 *
 * @param store - The compositor store
 * @param layerId - Layer ID
 * @param propertyPath - Property path
 * @param keyframeId - Keyframe ID
 * @param settings - Velocity settings
 */
export function applyKeyframeVelocity(
  store: VelocityStoreAccess,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  settings: VelocitySettings,
): boolean {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property?.keyframes) return false;

  const kfIndex = property.keyframes.findIndex((kf) => kf.id === keyframeId);
  if (kfIndex < 0) return false;

  const keyframe = property.keyframes[kfIndex];
  const prevKf = kfIndex > 0 ? property.keyframes[kfIndex - 1] : null;
  const nextKf =
    kfIndex < property.keyframes.length - 1
      ? property.keyframes[kfIndex + 1]
      : null;

  // Calculate handle frame offsets from influence percentages
  const inDuration = prevKf ? keyframe.frame - prevKf.frame : 10;
  const outDuration = nextKf ? nextKf.frame - keyframe.frame : 10;

  const inInfluence = settings.incomingInfluence / 100;
  const outInfluence = settings.outgoingInfluence / 100;

  // Convert velocity to value offset
  // Velocity is in units per second, convert to units per frame segment
  const fps = Number.isFinite(store.fps) && store.fps > 0 ? store.fps : 16;
  const inVelocityPerFrame = settings.incomingVelocity / fps;
  const outVelocityPerFrame = settings.outgoingVelocity / fps;

  // Set bezier handles
  keyframe.inHandle = {
    frame: -inDuration * inInfluence,
    value: -inVelocityPerFrame * inDuration * inInfluence,
    enabled: true,
  };

  keyframe.outHandle = {
    frame: outDuration * outInfluence,
    value: outVelocityPerFrame * outDuration * outInfluence,
    enabled: true,
  };

  // Ensure interpolation is bezier
  keyframe.interpolation = "bezier";

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Get the current velocity settings from a keyframe's handles.
 */
export function getKeyframeVelocity(
  store: VelocityStoreAccess,
  layerId: string,
  propertyPath: string,
  keyframeId: string,
): VelocitySettings | null {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return null;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property?.keyframes) return null;

  const kfIndex = property.keyframes.findIndex((kf) => kf.id === keyframeId);
  if (kfIndex < 0) return null;

  const keyframe = property.keyframes[kfIndex];
  const prevKf = kfIndex > 0 ? property.keyframes[kfIndex - 1] : null;
  const nextKf =
    kfIndex < property.keyframes.length - 1
      ? property.keyframes[kfIndex + 1]
      : null;

  // Calculate durations
  const inDuration = prevKf ? keyframe.frame - prevKf.frame : 10;
  const outDuration = nextKf ? nextKf.frame - keyframe.frame : 10;

  // Extract influence from handle frame offset (guard against div/0)
  const inInfluence =
    keyframe.inHandle?.enabled && inDuration > 0
      ? (Math.abs(keyframe.inHandle.frame) / inDuration) * 100
      : 33.33;

  const outInfluence =
    keyframe.outHandle?.enabled && outDuration > 0
      ? (keyframe.outHandle.frame / outDuration) * 100
      : 33.33;

  // Convert value offset back to velocity (validate fps)
  const fps = Number.isFinite(store.fps) && store.fps > 0 ? store.fps : 16;
  const inHandleFrame = Math.abs(keyframe.inHandle?.frame ?? 0);
  const inVelocity =
    keyframe.inHandle?.enabled && inHandleFrame > 0
      ? (-keyframe.inHandle.value / inHandleFrame) * fps
      : 0;

  const outHandleFrame = keyframe.outHandle?.frame ?? 0;
  const outVelocity =
    keyframe.outHandle?.enabled && outHandleFrame !== 0
      ? (keyframe.outHandle.value / outHandleFrame) * fps
      : 0;

  return {
    incomingVelocity: inVelocity,
    outgoingVelocity: outVelocity,
    incomingInfluence: Math.min(100, Math.max(0, inInfluence)),
    outgoingInfluence: Math.min(100, Math.max(0, outInfluence)),
  };
}
