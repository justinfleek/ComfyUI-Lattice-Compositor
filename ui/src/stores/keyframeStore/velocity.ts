/**
 * Keyframe Velocity Operations
 *
 * Apply and retrieve velocity settings for keyframe handles.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import { isFiniteNumber } from "@/utils/typeGuards";
import { findPropertyByPath } from "./helpers";
import type { VelocitySettings } from "./types";
import { useProjectStore } from "../projectStore";
import { useLayerStore } from "../layerStore";

// ============================================================================
// KEYFRAME VELOCITY
// ============================================================================

/**
 * Apply velocity settings to a keyframe.
 * Converts velocity and influence to bezier handle values.
 *
 * @param layerId - Layer ID
 * @param propertyPath - Property path
 * @param keyframeId - Keyframe ID
 * @param settings - Velocity settings
 */
export function applyKeyframeVelocity(
  layerId: string,
  propertyPath: string,
  keyframeId: string,
  settings: VelocitySettings,
): boolean {
  const projectStore = useProjectStore();
  const layerStore = useLayerStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (property == null || typeof property !== "object" || !("keyframes" in property) || property.keyframes == null || !Array.isArray(property.keyframes)) return false;

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
  const fps = projectStore.getFps();
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
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  return true;
}

/**
 * Get the current velocity settings from a keyframe's handles.
 */
export function getKeyframeVelocity(
  layerId: string,
  propertyPath: string,
  keyframeId: string,
): VelocitySettings {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[KeyframeStore] Cannot get keyframe velocity: Layer "${layerId}" not found`);
  }

  const property = findPropertyByPath(layer, propertyPath);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (property == null || typeof property !== "object" || !("keyframes" in property) || property.keyframes == null || !Array.isArray(property.keyframes)) {
    throw new Error(`[KeyframeStore] Cannot get keyframe velocity: Property "${propertyPath}" not found or has no keyframes on layer "${layerId}"`);
  }

  const kfIndex = property.keyframes.findIndex((kf) => kf.id === keyframeId);
  if (kfIndex < 0) {
    throw new Error(`[KeyframeStore] Cannot get keyframe velocity: Keyframe "${keyframeId}" not found in property "${propertyPath}" on layer "${layerId}"`);
  }

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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const inHandle = (keyframe != null && typeof keyframe === "object" && "inHandle" in keyframe && keyframe.inHandle != null && typeof keyframe.inHandle === "object") ? keyframe.inHandle : undefined;
  const inHandleEnabled = (inHandle != null && typeof inHandle === "object" && "enabled" in inHandle && typeof inHandle.enabled === "boolean" && inHandle.enabled) ? true : false;
  const inInfluence =
    inHandleEnabled && inDuration > 0
      ? (Math.abs(inHandle.frame) / inDuration) * 100
      : 33.33;

  const outHandle = (keyframe != null && typeof keyframe === "object" && "outHandle" in keyframe && keyframe.outHandle != null && typeof keyframe.outHandle === "object") ? keyframe.outHandle : undefined;
  const outHandleEnabled = (outHandle != null && typeof outHandle === "object" && "enabled" in outHandle && typeof outHandle.enabled === "boolean" && outHandle.enabled) ? true : false;
  const outInfluence =
    outHandleEnabled && outDuration > 0
      ? (outHandle.frame / outDuration) * 100
      : 33.33;

  // Convert value offset back to velocity (validate fps)
  const fps = projectStore.getFps();
  // Type proof: inHandle?.frame ∈ ℝ ∪ {undefined} → ℝ
  const inHandleFrameValue = (inHandle != null && typeof inHandle === "object" && "frame" in inHandle && typeof inHandle.frame === "number") ? inHandle.frame : undefined;
  const inHandleFrameRaw = isFiniteNumber(inHandleFrameValue) ? inHandleFrameValue : 0;
  const inHandleFrame = Math.abs(inHandleFrameRaw);
  const inVelocity =
    inHandleEnabled && inHandleFrame > 0
      ? (-inHandle.value / inHandleFrame) * fps
      : 0;

  // Type proof: outHandle?.frame ∈ ℝ ∪ {undefined} → ℝ
  const outHandleFrameValue = (outHandle != null && typeof outHandle === "object" && "frame" in outHandle && typeof outHandle.frame === "number") ? outHandle.frame : undefined;
  const outHandleFrame = isFiniteNumber(outHandleFrameValue) ? outHandleFrameValue : 0;
  const outVelocity =
    outHandleEnabled && outHandleFrame !== 0
      ? (outHandle.value / outHandleFrame) * fps
      : 0;

  return {
    incomingVelocity: inVelocity,
    outgoingVelocity: outVelocity,
    incomingInfluence: Math.min(100, Math.max(0, inInfluence)),
    outgoingInfluence: Math.min(100, Math.max(0, outInfluence)),
  };
}
