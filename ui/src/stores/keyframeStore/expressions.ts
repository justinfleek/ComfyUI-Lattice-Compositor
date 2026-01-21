/**
 * Property Expression Operations
 *
 * Set, enable, disable, toggle, remove, get expressions on properties.
 * Also includes expression-to-keyframe conversion (baking).
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import { isFiniteNumber } from "@/utils/typeGuards";
import type { Keyframe, PropertyExpression, PropertyValue } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useLayerStore } from "@/stores/layerStore";
import { useProjectStore } from "../projectStore";
import { findPropertyByPath } from "./helpers";
import { evaluatePropertyAtFrame } from "./evaluation";

// ============================================================================
// EXPRESSION METHODS
// ============================================================================

/**
 * Set an expression on a property.
 */
export function setPropertyExpression(
  layerId: string,
  propertyPath: string,
  expression: PropertyExpression,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("setPropertyExpression: layer not found:", layerId);
    return false;
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    storeLogger.warn(
      "setPropertyExpression: property not found:",
      propertyPath,
    );
    return false;
  }

  property.expression = expression;
  projectStore.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  projectStore.pushHistory();

  storeLogger.debug("Set expression on", propertyPath, ":", expression.name);
  return true;
}

/**
 * Enable expression on a property (creates default if not exists).
 */
export function enablePropertyExpression(
  layerId: string,
  propertyPath: string,
  expressionName: string = "custom",
  params: Record<string, number | string | boolean> = {},
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return false;

  const expression: PropertyExpression = {
    enabled: true,
    type: expressionName === "custom" ? "custom" : "preset",
    name: expressionName,
    params,
  };

  property.expression = expression;
  projectStore.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  projectStore.pushHistory();

  return true;
}

/**
 * Disable expression on a property (keeps expression data for re-enabling).
 */
export function disablePropertyExpression(
  layerId: string,
  propertyPath: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || !property.expression) return false;

  property.expression.enabled = false;
  projectStore.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  projectStore.pushHistory();

  return true;
}

/**
 * Toggle expression enabled state.
 */
export function togglePropertyExpression(
  layerId: string,
  propertyPath: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || !property.expression) return false;

  property.expression.enabled = !property.expression.enabled;
  projectStore.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  projectStore.pushHistory();

  return property.expression.enabled;
}

/**
 * Remove expression from a property.
 */
export function removePropertyExpression(
  layerId: string,
  propertyPath: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return false;

  delete property.expression;
  projectStore.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  projectStore.pushHistory();

  return true;
}

/**
 * Get expression on a property.
 */
export function getPropertyExpression(
  layerId: string,
  propertyPath: string,
): PropertyExpression {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[KeyframeStore] Cannot get property expression: Layer "${layerId}" not found`);
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    throw new Error(`[KeyframeStore] Cannot get property expression: Property "${propertyPath}" not found on layer "${layerId}"`);
  }
  if (!property.expression) {
    throw new Error(`[KeyframeStore] Property "${propertyPath}" on layer "${layerId}" has no expression`);
  }
  return property.expression;
}

/**
 * Check if property has an expression.
 */
export function hasPropertyExpression(
  layerId: string,
  propertyPath: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const propertyExpression = (property != null && typeof property === "object" && "expression" in property && property.expression != null) ? property.expression : undefined;
  return propertyExpression !== undefined;
}

/**
 * Update expression parameters.
 */
export function updateExpressionParams(
  layerId: string,
  propertyPath: string,
  params: Record<string, number | string | boolean>,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || !property.expression) return false;

  property.expression.params = { ...property.expression.params, ...params };
  projectStore.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  projectStore.pushHistory();

  return true;
}

// ============================================================================
// CONVERT EXPRESSION TO KEYFRAMES (BAKE)
// ============================================================================

/**
 * Convert an expression to keyframes by sampling at every frame.
 * This "bakes" the expression result into keyframes.
 *
 * @param store - Store with expression evaluation capability
 * @param layerId - Layer ID
 * @param propertyPath - Property path with expression
 * @param startFrame - Start frame (default: 0)
 * @param endFrame - End frame (default: composition duration)
 * @param sampleRate - Sample every N frames (default: 1 = every frame)
 * @returns Number of keyframes created
 */
export function convertExpressionToKeyframes(
  layerId: string,
  propertyPath: string,
  startFrame?: number,
  endFrame?: number,
  sampleRate: number = 1,
): number {
  const projectStore = useProjectStore();
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(layerId);
  if (!layer) {
    storeLogger.warn("convertExpressionToKeyframes: layer not found:", layerId);
    return 0;
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    storeLogger.warn(
      "convertExpressionToKeyframes: property not found:",
      propertyPath,
    );
    return 0;
  }

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const propertyExpression = (property != null && typeof property === "object" && "expression" in property && property.expression != null && typeof property.expression === "object") ? property.expression : undefined;
  const expressionEnabled = (propertyExpression != null && typeof propertyExpression === "object" && "enabled" in propertyExpression && typeof propertyExpression.enabled === "boolean" && propertyExpression.enabled) ? true : false;
  if (!expressionEnabled) {
    storeLogger.warn(
      "convertExpressionToKeyframes: no active expression on property",
    );
    return 0;
  }

  // Type proof: startFrame ∈ ℕ ∪ {undefined} → ℕ
  const startFrameValue = startFrame;
  const start = isFiniteNumber(startFrameValue) && Number.isInteger(startFrameValue) && startFrameValue >= 0 ? startFrameValue : 0;
  // Type proof: endFrame ∈ ℕ ∪ {undefined} → ℕ
  const endFrameValue = endFrame;
  const end = isFiniteNumber(endFrameValue) && Number.isInteger(endFrameValue) && endFrameValue >= 0 ? endFrameValue : projectStore.getFrameCount();
  // Validate sampleRate (Math.round(NaN) = NaN, Math.max(1, NaN) = NaN)
  const rate = Number.isFinite(sampleRate)
    ? Math.max(1, Math.round(sampleRate))
    : 1;

  // Clear existing keyframes
  property.keyframes = [];
  property.animated = true;

  let keyframesCreated = 0;

  // Sample expression at each frame
  for (let frame = start; frame <= end; frame += rate) {
    const value = evaluatePropertyAtFrame(layerId, propertyPath, frame);

    if (value !== undefined && value !== null) {
      // Convert array values [x, y] or [x, y, z] to object format for PropertyValue
      let keyframeValue: PropertyValue;
      if (Array.isArray(value)) {
        if (value.length === 2) {
          keyframeValue = { x: value[0], y: value[1] };
        } else if (value.length >= 3) {
          keyframeValue = { x: value[0], y: value[1], z: value[2] };
        } else {
          // Type proof: value[0] ∈ ℝ ∪ {undefined} → ℝ
          const firstValue = value[0];
          keyframeValue = isFiniteNumber(firstValue) ? firstValue : 0;
        }
      } else {
        keyframeValue = value;
      }

      const keyframe: Keyframe<PropertyValue> = {
        id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
        frame,
        value: keyframeValue,
        interpolation: "linear",
        inHandle: { frame: 0, value: 0, enabled: false },
        outHandle: { frame: 0, value: 0, enabled: false },
        controlMode: "smooth",
      };

      property.keyframes.push(keyframe);
      keyframesCreated++;
    }
  }

  // Disable the expression after baking
  if (property.expression) {
    property.expression.enabled = false;
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  storeLogger.info(
    "convertExpressionToKeyframes: created",
    keyframesCreated,
    "keyframes",
  );
  return keyframesCreated;
}

/**
 * Check if a property has a bakeable expression.
 */
export function canBakeExpression(
  layerId: string,
  propertyPath: string,
): boolean {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return false;

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const propertyExpression = (property != null && typeof property === "object" && "expression" in property && property.expression != null && typeof property.expression === "object") ? property.expression : undefined;
  const expressionEnabled = (propertyExpression != null && typeof propertyExpression === "object" && "enabled" in propertyExpression && typeof propertyExpression.enabled === "boolean" && propertyExpression.enabled) ? true : false;
  return expressionEnabled === true;
}
