/**
 * Property Evaluator Service
 *
 * Cross-domain property evaluation without circular imports.
 * Coordinates between keyframes, expressions, and audio mappings.
 *
 * Evaluation order:
 * 1. Keyframe interpolation (services/interpolation.ts)
 * 2. Expression evaluation (applied in interpolateProperty)
 * 3. Audio reactive mapping overlay (from audioStore)
 * 4. Property driver adjustments (from expressionStore)
 *
 * @see docs/MASTER_REFACTOR_PLAN.md Phase 2
 */

import type { Layer, AnimatableProperty } from "@/types/project";
import type { AudioMapping } from "./audioReactiveMapping";
import { interpolateProperty } from "./interpolation";
import { storeLogger } from "@/utils/logger";

// ============================================================================
// TYPES
// ============================================================================

/**
 * Minimal store access interface to avoid circular dependencies.
 * Components pass in store access rather than importing stores directly.
 */
export interface PropertyEvaluatorAccess {
  /** Get all layers in active composition */
  getActiveCompLayers(): Layer[];
  /** Get FPS from active composition */
  readonly fps: number;
  /** Get frame count from active composition */
  readonly frameCount: number;
  /** Get audio reactive mappings (optional) */
  getAudioMappings?(): AudioMapping[];
  /** Get audio analysis data (optional) */
  getAudioAnalysis?(): AudioAnalysisData | null;
}

/**
 * Audio analysis data structure
 */
export interface AudioAnalysisData {
  amplitudeEnvelope?: number[];
  frequencyBands?: {
    bass?: number[];
    mid?: number[];
    high?: number[];
  };
  beats?: number[];
  bpm?: number;
}

/**
 * Property value result - can be scalar or vector
 */
export type PropertyValueResult = number | number[] | null;

// ============================================================================
// MAIN EVALUATION FUNCTIONS
// ============================================================================

/**
 * Evaluate a property at a specific frame with all modifiers applied.
 *
 * This is the main entry point for property evaluation. It:
 * 1. Gets keyframe interpolation (with expression if enabled)
 * 2. Applies audio reactive mapping if configured
 * 3. Applies property driver adjustments
 *
 * @param access - Store access interface
 * @param layerId - Layer ID to evaluate
 * @param propertyPath - Property path (e.g., 'transform.position', 'opacity')
 * @param frame - Frame number to evaluate at
 * @returns Evaluated property value or null if not found
 */
export function evaluatePropertyAtFrame(
  access: PropertyEvaluatorAccess,
  layerId: string,
  propertyPath: string,
  frame: number,
): PropertyValueResult {
  const layer = access.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.warn(`evaluatePropertyAtFrame: Layer ${layerId} not found`);
    return null;
  }

  const fps = access.fps;
  const duration = access.frameCount / fps;

  // Step 1: Get base value from keyframe interpolation (includes expressions)
  let value = getKeyframeValue(layer, propertyPath, frame, fps, layerId, duration);

  if (value === null) {
    return null;
  }

  // Step 2: Apply audio reactive mapping if configured
  if (access.getAudioMappings && access.getAudioAnalysis) {
    value = applyAudioMapping(
      value,
      layerId,
      propertyPath,
      frame,
      access.getAudioMappings(),
      access.getAudioAnalysis(),
    );
  }

  return value;
}

/**
 * Get scalar property value at frame (for property drivers)
 *
 * @param access - Store access interface
 * @param layerId - Layer ID
 * @param propertyPath - Property path with component (e.g., 'transform.position.x')
 * @param frame - Frame number
 * @returns Scalar value or null
 */
export function getScalarPropertyValue(
  access: PropertyEvaluatorAccess,
  layerId: string,
  propertyPath: string,
  frame: number,
): number | null {
  const result = evaluatePropertyAtFrame(access, layerId, propertyPath, frame);

  if (result === null) return null;
  if (typeof result === "number") return result;

  // Extract component from path for vector properties
  const parts = propertyPath.split(".");
  const component = parts[parts.length - 1];

  if (Array.isArray(result)) {
    if (component === "x") return result[0] ?? null;
    if (component === "y") return result[1] ?? null;
    if (component === "z") return result[2] ?? null;
    // Return first component by default for vectors
    return result[0] ?? null;
  }

  return null;
}

// ============================================================================
// KEYFRAME INTERPOLATION
// ============================================================================

/**
 * Get interpolated keyframe value for a property.
 * This includes expression evaluation via interpolateProperty.
 */
function getKeyframeValue(
  layer: Layer,
  propertyPath: string,
  frame: number,
  fps: number,
  layerId: string,
  duration: number,
): PropertyValueResult {
  // Normalize path (remove 'transform.' prefix)
  const normalizedPath = propertyPath.replace(/^transform\./, "");
  const t = layer.transform;

  // Transform properties
  if (normalizedPath === "position" || normalizedPath === "position.x" || normalizedPath === "position.y" || normalizedPath === "position.z") {
    if (!t.position) return null;
    const p = interpolateProperty(t.position, frame, fps, layerId, duration);
    if (normalizedPath === "position") return [p.x, p.y, p.z ?? 0];
    if (normalizedPath === "position.x") return p.x;
    if (normalizedPath === "position.y") return p.y;
    if (normalizedPath === "position.z") return p.z ?? 0;
  }

  if (normalizedPath === "scale" || normalizedPath === "scale.x" || normalizedPath === "scale.y" || normalizedPath === "scale.z") {
    if (!t.scale) return null;
    const s = interpolateProperty(t.scale, frame, fps, layerId, duration);
    if (normalizedPath === "scale") return [s.x, s.y, s.z ?? 100];
    if (normalizedPath === "scale.x") return s.x;
    if (normalizedPath === "scale.y") return s.y;
    if (normalizedPath === "scale.z") return s.z ?? 100;
  }

  if (normalizedPath === "rotation" && t.rotation) {
    return interpolateProperty(t.rotation, frame, fps, layerId, duration);
  }

  if (normalizedPath === "rotationX" && t.rotationX) {
    return interpolateProperty(t.rotationX, frame, fps, layerId, duration);
  }

  if (normalizedPath === "rotationY" && t.rotationY) {
    return interpolateProperty(t.rotationY, frame, fps, layerId, duration);
  }

  if (normalizedPath === "rotationZ" && t.rotationZ) {
    return interpolateProperty(t.rotationZ, frame, fps, layerId, duration);
  }

  if (normalizedPath.startsWith("anchorPoint") || normalizedPath.startsWith("origin")) {
    const originProp = t.origin || t.anchorPoint;
    if (!originProp) return null;
    const a = interpolateProperty(originProp, frame, fps, layerId, duration);
    if (normalizedPath === "anchorPoint" || normalizedPath === "origin") {
      return [a.x, a.y, a.z ?? 0];
    }
    if (normalizedPath.endsWith(".x")) return a.x;
    if (normalizedPath.endsWith(".y")) return a.y;
    if (normalizedPath.endsWith(".z")) return a.z ?? 0;
  }

  if (normalizedPath === "orientation" && t.orientation) {
    const o = interpolateProperty(t.orientation, frame, fps, layerId, duration);
    return [o.x, o.y, o.z ?? 0];
  }

  // Opacity
  if (propertyPath === "opacity" && layer.opacity) {
    return interpolateProperty(layer.opacity, frame, fps, layerId, duration);
  }

  // Custom properties
  const customProp = layer.properties.find(
    (p) => p.name === propertyPath || p.id === propertyPath,
  );
  if (customProp) {
    const value = interpolateProperty(customProp, frame, fps, layerId, duration);
    if (value && typeof value === "object" && "x" in value && "y" in value) {
      const posValue = value as { x: number; y: number; z?: number };
      return [posValue.x, posValue.y, posValue.z ?? 0];
    }
    return value as PropertyValueResult;
  }

  return null;
}

// ============================================================================
// AUDIO REACTIVE MAPPING
// ============================================================================

/**
 * Apply audio reactive mapping to a property value.
 *
 * Audio mappings modify property values based on audio analysis data
 * (amplitude, frequency bands, beats).
 */
function applyAudioMapping(
  baseValue: PropertyValueResult,
  layerId: string,
  _propertyPath: string,
  frame: number,
  mappings: AudioMapping[],
  audioAnalysis: AudioAnalysisData | null,
): PropertyValueResult {
  if (!audioAnalysis || mappings.length === 0) {
    return baseValue;
  }

  // Find mapping for this layer (AudioMapping uses targetLayerId and target, not propertyPath)
  const mapping = mappings.find(
    (m) => m.targetLayerId === layerId && m.enabled,
  );

  if (!mapping) {
    return baseValue;
  }

  // Get audio value for this frame based on feature type
  let audioValue = 0;
  const frameIndex = Math.floor(frame);

  switch (mapping.feature) {
    case "amplitude":
      audioValue = audioAnalysis.amplitudeEnvelope?.[frameIndex] ?? 0;
      break;
    case "bass":
      audioValue = audioAnalysis.frequencyBands?.bass?.[frameIndex] ?? 0;
      break;
    case "mid":
      audioValue = audioAnalysis.frequencyBands?.mid?.[frameIndex] ?? 0;
      break;
    case "high":
      audioValue = audioAnalysis.frequencyBands?.high?.[frameIndex] ?? 0;
      break;
    case "spectralFlux":
    case "onsets":
    case "peaks":
      audioValue = audioAnalysis.beats?.includes(frameIndex) ? 1 : 0;
      break;
    default:
      audioValue = audioAnalysis.amplitudeEnvelope?.[frameIndex] ?? 0;
  }

  // Apply threshold (noise gate)
  if (audioValue < mapping.threshold) {
    audioValue = 0;
  }

  // Apply curve shaping
  if (mapping.amplitudeCurve !== 1) {
    audioValue = Math.pow(audioValue, mapping.amplitudeCurve);
  }

  // Apply sensitivity and offset
  audioValue = audioValue * mapping.sensitivity + mapping.offset;

  // Apply inversion if needed
  if (mapping.invert) {
    audioValue = 1 - audioValue;
  }

  // Clamp to min/max range
  const mappedValue = Math.max(mapping.min, Math.min(mapping.max, audioValue));

  // Apply to base value - AudioMapping doesn't have "mode", it adds by default
  if (typeof baseValue === "number") {
    return baseValue + mappedValue;
  }

  // For vector values, apply to all components
  if (Array.isArray(baseValue)) {
    return baseValue.map((v) => v + mappedValue);
  }

  return baseValue;
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/**
 * Check if a property has keyframes
 */
export function propertyHasKeyframes(property: AnimatableProperty<unknown>): boolean {
  return property.keyframes && property.keyframes.length > 0;
}

/**
 * Check if a property has an enabled expression
 */
export function propertyHasExpression(property: AnimatableProperty<unknown>): boolean {
  return property.expression?.enabled === true;
}

/**
 * Get the effective value source for a property
 */
export function getPropertyValueSource(
  property: AnimatableProperty<unknown>,
): "static" | "keyframes" | "expression" {
  if (propertyHasExpression(property)) return "expression";
  if (propertyHasKeyframes(property)) return "keyframes";
  return "static";
}
