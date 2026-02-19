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

import { isFiniteNumber } from "@/utils/typeGuards";
import type { Layer, AnimatableProperty } from "@/types/project";
import type { AudioMapping } from "./audioReactiveMapping";
import { interpolateProperty } from "./interpolation";
import { storeLogger } from "@/utils/logger";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

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
 * Note: null is only used internally for error propagation, never returned to callers
 */
export type PropertyValueResult = number | number[];

// ════════════════════════════════════════════════════════════════════════════
//                                           // main // evaluation // functions
// ════════════════════════════════════════════════════════════════════════════

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
 * @returns Evaluated property value
 * @throws Error if layer or property is not found
 */
export function evaluatePropertyAtFrame(
  access: PropertyEvaluatorAccess,
  layerId: string,
  propertyPath: string,
  frame: number,
): PropertyValueResult {
  const layer = access.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[PropertyEvaluator] Cannot evaluate property "${propertyPath}" at frame ${frame}: Layer "${layerId}" not found`);
  }

  const fps = access.fps;
  const duration = access.frameCount / fps;

  // Step 1: Get base value from keyframe interpolation (includes expressions)
  let value = getKeyframeValue(layer, propertyPath, frame, fps, layerId, duration);

  if (value === null) {
    throw new Error(`[PropertyEvaluator] Cannot evaluate property "${propertyPath}" at frame ${frame} for layer "${layerId}": Property not found or has no value`);
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
): number {
  const result = evaluatePropertyAtFrame(access, layerId, propertyPath, frame);

  if (typeof result === "number") return result;

  // Extract component from path for vector properties
  const parts = propertyPath.split(".");
  const component = parts[parts.length - 1];

  if (Array.isArray(result)) {
    // Type proof: result[0/1/2] ∈ ℝ ∪ {undefined} → ℝ
    if (component === "x") {
      const xValue = result[0];
      if (typeof xValue === "number" && isFiniteNumber(xValue)) {
        return xValue;
      }
      throw new Error(`[PropertyEvaluator] Cannot get scalar property value: Property "${propertyPath}" at frame ${frame} for layer "${layerId}" has invalid x component`);
    }
    if (component === "y") {
      const yValue = result[1];
      if (typeof yValue === "number" && isFiniteNumber(yValue)) {
        return yValue;
      }
      throw new Error(`[PropertyEvaluator] Cannot get scalar property value: Property "${propertyPath}" at frame ${frame} for layer "${layerId}" has invalid y component`);
    }
    if (component === "z") {
      const zValue = result[2];
      if (typeof zValue === "number" && isFiniteNumber(zValue)) {
        return zValue;
      }
      throw new Error(`[PropertyEvaluator] Cannot get scalar property value: Property "${propertyPath}" at frame ${frame} for layer "${layerId}" has invalid z component`);
    }
    // Return first component by default for vectors
    const firstValue = result[0];
    if (typeof firstValue === "number" && isFiniteNumber(firstValue)) {
      return firstValue;
    }
    throw new Error(`[PropertyEvaluator] Cannot get scalar property value: Property "${propertyPath}" at frame ${frame} for layer "${layerId}" has invalid vector component`);
  }

  throw new Error(`[PropertyEvaluator] Cannot get scalar property value: Property "${propertyPath}" at frame ${frame} for layer "${layerId}" is not a scalar or vector property`);
}

// ════════════════════════════════════════════════════════════════════════════
//                                                 // keyframe // interpolation
// ════════════════════════════════════════════════════════════════════════════

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
    if (!t.position) {
      throw new Error(`[PropertyEvaluator] Cannot get keyframe value: Layer "${layerId}" has no position property`);
    }
    const p = interpolateProperty(t.position, frame, fps, layerId, duration);
    // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
    const zValue = p.z;
    const z = isFiniteNumber(zValue) ? zValue : 0;
    if (normalizedPath === "position") return [p.x, p.y, z];
    if (normalizedPath === "position.x") return p.x;
    if (normalizedPath === "position.y") return p.y;
    if (normalizedPath === "position.z") return z;
  }

  if (normalizedPath === "scale" || normalizedPath === "scale.x" || normalizedPath === "scale.y" || normalizedPath === "scale.z") {
    if (!t.scale) {
      throw new Error(`[PropertyEvaluator] Cannot get keyframe value: Layer "${layerId}" has no scale property`);
    }
    const s = interpolateProperty(t.scale, frame, fps, layerId, duration);
    // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
    const scaleZValue = s.z;
    const scaleZ = isFiniteNumber(scaleZValue) ? scaleZValue : 100;
    if (normalizedPath === "scale") return [s.x, s.y, scaleZ];
    if (normalizedPath === "scale.x") return s.x;
    if (normalizedPath === "scale.y") return s.y;
    if (normalizedPath === "scale.z") return scaleZ;
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
    if (!originProp) {
      throw new Error(`[PropertyEvaluator] Cannot get keyframe value: Layer "${layerId}" has no origin or anchorPoint property`);
    }
    const a = interpolateProperty(originProp, frame, fps, layerId, duration);
    if (normalizedPath === "anchorPoint" || normalizedPath === "origin") {
      // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const anchorZValue = a.z;
      const anchorZ = isFiniteNumber(anchorZValue) ? anchorZValue : 0;
      return [a.x, a.y, anchorZ];
    }
    if (normalizedPath.endsWith(".x")) return a.x;
    if (normalizedPath.endsWith(".y")) return a.y;
    if (normalizedPath.endsWith(".z")) {
      // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const anchorZValue = a.z;
      return isFiniteNumber(anchorZValue) ? anchorZValue : 0;
    }
  }

  if (normalizedPath === "orientation" && t.orientation) {
    const o = interpolateProperty(t.orientation, frame, fps, layerId, duration);
    // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
    const orientZValue = o.z;
    const orientZ = isFiniteNumber(orientZValue) ? orientZValue : 0;
    return [o.x, o.y, orientZ];
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
      // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const posZValue = posValue.z;
      const posZ = isFiniteNumber(posZValue) ? posZValue : 0;
      return [posValue.x, posValue.y, posZ];
    }
    return value as PropertyValueResult;
  }

  throw new Error(`[PropertyEvaluator] Cannot get keyframe value: Property "${propertyPath}" not found on layer "${layerId}"`);
}

// ════════════════════════════════════════════════════════════════════════════
//                                              // audio // reactive // mapping
// ════════════════════════════════════════════════════════════════════════════

/**
 * Apply audio reactive mapping to a property value.
 *
 * Audio mappings modify property values based on audio analysis data
 * (amplitude, frequency bands, beats).
 */
function applyAudioMapping(
  baseValue: PropertyValueResult | null,
  layerId: string,
  _propertyPath: string,
  frame: number,
  mappings: AudioMapping[],
  audioAnalysis: AudioAnalysisData | null,
): PropertyValueResult {
  if (!audioAnalysis || mappings.length === 0) {
    if (baseValue === null) {
      throw new Error(`[PropertyEvaluator] Cannot apply audio mapping: Base value is null for layer "${layerId}" at frame ${frame}`);
    }
    return baseValue;
  }

  // Find mapping for this layer (AudioMapping uses targetLayerId and target, not propertyPath)
  const mapping = mappings.find(
    (m) => m.targetLayerId === layerId && m.enabled,
  );

  if (!mapping) {
    if (baseValue === null) {
      throw new Error(`[PropertyEvaluator] Cannot apply audio mapping: Base value is null for layer "${layerId}" at frame ${frame}`);
    }
    return baseValue;
  }

  // Get audio value for this frame based on feature type
  let audioValue = 0;
  const frameIndex = Math.floor(frame);

  switch (mapping.feature) {
    case "amplitude": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: amplitudeEnvelope ∈ number[] | undefined → number[]
      const amplitudeEnvelope = Array.isArray(audioAnalysis.amplitudeEnvelope)
        ? audioAnalysis.amplitudeEnvelope
        : [];
      // Pattern match: array access with bounds check - no undefined assignment
      if (frameIndex >= 0 && frameIndex < amplitudeEnvelope.length && typeof amplitudeEnvelope[frameIndex] === "number") {
        const ampValue = amplitudeEnvelope[frameIndex];
        audioValue = isFiniteNumber(ampValue) ? ampValue : 0;
      } else {
        audioValue = 0;
      }
      break;
    }
    case "bass": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: frequencyBands.bass ∈ number[] | undefined → number[]
      const frequencyBands = (typeof audioAnalysis.frequencyBands === "object" && audioAnalysis.frequencyBands !== null && "bass" in audioAnalysis.frequencyBands && Array.isArray(audioAnalysis.frequencyBands.bass))
        ? audioAnalysis.frequencyBands.bass
        : [];
      // Pattern match: array access with bounds check - no undefined assignment
      if (frameIndex >= 0 && frameIndex < frequencyBands.length && typeof frequencyBands[frameIndex] === "number") {
        const bassValue = frequencyBands[frameIndex];
        audioValue = isFiniteNumber(bassValue) ? bassValue : 0;
      } else {
        audioValue = 0;
      }
      break;
    }
    case "mid": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: frequencyBands.mid ∈ number[] | undefined → number[]
      const frequencyBandsMid = (typeof audioAnalysis.frequencyBands === "object" && audioAnalysis.frequencyBands !== null && "mid" in audioAnalysis.frequencyBands && Array.isArray(audioAnalysis.frequencyBands.mid))
        ? audioAnalysis.frequencyBands.mid
        : [];
      // Pattern match: array access with bounds check - no undefined assignment
      if (frameIndex >= 0 && frameIndex < frequencyBandsMid.length && typeof frequencyBandsMid[frameIndex] === "number") {
        const midValue = frequencyBandsMid[frameIndex];
        audioValue = isFiniteNumber(midValue) ? midValue : 0;
      } else {
        audioValue = 0;
      }
      break;
    }
    case "high": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: frequencyBands.high ∈ number[] | undefined → number[]
      const frequencyBandsHigh = (typeof audioAnalysis.frequencyBands === "object" && audioAnalysis.frequencyBands !== null && "high" in audioAnalysis.frequencyBands && Array.isArray(audioAnalysis.frequencyBands.high))
        ? audioAnalysis.frequencyBands.high
        : [];
      // Pattern match: array access with bounds check - no undefined assignment
      if (frameIndex >= 0 && frameIndex < frequencyBandsHigh.length && typeof frequencyBandsHigh[frameIndex] === "number") {
        const highValue = frequencyBandsHigh[frameIndex];
        audioValue = isFiniteNumber(highValue) ? highValue : 0;
      } else {
        audioValue = 0;
      }
      break;
    }
    case "spectralFlux":
    case "onsets":
    case "peaks": {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      const beats = Array.isArray(audioAnalysis.beats)
        ? audioAnalysis.beats
        : [];
      const hasBeat = beats.includes(frameIndex);
      audioValue = hasBeat === true ? 1 : 0;
      break;
    }
    default: {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: amplitudeEnvelope ∈ number[] | undefined → number[]
      const amplitudeEnvelope = Array.isArray(audioAnalysis.amplitudeEnvelope)
        ? audioAnalysis.amplitudeEnvelope
        : [];
      // Pattern match: array access with bounds check - no undefined assignment
      if (frameIndex >= 0 && frameIndex < amplitudeEnvelope.length && typeof amplitudeEnvelope[frameIndex] === "number") {
        const ampValue = amplitudeEnvelope[frameIndex];
        audioValue = isFiniteNumber(ampValue) ? ampValue : 0;
      } else {
        audioValue = 0;
      }
      break;
    }
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
  if (baseValue === null) {
    throw new Error(`[PropertyEvaluator] Cannot apply audio mapping: Base value is null for layer "${layerId}" at frame ${frame}`);
  }
  if (typeof baseValue === "number") {
    return baseValue + mappedValue;
  }

  // For vector values, apply to all components
  if (Array.isArray(baseValue)) {
    return baseValue.map((v) => v + mappedValue);
  }

  throw new Error(`[PropertyEvaluator] Cannot apply audio mapping: Base value is invalid type for layer "${layerId}" at frame ${frame}`);
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // utility // functions
// ════════════════════════════════════════════════════════════════════════════

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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  return (typeof property.expression === "object" && property.expression !== null && "enabled" in property.expression && property.expression.enabled === true);
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
