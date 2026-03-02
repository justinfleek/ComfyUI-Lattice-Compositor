/**
 * Global Light Service
 *
 * Manages global light settings for Layer Styles
 * When styles have useGlobalLight=true, they share this angle/altitude
 *
 * This provides a unified light source direction across all styled layers
 * in a composition, matching industry-standard behavior.
 */

import type { GlobalLightSettings } from "@/types/layerStyles";
import type { AnimatableProperty } from "@/types/project";
import { interpolateProperty } from "./interpolation";

// ============================================================================
// DEFAULT VALUES
// ============================================================================

const DEFAULT_ANGLE = 120; // Degrees (0 = right, 90 = top, counterclockwise)
const DEFAULT_ALTITUDE = 30; // Degrees (0 = horizontal, 90 = directly above)

// ============================================================================
// GLOBAL LIGHT CACHE
// ============================================================================

/**
 * Cache of global light settings per composition
 */
const globalLightCache = new Map<string, GlobalLightSettings>();

// ============================================================================
// FACTORY FUNCTIONS
// ============================================================================

/**
 * Create an animatable property with default values
 */
function createAnimatableProperty<T>(
  name: string,
  value: T,
  type: "number" | "color" | "position" = "number",
): AnimatableProperty<T> {
  return {
    id: `global-light-${name}-${Date.now()}`,
    name,
    type,
    value,
    animated: false,
    keyframes: [],
  };
}

/**
 * Create default global light settings
 */
export function createDefaultGlobalLight(): GlobalLightSettings {
  return {
    angle: createAnimatableProperty("Global Light Angle", DEFAULT_ANGLE),
    altitude: createAnimatableProperty(
      "Global Light Altitude",
      DEFAULT_ALTITUDE,
    ),
  };
}

// ============================================================================
// GETTERS
// ============================================================================

/**
 * Get global light settings for a composition
 * Creates default settings if none exist
 */
export function getGlobalLight(compositionId: string): GlobalLightSettings {
  let settings = globalLightCache.get(compositionId);
  if (!settings) {
    settings = createDefaultGlobalLight();
    globalLightCache.set(compositionId, settings);
  }
  return settings;
}

/**
 * Get the current global light angle for a composition
 * Evaluates keyframes if animated
 */
export function getGlobalLightAngle(
  compositionId: string,
  frame: number = 0,
): number {
  const settings = getGlobalLight(compositionId);

  if (settings.angle.animated && settings.angle.keyframes.length > 0) {
    // Use interpolation service for proper keyframe evaluation
    const interpolated = interpolateProperty(settings.angle, frame);
    return typeof interpolated === "number"
      ? interpolated
      : settings.angle.value;
  }

  return settings.angle.value;
}

/**
 * Get the current global light altitude for a composition
 * Evaluates keyframes if animated
 */
export function getGlobalLightAltitude(
  compositionId: string,
  frame: number = 0,
): number {
  const settings = getGlobalLight(compositionId);

  if (settings.altitude.animated && settings.altitude.keyframes.length > 0) {
    // Use interpolation service for proper keyframe evaluation
    const interpolated = interpolateProperty(settings.altitude, frame);
    return typeof interpolated === "number"
      ? interpolated
      : settings.altitude.value;
  }

  return settings.altitude.value;
}

// ============================================================================
// SETTERS
// ============================================================================

/**
 * Set the global light angle for a composition
 */
export function setGlobalLightAngle(
  compositionId: string,
  angle: number,
): void {
  const settings = getGlobalLight(compositionId);
  settings.angle.value = normalizeAngle(angle);
}

/**
 * Set the global light altitude for a composition
 */
export function setGlobalLightAltitude(
  compositionId: string,
  altitude: number,
): void {
  const settings = getGlobalLight(compositionId);
  settings.altitude.value = clamp(altitude, 0, 90);
}

/**
 * Set both angle and altitude at once
 */
export function setGlobalLightDirection(
  compositionId: string,
  angle: number,
  altitude: number,
): void {
  setGlobalLightAngle(compositionId, angle);
  setGlobalLightAltitude(compositionId, altitude);
}

/**
 * Replace the entire global light settings for a composition
 */
export function setGlobalLightSettings(
  compositionId: string,
  settings: GlobalLightSettings,
): void {
  globalLightCache.set(compositionId, settings);
}

// ============================================================================
// ANIMATION
// ============================================================================

/**
 * Enable animation on global light angle
 */
export function enableGlobalLightAngleAnimation(
  compositionId: string,
  enabled: boolean = true,
): void {
  const settings = getGlobalLight(compositionId);
  settings.angle.animated = enabled;
}

/**
 * Enable animation on global light altitude
 */
export function enableGlobalLightAltitudeAnimation(
  compositionId: string,
  enabled: boolean = true,
): void {
  const settings = getGlobalLight(compositionId);
  settings.altitude.animated = enabled;
}

// ============================================================================
// UTILITIES
// ============================================================================

/**
 * Normalize angle to 0-360 range
 */
function normalizeAngle(angle: number): number {
  angle = angle % 360;
  if (angle < 0) angle += 360;
  return angle;
}

/**
 * Clamp value to range
 */
function clamp(value: number, min: number, max: number): number {
  return Math.max(min, Math.min(max, value));
}

/**
 * Convert angle and altitude to a light direction vector (normalized)
 */
export function getLightDirection(
  compositionId: string,
  frame: number = 0,
): { x: number; y: number; z: number } {
  const angle = getGlobalLightAngle(compositionId, frame);
  const altitude = getGlobalLightAltitude(compositionId, frame);

  // Convert to radians
  const angleRad = ((angle - 90) * Math.PI) / 180; // Adjust so 0° = right
  const altitudeRad = (altitude * Math.PI) / 180;

  // Calculate direction vector
  const cosAlt = Math.cos(altitudeRad);
  return {
    x: Math.cos(angleRad) * cosAlt,
    y: -Math.sin(angleRad) * cosAlt,
    z: Math.sin(altitudeRad),
  };
}

/**
 * Calculate shadow offset from global light
 */
export function getShadowOffset(
  compositionId: string,
  distance: number,
  frame: number = 0,
): { x: number; y: number } {
  const angle = getGlobalLightAngle(compositionId, frame);
  const angleRad = ((angle - 90) * Math.PI) / 180;

  return {
    x: Math.cos(angleRad) * distance,
    y: -Math.sin(angleRad) * distance,
  };
}

// ============================================================================
// CLEANUP
// ============================================================================

/**
 * Remove global light settings for a composition
 * Called when a composition is deleted
 */
export function removeGlobalLight(compositionId: string): void {
  globalLightCache.delete(compositionId);
}

/**
 * Clear all cached global light settings
 */
export function clearGlobalLightCache(): void {
  globalLightCache.clear();
}

// ============================================================================
// SERIALIZATION
// ============================================================================

/**
 * Serialize global light settings for save
 */
export function serializeGlobalLight(
  compositionId: string,
): GlobalLightSettings | undefined {
  return globalLightCache.get(compositionId);
}

/**
 * Deserialize global light settings from save
 */
export function deserializeGlobalLight(
  compositionId: string,
  settings: GlobalLightSettings,
): void {
  globalLightCache.set(compositionId, settings);
}

// ============================================================================
// EXPORTS
// ============================================================================

export { DEFAULT_ANGLE, DEFAULT_ALTITUDE, normalizeAngle, clamp };
