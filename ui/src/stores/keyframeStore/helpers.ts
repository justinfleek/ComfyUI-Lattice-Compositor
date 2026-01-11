/**
 * Keyframe Store Helpers
 *
 * Utility functions used across keyframe operations.
 */

import type { AnimatableProperty, Layer } from "@/types/project";

// ============================================================================
// FRAME VALIDATION
// ============================================================================

/**
 * Validate and sanitize frame number, returning fallback if invalid.
 * Guards against NaN, undefined, null, and Infinity.
 */
export function safeFrame(frame: number | undefined | null, fallback = 0): number {
  return Number.isFinite(frame) ? frame! : fallback;
}

// ============================================================================
// PROPERTY LOOKUP
// ============================================================================

/**
 * Find a property by its path on a layer.
 * Supports both 'position' and 'transform.position' formats.
 *
 * @param layer - The layer to search
 * @param propertyPath - Path to the property (e.g., 'position', 'transform.position', 'opacity')
 * @returns The animatable property or undefined if not found
 */
export function findPropertyByPath(
  layer: Layer,
  propertyPath: string,
): AnimatableProperty<any> | undefined {
  // Normalize path - strip 'transform.' prefix if present
  const normalizedPath = propertyPath.replace(/^transform\./, "");

  // Check transform properties
  if (normalizedPath === "position") {
    return layer.transform.position;
  }
  if (normalizedPath === "scale") {
    return layer.transform.scale;
  }
  if (normalizedPath === "rotation") {
    return layer.transform.rotation;
  }
  if (normalizedPath === "anchorPoint") {
    return layer.transform.anchorPoint;
  }
  if (normalizedPath === "origin") {
    return layer.transform.origin;
  }
  if (propertyPath === "opacity") {
    return layer.opacity;
  }

  // Check 3D rotation properties
  if (normalizedPath === "rotationX" && layer.transform.rotationX) {
    return layer.transform.rotationX;
  }
  if (normalizedPath === "rotationY" && layer.transform.rotationY) {
    return layer.transform.rotationY;
  }
  if (normalizedPath === "rotationZ" && layer.transform.rotationZ) {
    return layer.transform.rotationZ;
  }
  if (normalizedPath === "orientation" && layer.transform.orientation) {
    return layer.transform.orientation;
  }

  // Check custom properties by name or id
  return layer.properties.find(
    (p) => p.name === propertyPath || p.id === propertyPath,
  );
}
