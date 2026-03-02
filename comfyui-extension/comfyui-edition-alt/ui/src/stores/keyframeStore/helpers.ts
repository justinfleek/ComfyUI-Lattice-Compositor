/**
 * Keyframe Store Helpers
 *
 * Utility functions used across keyframe operations.
 */

import type { AnimatableProperty, Layer } from "@/types/project";
import type { PropertyValue } from "@/types/animation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // frame // validation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Validate and sanitize frame number, returning fallback if invalid.
 * Guards against NaN, undefined, null, and Infinity.
 */
export function safeFrame(frame: number | undefined | null, fallback = 0): number {
  // Explicit check: validate frame is finite number
  if (frame !== null && frame !== undefined && Number.isFinite(frame)) {
    return frame;
  }
  return fallback;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                        // property // lookup
// ════════════════════════════════════════════════════════════════════════════

/**
 * Find a property by its path on a layer.
 * Supports both 'position' and 'transform.position' formats.
 * Also supports nested paths for mesh warp pins and pose keypoints:
 * - 'warpPins.${pinId}.position'
 * - 'warpPins.${pinId}.rotation'
 * - 'warpPins.${pinId}.scale'
 * - 'animatedKeypoints.${keypointId}'
 *
 * @param layer - The layer to search
 * @param propertyPath - Path to the property (e.g., 'position', 'transform.position', 'opacity', 'warpPins.pin_123.position')
 * @returns The animatable property or undefined if not found
 */
export function findPropertyByPath(
  layer: Layer,
  propertyPath: string,
): AnimatableProperty<PropertyValue> | undefined {
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

  // Check nested paths for mesh warp pins (spline layers)
  // Format: warpPins.${pinId}.position|rotation|scale|inFront
  if (propertyPath.startsWith("warpPins.") || propertyPath.startsWith("puppetPins.")) {
    const parts = propertyPath.split(".");
    if (parts.length === 3) {
      const pinsKey = parts[0]; // 'warpPins' or 'puppetPins'
      const pinId = parts[1];
      const propName = parts[2]; // 'position', 'rotation', 'scale', 'inFront'
      
      if (layer.type === "spline" && layer.data) {
        const splineData = layer.data as import("@/types/spline").SplineData;
        // Support both warpPins and deprecated puppetPins
        // Type-safe property access: check for specific known properties
        let pins: import("@/types/meshWarp").WarpPin[] | undefined;
        if (pinsKey === "warpPins" && splineData.warpPins !== undefined && Array.isArray(splineData.warpPins)) {
          pins = splineData.warpPins;
        } else if (pinsKey === "puppetPins" && splineData.puppetPins !== undefined && Array.isArray(splineData.puppetPins)) {
          pins = splineData.puppetPins;
        }
        
        if (pins) {
          const pin = pins.find((p) => p.id === pinId);
          if (pin) {
            if (propName === "position") return pin.position as AnimatableProperty<PropertyValue>;
            if (propName === "rotation") return pin.rotation as AnimatableProperty<PropertyValue>;
            if (propName === "scale") return pin.scale as AnimatableProperty<PropertyValue>;
            if (propName === "inFront" && pin.inFront) return pin.inFront as AnimatableProperty<PropertyValue>;
          }
        }
      }
      return undefined;
    }
  }

  // Check nested paths for pose layer animated keypoints
  // Format: animatedKeypoints.${keypointId}
  if (propertyPath.startsWith("animatedKeypoints.")) {
    const parts = propertyPath.split(".");
    if (parts.length === 2) {
      const keypointId = parts[1];
      
      if (layer.type === "pose" && layer.data) {
        // Type-safe access: layer.data must have animatedKeypoints for pose layers
        const layerData = layer.data;
        const animatedKeypoints = (layerData !== null && typeof layerData === "object" && "animatedKeypoints" in layerData && layerData.animatedKeypoints !== null && typeof layerData.animatedKeypoints === "object")
          ? layerData.animatedKeypoints as Record<string, AnimatableProperty<import("@/types/project").Vec2>>
          : undefined;

        if (animatedKeypoints && keypointId in animatedKeypoints) {
          return animatedKeypoints[keypointId] as AnimatableProperty<PropertyValue>;
        }
      }
      return undefined;
    }
  }

  // Check custom properties by name or id
  return layer.properties.find(
    (p) => p.name === propertyPath || p.id === propertyPath,
  );
}
