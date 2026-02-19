/**
 * Property Evaluation
 *
 * Functions for evaluating property values at specific frames.
 * Handles transform properties, custom properties, and returns appropriate types.
 */

import { interpolateProperty } from "@/services/interpolation";
import { isFiniteNumber } from "@/utils/typeGuards";
import type { Layer, AnimatableProperty } from "@/types/project";
import type { PropertyPath } from "@/services/propertyDriver";
import { useProjectStore } from "../projectStore";
import { useAnimationStore } from "../animationStore";

/**
 * Get a single scalar property value at a specific frame.
 * Returns null if layer not found or property unsupported.
 *
 * Used by property driver system and expression evaluation.
 *
 * @param store - Store with composition and layer access
 * @param layerId - Layer ID
 * @param propertyPath - Property path (e.g., 'transform.position.x', 'opacity')
 * @param frame - Frame number to evaluate at
 * @returns Scalar value or null if not found
 */
export function getPropertyValueAtFrame(
  layerId: string,
  propertyPath: PropertyPath | string,
  frame: number,
): number {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[KeyframeStore] Cannot get property value at frame: Layer "${layerId}" not found`);
  }

  // Get composition context for expressions
  const comp = projectStore.getActiveComp();
  const fps = projectStore.getFps();
  const duration = comp
    ? comp.settings.frameCount / comp.settings.fps
    : undefined;

  const parts = (propertyPath as string).split(".");
  if (parts[0] === "transform") {
    const t = layer.transform;
    if (parts[1] === "position") {
      const p = interpolateProperty(
        t.position,
        frame,
        fps,
        layerId,
        duration,
      );
      // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const zValue = p.z;
      const z = isFiniteNumber(zValue) ? zValue : 0;
      return parts[2] === "x" ? p.x : parts[2] === "y" ? p.y : z;
    }
    if (parts[1] === "anchorPoint" || parts[1] === "origin") {
      // Use origin (new name) with fallback to anchorPoint
      const originProp = t.origin || t.anchorPoint;
      if (!originProp) return 0;
      const a = interpolateProperty(
        originProp,
        frame,
        fps,
        layerId,
        duration,
      );
      // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const zValue = a.z;
      const z = isFiniteNumber(zValue) ? zValue : 0;
      return parts[2] === "x" ? a.x : parts[2] === "y" ? a.y : z;
    }
    if (parts[1] === "scale") {
      const s = interpolateProperty(t.scale, frame, fps, layerId, duration);
      // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const zValue = s.z;
      const z = isFiniteNumber(zValue) ? zValue : 100;
      return parts[2] === "x" ? s.x : parts[2] === "y" ? s.y : z;
    }
    if (parts[1] === "rotation")
      return interpolateProperty(t.rotation, frame, fps, layerId, duration);
    if (parts[1] === "rotationX" && t.rotationX)
      return interpolateProperty(
        t.rotationX,
        frame,
        fps,
        layerId,
        duration,
      );
    if (parts[1] === "rotationY" && t.rotationY)
      return interpolateProperty(
        t.rotationY,
        frame,
        fps,
        layerId,
        duration,
      );
    if (parts[1] === "rotationZ" && t.rotationZ)
      return interpolateProperty(
        t.rotationZ,
        frame,
        fps,
        layerId,
        duration,
      );
  }
  if (parts[0] === "opacity") {
    return interpolateProperty(layer.opacity, frame, fps, layerId, duration);
  }
  throw new Error(`[KeyframeStore] Cannot get property value at frame: Unknown property path "${propertyPath}" on layer "${layerId}"`);
}

/**
 * Evaluate a property at a specific frame and return the full value.
 * Returns the interpolated value as an array for position/scale/origin types,
 * or a single value for scalar types (rotation, opacity).
 *
 * Used by MotionPathOverlay to get full position values for path rendering.
 *
 * @param store - Store with composition and layer access
 * @param layerId - Layer ID
 * @param propertyPath - Property path (e.g., 'position', 'transform.position', 'opacity')
 * @param frame - Frame number to evaluate at
 * @returns Array for vector properties, number for scalars, null if not found
 */
export function evaluatePropertyAtFrame(
  layerId: string,
  propertyPath: string,
  frame: number,
): number[] | number {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    throw new Error(`[KeyframeStore] Cannot get property value at frame: Layer "${layerId}" not found`);
  }

  // Get composition context for expressions
  const comp = projectStore.getActiveComp();
  const fps = projectStore.getFps();
  const duration = comp
    ? comp.settings.frameCount / comp.settings.fps
    : undefined;

  // Normalize path
  const normalizedPath = propertyPath.replace(/^transform\./, "");

  // Handle transform properties
  const t = layer.transform;

  if (normalizedPath === "position" && t.position) {
    const p = interpolateProperty(
      t.position,
      frame,
      fps,
      layerId,
      duration,
    );
    // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
    const zValue = p.z;
    const z = isFiniteNumber(zValue) ? zValue : 0;
    return [p.x, p.y, z];
  }

  if (
    (normalizedPath === "anchorPoint" || normalizedPath === "origin") &&
    (t.origin || t.anchorPoint)
  ) {
    const originProp = t.origin || t.anchorPoint;
    if (!originProp) {
      throw new Error(`[KeyframeStore] Cannot get layer origin: Layer "${layerId}" has no origin or anchorPoint property`);
    }
    const a = interpolateProperty(
      originProp,
      frame,
      fps,
      layerId,
      duration,
    );
    // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
    const zValue = a.z;
    const z = isFiniteNumber(zValue) ? zValue : 0;
    return [a.x, a.y, z];
  }

  if (normalizedPath === "scale" && t.scale) {
    const s = interpolateProperty(t.scale, frame, fps, layerId, duration);
    // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
    const zValue = s.z;
    const z = isFiniteNumber(zValue) ? zValue : 100;
    return [s.x, s.y, z];
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

  if (normalizedPath === "orientation" && t.orientation) {
    const o = interpolateProperty(
      t.orientation,
      frame,
      fps,
      layerId,
      duration,
    );
    // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
    const zValue = o.z;
    const z = isFiniteNumber(zValue) ? zValue : 0;
    return [o.x, o.y, z];
  }

  if (propertyPath === "opacity" && layer.opacity) {
    return interpolateProperty(
      layer.opacity,
      frame,
      fps,
      layerId,
      duration,
    );
  }

  // Check custom properties
  const customProp = layer.properties.find(
    (p) => p.name === propertyPath || p.id === propertyPath,
  );
  if (customProp) {
    const value = interpolateProperty(
      customProp,
      frame,
      fps,
      layerId,
      duration,
    );
    // If it's a position-like value with x/y, return as array
    if (
      value &&
      typeof value === "object" &&
      "x" in value &&
      "y" in value
    ) {
      // Type guard for position-like objects
      const posValue = value as { x: number; y: number; z?: number };
      // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
      const zValue = posValue.z;
      const z = isFiniteNumber(zValue) ? zValue : 0;
      return [posValue.x, posValue.y, z];
    }
    return value;
  }

  throw new Error(`[KeyframeStore] Cannot evaluate property "${propertyPath}" at frame ${frame} for layer "${layerId}": Property not found or unsupported`);
}

/**
 * Get interpolated value for any animatable property at current frame.
 * Convenience method that passes fps and duration from composition settings.
 *
 * @param property - The animatable property to interpolate
 * @returns The interpolated value at the current frame
 */
export function getInterpolatedValue<T>(
  property: AnimatableProperty<T>,
): T {
  const projectStore = useProjectStore();
  const animationStore = useAnimationStore();
  const comp = projectStore.getActiveComp();
  const frame = animationStore.currentFrame;
  const fps = projectStore.getFps();
  const duration = comp
    ? comp.settings.frameCount / comp.settings.fps
    : undefined;
  return interpolateProperty(property, frame, fps, "", duration);
}
