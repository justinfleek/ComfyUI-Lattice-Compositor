/**
 * Curve Editor Coordinate Utilities
 *
 * Provides coordinate conversion functions for the curve editor (graph editor).
 * Handles transformation between frame/value space and screen pixel space.
 */

import type { AnimatableProperty, Keyframe } from "@/types/project";
import { isFiniteNumber } from "@/utils/typeGuards";
import type { PropertyValue } from "@/types/animation";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

export interface CurveViewState {
  frameStart: number;
  frameEnd: number;
  valueMin: number;
  valueMax: number;
  zoom: number;
}

export interface CurveMargin {
  top: number;
  right: number;
  bottom: number;
  left: number;
}

// Default margin values
export const DEFAULT_CURVE_MARGIN: CurveMargin = {
  top: 10,
  right: 10,
  bottom: 10,
  left: 10,
};

// ============================================================
// COORDINATE CONVERSION
// ============================================================

/**
 * Convert frame number to screen X coordinate
 */
export function frameToScreenX(
  frame: number,
  viewState: CurveViewState,
  canvasWidth: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN,
): number {
  const graphWidth = canvasWidth - margin.left - margin.right;
  const t =
    (frame - viewState.frameStart) /
    (viewState.frameEnd - viewState.frameStart);
  return margin.left + t * graphWidth;
}

/**
 * Convert screen X coordinate to frame number
 */
export function screenXToFrame(
  screenX: number,
  viewState: CurveViewState,
  canvasWidth: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN,
): number {
  const graphWidth = canvasWidth - margin.left - margin.right;
  const t = (screenX - margin.left) / graphWidth;
  return viewState.frameStart + t * (viewState.frameEnd - viewState.frameStart);
}

/**
 * Convert value to screen Y coordinate
 */
export function valueToScreenY(
  value: number,
  viewState: CurveViewState,
  canvasHeight: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN,
): number {
  const graphHeight = canvasHeight - margin.top - margin.bottom;
  const t =
    (value - viewState.valueMin) / (viewState.valueMax - viewState.valueMin);
  return canvasHeight - margin.bottom - t * graphHeight;
}

/**
 * Convert screen Y coordinate to value
 */
export function screenYToValue(
  screenY: number,
  viewState: CurveViewState,
  canvasHeight: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN,
): number {
  const graphHeight = canvasHeight - margin.top - margin.bottom;
  const t = (canvasHeight - margin.bottom - screenY) / graphHeight;
  return viewState.valueMin + t * (viewState.valueMax - viewState.valueMin);
}

// ============================================================
// KEYFRAME POSITION HELPERS
// ============================================================

/**
 * Get screen X coordinate for a keyframe
 */
export function getKeyframeScreenX(
  kf: Keyframe<PropertyValue>,
  viewState: CurveViewState,
  canvasWidth: number,
  margin?: CurveMargin,
): number {
  return frameToScreenX(kf.frame, viewState, canvasWidth, margin);
}

/**
 * Get screen Y coordinate for a keyframe
 */
export function getKeyframeScreenY(
  _prop: AnimatableProperty<PropertyValue>,
  kf: Keyframe<PropertyValue>,
  viewState: CurveViewState,
  canvasHeight: number,
  margin?: CurveMargin,
): number {
  const value = getNumericValue(kf.value);
  return valueToScreenY(value, viewState, canvasHeight, margin);
}

/**
 * Type for position/vector values that can be extracted from keyframes
 */
interface PositionLike {
  x?: number;
  y?: number;
  z?: number;
}

/**
 * Type guard for position-like objects
 */
function isPositionLike(value: RuntimeValue): value is PositionLike {
  return (
    typeof value === "object" &&
    value !== null &&
    ("x" in value || "y" in value || "z" in value)
  );
}

/**
 * Extract numeric value from keyframe value (handles number and object types)
 */
export function getNumericValue(value: RuntimeValue): number {
  if (typeof value === "number") return value;
  if (isPositionLike(value)) {
    if (typeof value.x === "number") return value.x;
    if (typeof value.y === "number") return value.y;
    if (typeof value.z === "number") return value.z;
  }
  return 0;
}

/**
 * Get display value for a keyframe (for UI input fields)
 */
export function getKeyframeDisplayValue(
  selection:
    | { propId: string; index: number; keyframe: Keyframe<PropertyValue> }
    | undefined,
): number {
  if (!selection) return 0;
  const value = selection.keyframe.value;
  // Deterministic: Explicit type narrowing - check for coordinate-like objects with x property
  if (typeof value === "number") {
    return value;
  }
  if (typeof value === "object" && value !== null && "x" in value) {
    // Type proof: value has x property (coordinate-like object)
    const xValue = (value as { x: number; y: number; z?: number }).x;
    return isFiniteNumber(xValue) ? xValue : 0;
  }
  return 0;
}

// ============================================================
// HANDLE POSITION HELPERS
// ============================================================

/**
 * Get screen X coordinate for outgoing handle
 */
export function getOutHandleX(
  prop: AnimatableProperty<PropertyValue>,
  kfIndex: number,
  viewState: CurveViewState,
  canvasWidth: number,
  margin?: CurveMargin,
): number {
  const kf = prop.keyframes[kfIndex];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  if (!kf || !(kf.outHandle !== undefined && typeof kf.outHandle === "object" && "enabled" in kf.outHandle && kf.outHandle.enabled === true)) {
    return frameToScreenX(kf.frame, viewState, canvasWidth, margin);
  }
  const handleFrame = kf.frame + kf.outHandle.frame;
  return frameToScreenX(handleFrame, viewState, canvasWidth, margin);
}

/**
 * Get screen Y coordinate for outgoing handle
 */
export function getOutHandleY(
  prop: AnimatableProperty<PropertyValue>,
  kfIndex: number,
  viewState: CurveViewState,
  canvasHeight: number,
  margin?: CurveMargin,
): number {
  const kf = prop.keyframes[kfIndex];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  if (!kf || !(kf.outHandle !== undefined && typeof kf.outHandle === "object" && "enabled" in kf.outHandle && kf.outHandle.enabled === true)) {
    return valueToScreenY(
      getNumericValue(kf.value),
      viewState,
      canvasHeight,
      margin,
    );
  }
  const handleValue = getNumericValue(kf.value) + kf.outHandle.value;
  return valueToScreenY(handleValue, viewState, canvasHeight, margin);
}

/**
 * Get screen X coordinate for incoming handle
 */
export function getInHandleX(
  prop: AnimatableProperty<PropertyValue>,
  kfIndex: number,
  viewState: CurveViewState,
  canvasWidth: number,
  margin?: CurveMargin,
): number {
  const kf = prop.keyframes[kfIndex];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  if (!kf || !(kf.inHandle !== undefined && typeof kf.inHandle === "object" && "enabled" in kf.inHandle && kf.inHandle.enabled === true)) {
    return frameToScreenX(kf.frame, viewState, canvasWidth, margin);
  }
  const handleFrame = kf.frame + kf.inHandle.frame;
  return frameToScreenX(handleFrame, viewState, canvasWidth, margin);
}

/**
 * Get screen Y coordinate for incoming handle
 */
export function getInHandleY(
  prop: AnimatableProperty<PropertyValue>,
  kfIndex: number,
  viewState: CurveViewState,
  canvasHeight: number,
  margin?: CurveMargin,
): number {
  const kf = prop.keyframes[kfIndex];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  if (!kf || !(kf.inHandle !== undefined && typeof kf.inHandle === "object" && "enabled" in kf.inHandle && kf.inHandle.enabled === true)) {
    return valueToScreenY(
      getNumericValue(kf.value),
      viewState,
      canvasHeight,
      margin,
    );
  }
  const handleValue = getNumericValue(kf.value) + kf.inHandle.value;
  return valueToScreenY(handleValue, viewState, canvasHeight, margin);
}

// ============================================================
// UTILITY FUNCTIONS
// ============================================================

/**
 * Check if a keyframe is within the current view bounds
 */
export function isKeyframeInView(
  kf: Keyframe<PropertyValue>,
  viewState: CurveViewState,
): boolean {
  return kf.frame >= viewState.frameStart && kf.frame <= viewState.frameEnd;
}

/**
 * Calculate optimal grid step size for axis labels
 */
export function calculateGridStep(
  range: number,
  pixelSize: number,
  targetSpacing: number,
): number {
  const rawStep = (range * targetSpacing) / pixelSize;
  const magnitude = 10 ** Math.floor(Math.log10(rawStep));
  const normalized = rawStep / magnitude;

  if (normalized <= 1) return magnitude;
  if (normalized <= 2) return 2 * magnitude;
  if (normalized <= 5) return 5 * magnitude;
  return 10 * magnitude;
}

/**
 * Get property path from AnimatableProperty name for store operations
 */
export function getPropertyPath(prop: AnimatableProperty<PropertyValue>): string {
  const name = prop.name.toLowerCase();
  if (name === "position") return "transform.position";
  if (name === "scale") return "transform.scale";
  if (name === "rotation") return "transform.rotation";
  if (name === "opacity") return "opacity";
  if (name === "origin" || name === "anchor point")
    return "transform.anchorPoint";
  return prop.id; // Custom properties use ID
}

// ============================================================
// COMPOSABLE EXPORT
// ============================================================

export function useCurveEditorCoords() {
  return {
    // Coordinate conversion
    frameToScreenX,
    screenXToFrame,
    valueToScreenY,
    screenYToValue,

    // Keyframe positions
    getKeyframeScreenX,
    getKeyframeScreenY,
    getNumericValue,
    getKeyframeDisplayValue,

    // Handle positions
    getOutHandleX,
    getOutHandleY,
    getInHandleX,
    getInHandleY,

    // Utilities
    isKeyframeInView,
    calculateGridStep,
    getPropertyPath,
  };
}
