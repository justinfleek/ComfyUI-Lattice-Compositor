/**
 * Curve Editor Coordinate Utilities
 *
 * Provides coordinate conversion functions for the curve editor (graph editor).
 * Handles transformation between frame/value space and screen pixel space.
 */

import type { Keyframe, AnimatableProperty } from '@/types/project';

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
  left: 10
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
  margin: CurveMargin = DEFAULT_CURVE_MARGIN
): number {
  const graphWidth = canvasWidth - margin.left - margin.right;
  const t = (frame - viewState.frameStart) / (viewState.frameEnd - viewState.frameStart);
  return margin.left + t * graphWidth;
}

/**
 * Convert screen X coordinate to frame number
 */
export function screenXToFrame(
  screenX: number,
  viewState: CurveViewState,
  canvasWidth: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN
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
  margin: CurveMargin = DEFAULT_CURVE_MARGIN
): number {
  const graphHeight = canvasHeight - margin.top - margin.bottom;
  const t = (value - viewState.valueMin) / (viewState.valueMax - viewState.valueMin);
  return canvasHeight - margin.bottom - t * graphHeight;
}

/**
 * Convert screen Y coordinate to value
 */
export function screenYToValue(
  screenY: number,
  viewState: CurveViewState,
  canvasHeight: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN
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
  kf: Keyframe<any>,
  viewState: CurveViewState,
  canvasWidth: number,
  margin?: CurveMargin
): number {
  return frameToScreenX(kf.frame, viewState, canvasWidth, margin);
}

/**
 * Get screen Y coordinate for a keyframe
 */
export function getKeyframeScreenY(
  prop: AnimatableProperty<any>,
  kf: Keyframe<any>,
  viewState: CurveViewState,
  canvasHeight: number,
  margin?: CurveMargin
): number {
  const value = getNumericValue(kf.value);
  return valueToScreenY(value, viewState, canvasHeight, margin);
}

/**
 * Extract numeric value from keyframe value (handles number and object types)
 */
export function getNumericValue(value: any): number {
  if (typeof value === 'number') return value;
  if (typeof value === 'object') return value.x ?? value.y ?? value.z ?? 0;
  return 0;
}

/**
 * Get display value for a keyframe (for UI input fields)
 */
export function getKeyframeDisplayValue(
  selection: { propId: string; index: number; keyframe: Keyframe<any> } | undefined
): number {
  if (!selection) return 0;
  const value = selection.keyframe.value;
  return typeof value === 'number' ? value :
    typeof value === 'object' ? (value.x ?? 0) : 0;
}

// ============================================================
// HANDLE POSITION HELPERS
// ============================================================

/**
 * Get screen X coordinate for outgoing handle
 */
export function getOutHandleX(
  prop: AnimatableProperty<any>,
  kfIndex: number,
  viewState: CurveViewState,
  canvasWidth: number,
  margin?: CurveMargin
): number {
  const kf = prop.keyframes[kfIndex];
  if (!kf || !kf.outHandle?.enabled) {
    return frameToScreenX(kf.frame, viewState, canvasWidth, margin);
  }
  const handleFrame = kf.frame + kf.outHandle.frame;
  return frameToScreenX(handleFrame, viewState, canvasWidth, margin);
}

/**
 * Get screen Y coordinate for outgoing handle
 */
export function getOutHandleY(
  prop: AnimatableProperty<any>,
  kfIndex: number,
  viewState: CurveViewState,
  canvasHeight: number,
  margin?: CurveMargin
): number {
  const kf = prop.keyframes[kfIndex];
  if (!kf || !kf.outHandle?.enabled) {
    return valueToScreenY(getNumericValue(kf.value), viewState, canvasHeight, margin);
  }
  const handleValue = getNumericValue(kf.value) + kf.outHandle.value;
  return valueToScreenY(handleValue, viewState, canvasHeight, margin);
}

/**
 * Get screen X coordinate for incoming handle
 */
export function getInHandleX(
  prop: AnimatableProperty<any>,
  kfIndex: number,
  viewState: CurveViewState,
  canvasWidth: number,
  margin?: CurveMargin
): number {
  const kf = prop.keyframes[kfIndex];
  if (!kf || !kf.inHandle?.enabled) {
    return frameToScreenX(kf.frame, viewState, canvasWidth, margin);
  }
  const handleFrame = kf.frame + kf.inHandle.frame;
  return frameToScreenX(handleFrame, viewState, canvasWidth, margin);
}

/**
 * Get screen Y coordinate for incoming handle
 */
export function getInHandleY(
  prop: AnimatableProperty<any>,
  kfIndex: number,
  viewState: CurveViewState,
  canvasHeight: number,
  margin?: CurveMargin
): number {
  const kf = prop.keyframes[kfIndex];
  if (!kf || !kf.inHandle?.enabled) {
    return valueToScreenY(getNumericValue(kf.value), viewState, canvasHeight, margin);
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
  kf: Keyframe<any>,
  viewState: CurveViewState
): boolean {
  return kf.frame >= viewState.frameStart && kf.frame <= viewState.frameEnd;
}

/**
 * Calculate optimal grid step size for axis labels
 */
export function calculateGridStep(
  range: number,
  pixelSize: number,
  targetSpacing: number
): number {
  const rawStep = range * targetSpacing / pixelSize;
  const magnitude = Math.pow(10, Math.floor(Math.log10(rawStep)));
  const normalized = rawStep / magnitude;

  if (normalized <= 1) return magnitude;
  if (normalized <= 2) return 2 * magnitude;
  if (normalized <= 5) return 5 * magnitude;
  return 10 * magnitude;
}

/**
 * Get property path from AnimatableProperty name for store operations
 */
export function getPropertyPath(prop: AnimatableProperty<any>): string {
  const name = prop.name.toLowerCase();
  if (name === 'position') return 'transform.position';
  if (name === 'scale') return 'transform.scale';
  if (name === 'rotation') return 'transform.rotation';
  if (name === 'opacity') return 'opacity';
  if (name === 'origin' || name === 'anchor point') return 'transform.anchorPoint';
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
    getPropertyPath
  };
}
