/**
 * Curve Editor View Management
 *
 * Manages the view state (zoom, pan, fit to view) for the curve editor.
 */

import { type Ref, reactive } from "vue";
import type { AnimatableProperty, Keyframe } from "@/types/project";
import {
  type CurveMargin,
  type CurveViewState,
  DEFAULT_CURVE_MARGIN,
  getNumericValue,
  screenXToFrame,
  screenYToValue,
} from "./useCurveEditorCoords";

export interface SelectedKeyframe {
  propId: string;
  index: number;
  keyframe: Keyframe<any>;
}

// ============================================================
// VIEW STATE FACTORY
// ============================================================

/**
 * Create initial view state
 */
export function createViewState(
  frameStart = 0,
  frameEnd = 100,
  valueMin = 0,
  valueMax = 100,
): CurveViewState {
  return reactive({
    frameStart,
    frameEnd,
    valueMin,
    valueMax,
    zoom: 1,
  });
}

// ============================================================
// FIT TO VIEW
// ============================================================

/**
 * Fit view to show all visible keyframes
 */
export function fitToView(
  viewState: CurveViewState,
  visibleProperties: AnimatableProperty<any>[],
): void {
  if (visibleProperties.length === 0) return;

  let minFrame = Infinity;
  let maxFrame = -Infinity;
  let minValue = Infinity;
  let maxValue = -Infinity;

  for (const prop of visibleProperties) {
    for (const kf of prop.keyframes) {
      minFrame = Math.min(minFrame, kf.frame);
      maxFrame = Math.max(maxFrame, kf.frame);
      const value = getNumericValue(kf.value);
      minValue = Math.min(minValue, value);
      maxValue = Math.max(maxValue, value);
    }
  }

  // Add padding
  const frameMargin = (maxFrame - minFrame) * 0.1 || 10;
  const valueMargin = (maxValue - minValue) * 0.1 || 10;

  viewState.frameStart = minFrame - frameMargin;
  viewState.frameEnd = maxFrame + frameMargin;
  viewState.valueMin = minValue - valueMargin;
  viewState.valueMax = maxValue + valueMargin;
}

/**
 * Fit view to show selected keyframes
 */
export function fitSelectionToView(
  viewState: CurveViewState,
  selectedKeyframes: SelectedKeyframe[],
  visibleProperties: AnimatableProperty<any>[],
): void {
  if (selectedKeyframes.length === 0) {
    fitToView(viewState, visibleProperties);
    return;
  }

  let minFrame = Infinity;
  let maxFrame = -Infinity;
  let minValue = Infinity;
  let maxValue = -Infinity;

  for (const sk of selectedKeyframes) {
    minFrame = Math.min(minFrame, sk.keyframe.frame);
    maxFrame = Math.max(maxFrame, sk.keyframe.frame);
    const value = getNumericValue(sk.keyframe.value);
    minValue = Math.min(minValue, value);
    maxValue = Math.max(maxValue, value);
  }

  const frameMargin = (maxFrame - minFrame) * 0.1 || 10;
  const valueMargin = (maxValue - minValue) * 0.1 || 10;

  viewState.frameStart = minFrame - frameMargin;
  viewState.frameEnd = maxFrame + frameMargin;
  viewState.valueMin = minValue - valueMargin;
  viewState.valueMax = maxValue + valueMargin;
}

// ============================================================
// ZOOM
// ============================================================

/**
 * Zoom in (decrease frame/value range)
 */
export function zoomIn(viewState: CurveViewState): void {
  const centerFrame = (viewState.frameStart + viewState.frameEnd) / 2;
  const frameRange = viewState.frameEnd - viewState.frameStart;
  viewState.frameStart = centerFrame - frameRange * 0.4;
  viewState.frameEnd = centerFrame + frameRange * 0.4;
}

/**
 * Zoom out (increase frame/value range)
 */
export function zoomOut(viewState: CurveViewState): void {
  const centerFrame = (viewState.frameStart + viewState.frameEnd) / 2;
  const frameRange = viewState.frameEnd - viewState.frameStart;
  viewState.frameStart = centerFrame - frameRange * 0.6;
  viewState.frameEnd = centerFrame + frameRange * 0.6;
}

/**
 * Handle mouse wheel zoom (around cursor position)
 */
export function handleWheelZoom(
  event: WheelEvent,
  viewState: CurveViewState,
  canvasWidth: number,
  canvasHeight: number,
  canvasRect: DOMRect,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN,
): void {
  event.preventDefault();

  const x = event.clientX - canvasRect.left;
  const zoomFactor = event.deltaY > 0 ? 1.1 : 0.9;

  // Zoom around cursor position
  const frameAtCursor = screenXToFrame(x, viewState, canvasWidth, margin);

  const newFrameStart =
    frameAtCursor - (frameAtCursor - viewState.frameStart) * zoomFactor;
  const newFrameEnd =
    frameAtCursor + (viewState.frameEnd - frameAtCursor) * zoomFactor;

  if (event.shiftKey) {
    // Zoom time only
    viewState.frameStart = newFrameStart;
    viewState.frameEnd = newFrameEnd;
  } else {
    // Zoom both axes
    viewState.frameStart = newFrameStart;
    viewState.frameEnd = newFrameEnd;

    const y = event.clientY - canvasRect.top;
    const valueAtCursor = screenYToValue(y, viewState, canvasHeight, margin);
    viewState.valueMin =
      valueAtCursor - (valueAtCursor - viewState.valueMin) * zoomFactor;
    viewState.valueMax =
      valueAtCursor + (viewState.valueMax - valueAtCursor) * zoomFactor;
  }
}

// ============================================================
// PAN
// ============================================================

/**
 * Pan the view by delta amounts
 */
export function panView(
  viewState: CurveViewState,
  deltaX: number,
  deltaY: number,
  canvasWidth: number,
  canvasHeight: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN,
): void {
  const graphWidth = canvasWidth - margin.left - margin.right;
  const graphHeight = canvasHeight - margin.top - margin.bottom;

  const frameShift =
    (-deltaX / graphWidth) * (viewState.frameEnd - viewState.frameStart);
  const valueShift =
    (deltaY / graphHeight) * (viewState.valueMax - viewState.valueMin);

  viewState.frameStart += frameShift;
  viewState.frameEnd += frameShift;
  viewState.valueMin += valueShift;
  viewState.valueMax += valueShift;
}

// ============================================================
// COMPOSABLE EXPORT
// ============================================================

export function useCurveEditorView(
  canvasWidth: Ref<number>,
  canvasHeight: Ref<number>,
  visibleProperties: Ref<AnimatableProperty<any>[]>,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN,
) {
  const viewState = createViewState();

  return {
    viewState,

    fitToView: () => fitToView(viewState, visibleProperties.value),

    fitSelectionToView: (selectedKeyframes: SelectedKeyframe[]) =>
      fitSelectionToView(viewState, selectedKeyframes, visibleProperties.value),

    zoomIn: () => zoomIn(viewState),

    zoomOut: () => zoomOut(viewState),

    handleWheelZoom: (event: WheelEvent, canvasRect: DOMRect) =>
      handleWheelZoom(
        event,
        viewState,
        canvasWidth.value,
        canvasHeight.value,
        canvasRect,
        margin,
      ),

    panView: (deltaX: number, deltaY: number) =>
      panView(
        viewState,
        deltaX,
        deltaY,
        canvasWidth.value,
        canvasHeight.value,
        margin,
      ),
  };
}
