/**
 * Composables Index
 *
 * Exports all Vue composables for the Weyl Compositor.
 */

export { useCanvasSelection } from './useCanvasSelection';
export type { SelectableItem, SelectionMode, CanvasSelectionOptions } from './useCanvasSelection';

export { useCanvasSegmentation } from './useCanvasSegmentation';
export type { SegmentBoxState } from './useCanvasSegmentation';

export { useGuides } from './useGuides';

export { useKeyboardShortcuts } from './useKeyboardShortcuts';

export { useShapeDrawing } from './useShapeDrawing';
export type { ShapeDrawBounds, ShapeDrawState } from './useShapeDrawing';

export { useViewportGuides } from './useViewportGuides';
export type { SafeFrameBounds, ResolutionGuide, UseViewportGuidesOptions } from './useViewportGuides';

export { useSplineUtils } from './useSplineUtils';
export type { LayerTransformValues } from './useSplineUtils';
export {
  evaluateBezier,
  evaluateBezierTangent,
  bezierArcLength,
  findClosestPointOnPath,
  findPointAtPosition,
  generateSplinePath,
  generateCurvePreview,
  transformPointToComp,
  transformPointToLayer,
  calculateSmoothHandles,
  simplifyPath
} from './useSplineUtils';

// Curve Editor Composables
export { useCurveEditorCoords } from './useCurveEditorCoords';
export type { CurveViewState, CurveMargin } from './useCurveEditorCoords';
export {
  DEFAULT_CURVE_MARGIN,
  frameToScreenX,
  screenXToFrame,
  valueToScreenY,
  screenYToValue,
  getKeyframeScreenX,
  getKeyframeScreenY,
  getNumericValue,
  getKeyframeDisplayValue,
  getOutHandleX,
  getOutHandleY,
  getInHandleX,
  getInHandleY,
  isKeyframeInView,
  calculateGridStep,
  getPropertyPath
} from './useCurveEditorCoords';

export { useCurveEditorView, createViewState, fitToView, fitSelectionToView, zoomIn, zoomOut, handleWheelZoom, panView } from './useCurveEditorView';
export type { SelectedKeyframe } from './useCurveEditorView';

export { useCurveEditorDraw, PROPERTY_COLORS, getPropertyColor, drawGrid, drawPropertyCurve, drawTimeRuler, drawValueAxis, drawMainCanvas } from './useCurveEditorDraw';

export { useCurveEditorKeyboard, createKeyboardHandler, goToPreviousKeyframe, goToNextKeyframe, applyEasyEase } from './useCurveEditorKeyboard';
export type { EasyEaseParams, CurveEditorKeyboardOptions } from './useCurveEditorKeyboard';
