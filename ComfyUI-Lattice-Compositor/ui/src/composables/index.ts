/**
 * Composables Index
 *
 * Exports all Vue composables for the Lattice Compositor.
 */

// useAssetHandlers removed - functionality moved elsewhere
export type { SegmentBoxState } from "./useCanvasSegmentation";
export { useCanvasSegmentation } from "./useCanvasSegmentation";
export type {
  SelectableItem,
  SelectionMode,
  UseCanvasSelectionOptions,
} from "./useCanvasSelection";
export { useCanvasSelection } from "./useCanvasSelection";
export type { CurveMargin, CurveViewState } from "./useCurveEditorCoords";
// Curve Editor Composables
export {
  calculateGridStep,
  DEFAULT_CURVE_MARGIN,
  frameToScreenX,
  getInHandleX,
  getInHandleY,
  getKeyframeDisplayValue,
  getKeyframeScreenX,
  getKeyframeScreenY,
  getNumericValue,
  getOutHandleX,
  getOutHandleY,
  getPropertyPath,
  isKeyframeInView,
  screenXToFrame,
  screenYToValue,
  useCurveEditorCoords,
  valueToScreenY,
} from "./useCurveEditorCoords";
export {
  drawGrid,
  drawMainCanvas,
  drawPropertyCurve,
  drawTimeRuler,
  drawValueAxis,
  getPropertyColor,
  PROPERTY_COLORS,
  useCurveEditorDraw,
} from "./useCurveEditorDraw";
export type {
  CurveEditorInteractionOptions,
  DragTarget as CurveDragTarget,
  SelectedKeyframe as CurveSelectedKeyframe,
  SelectionBox,
} from "./useCurveEditorInteraction";
export { useCurveEditorInteraction } from "./useCurveEditorInteraction";
export type {
  CurveEditorKeyboardOptions,
  EasyEaseParams,
} from "./useCurveEditorKeyboard";
export {
  applyEasyEase,
  createKeyboardHandler,
  goToNextKeyframe,
  goToPreviousKeyframe,
  useCurveEditorKeyboard,
} from "./useCurveEditorKeyboard";
export type { SelectedKeyframe } from "./useCurveEditorView";
export {
  createViewState,
  fitSelectionToView,
  fitToView,
  handleWheelZoom,
  panView,
  useCurveEditorView,
  zoomIn,
  zoomOut,
} from "./useCurveEditorView";
export { useGuides } from "./useGuides";
export { useKeyboardShortcuts } from "./useKeyboardShortcuts";
export type { MenuActionsOptions } from "./useMenuActions";
export { useMenuActions } from "./useMenuActions";
export type { ShapeDrawBounds, ShapeDrawState } from "./useShapeDrawing";
export { useShapeDrawing } from "./useShapeDrawing";
export type {
  DragTarget,
  PenSubMode,
  SplineInteractionOptions,
} from "./useSplineInteraction";
export { useSplineInteraction } from "./useSplineInteraction";
export type { LayerTransformValues } from "./useSplineUtils";
export {
  bezierArcLength,
  calculateSmoothHandles,
  evaluateBezier,
  evaluateBezierTangent,
  findClosestPointOnPath,
  findPointAtPosition,
  generateCurvePreview,
  generateSplinePath,
  simplifyPath,
  transformPointToComp,
  transformPointToLayer,
  useSplineUtils,
} from "./useSplineUtils";
export type {
  ViewportControlsOptions,
  ViewportControlsReturn,
} from "./useViewportControls";
export { useViewportControls } from "./useViewportControls";
export type {
  ResolutionGuide,
  SafeFrameBounds,
  UseViewportGuidesOptions,
} from "./useViewportGuides";
export { useViewportGuides } from "./useViewportGuides";
