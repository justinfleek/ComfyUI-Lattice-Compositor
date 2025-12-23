/**
 * Curve Editor Drawing Utilities
 *
 * Canvas drawing functions for the curve editor (graph editor).
 * Handles grid, curves, time ruler, and value axis rendering.
 */

import type { AnimatableProperty } from '@/types/project';
import {
  type CurveViewState,
  type CurveMargin,
  DEFAULT_CURVE_MARGIN,
  frameToScreenX,
  valueToScreenY,
  getNumericValue,
  calculateGridStep
} from './useCurveEditorCoords';

// ============================================================
// PROPERTY COLORS
// ============================================================

export const PROPERTY_COLORS: Record<string, string> = {
  'Position': '#ff6b6b',
  'Position.x': '#ff6b6b',
  'Position.y': '#4ecdc4',
  'Position.z': '#45b7d1',
  'Scale': '#f7dc6f',
  'Scale.x': '#f7dc6f',
  'Scale.y': '#82e0aa',
  'Scale.z': '#85c1e9',
  'Rotation': '#bb8fce',
  'Opacity': '#f8b739',
  'default': '#7c9cff'
};

/**
 * Get color for a property
 */
export function getPropertyColor(propName: string): string {
  return PROPERTY_COLORS[propName] ?? PROPERTY_COLORS.default;
}

// ============================================================
// GRID DRAWING
// ============================================================

/**
 * Draw grid lines on the canvas
 */
export function drawGrid(
  ctx: CanvasRenderingContext2D,
  viewState: CurveViewState,
  canvasWidth: number,
  canvasHeight: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN
): void {
  const graphWidth = canvasWidth - margin.left - margin.right;
  const graphHeight = canvasHeight - margin.top - margin.bottom;

  ctx.strokeStyle = '#2a2a2a';
  ctx.lineWidth = 1;

  // Calculate grid spacing based on view
  const frameRange = viewState.frameEnd - viewState.frameStart;
  const frameStep = calculateGridStep(frameRange, graphWidth, 50);
  const valueRange = viewState.valueMax - viewState.valueMin;
  const valueStep = calculateGridStep(valueRange, graphHeight, 30);

  // Vertical lines (frame grid)
  const firstFrame = Math.ceil(viewState.frameStart / frameStep) * frameStep;
  for (let frame = firstFrame; frame <= viewState.frameEnd; frame += frameStep) {
    const x = frameToScreenX(frame, viewState, canvasWidth, margin);
    ctx.beginPath();
    ctx.moveTo(x, margin.top);
    ctx.lineTo(x, canvasHeight - margin.bottom);
    ctx.stroke();
  }

  // Horizontal lines (value grid)
  const firstValue = Math.ceil(viewState.valueMin / valueStep) * valueStep;
  for (let value = firstValue; value <= viewState.valueMax; value += valueStep) {
    const y = valueToScreenY(value, viewState, canvasHeight, margin);
    ctx.beginPath();
    ctx.moveTo(margin.left, y);
    ctx.lineTo(canvasWidth - margin.right, y);
    ctx.stroke();
  }

  // Zero lines (stronger)
  ctx.strokeStyle = '#3a3a3a';
  ctx.lineWidth = 1;

  if (viewState.frameStart <= 0 && viewState.frameEnd >= 0) {
    const x = frameToScreenX(0, viewState, canvasWidth, margin);
    ctx.beginPath();
    ctx.moveTo(x, margin.top);
    ctx.lineTo(x, canvasHeight - margin.bottom);
    ctx.stroke();
  }

  if (viewState.valueMin <= 0 && viewState.valueMax >= 0) {
    const y = valueToScreenY(0, viewState, canvasHeight, margin);
    ctx.beginPath();
    ctx.moveTo(margin.left, y);
    ctx.lineTo(canvasWidth - margin.right, y);
    ctx.stroke();
  }
}

// ============================================================
// CURVE DRAWING
// ============================================================

/**
 * Draw a property's animation curve
 */
export function drawPropertyCurve(
  ctx: CanvasRenderingContext2D,
  prop: AnimatableProperty<any>,
  viewState: CurveViewState,
  canvasWidth: number,
  canvasHeight: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN
): void {
  if (prop.keyframes.length < 2) return;

  const color = getPropertyColor(prop.name);

  // Two-pass rendering: black outline then colored fill
  for (let pass = 0; pass < 2; pass++) {
    if (pass === 0) {
      ctx.strokeStyle = '#000';
      ctx.lineWidth = 4;
    } else {
      ctx.strokeStyle = color;
      ctx.lineWidth = 2;
    }

    ctx.beginPath();
    let started = false;

    for (let i = 0; i < prop.keyframes.length - 1; i++) {
      const kf1 = prop.keyframes[i];
      const kf2 = prop.keyframes[i + 1];

      // Skip segments outside view
      if (kf2.frame < viewState.frameStart || kf1.frame > viewState.frameEnd) continue;

      const x1 = frameToScreenX(kf1.frame, viewState, canvasWidth, margin);
      const y1 = valueToScreenY(getNumericValue(kf1.value), viewState, canvasHeight, margin);
      const x2 = frameToScreenX(kf2.frame, viewState, canvasWidth, margin);
      const y2 = valueToScreenY(getNumericValue(kf2.value), viewState, canvasHeight, margin);

      if (!started) {
        ctx.moveTo(x1, y1);
        started = true;
      }

      if (kf1.interpolation === 'hold') {
        // Step function
        ctx.lineTo(x2, y1);
        ctx.lineTo(x2, y2);
      } else if (kf1.interpolation === 'linear' || (!kf1.outHandle?.enabled && !kf2.inHandle?.enabled)) {
        // Straight line
        ctx.lineTo(x2, y2);
      } else {
        // Bezier curve using absolute handle offsets
        const cp1x = frameToScreenX(kf1.frame + (kf1.outHandle?.frame ?? 0), viewState, canvasWidth, margin);
        const cp1y = valueToScreenY(getNumericValue(kf1.value) + (kf1.outHandle?.value ?? 0), viewState, canvasHeight, margin);
        const cp2x = frameToScreenX(kf2.frame + (kf2.inHandle?.frame ?? 0), viewState, canvasWidth, margin);
        const cp2y = valueToScreenY(getNumericValue(kf2.value) + (kf2.inHandle?.value ?? 0), viewState, canvasHeight, margin);

        ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, x2, y2);
      }
    }

    ctx.stroke();
  }
}

// ============================================================
// TIME RULER DRAWING
// ============================================================

/**
 * Draw the time ruler
 */
export function drawTimeRuler(
  ctx: CanvasRenderingContext2D,
  viewState: CurveViewState,
  canvasWidth: number,
  currentFrame: number
): void {
  const canvasHeight = 24;

  ctx.fillStyle = '#252525';
  ctx.fillRect(0, 0, canvasWidth, canvasHeight);

  const frameRange = viewState.frameEnd - viewState.frameStart;
  const frameStep = calculateGridStep(frameRange, canvasWidth, 60);

  ctx.fillStyle = '#888';
  ctx.font = '10px system-ui';
  ctx.textAlign = 'center';

  const firstFrame = Math.ceil(viewState.frameStart / frameStep) * frameStep;
  for (let frame = firstFrame; frame <= viewState.frameEnd; frame += frameStep) {
    const x = frameToScreenX(frame, viewState, canvasWidth);
    ctx.fillText(frame.toString(), x, 16);

    ctx.strokeStyle = '#444';
    ctx.beginPath();
    ctx.moveTo(x, 20);
    ctx.lineTo(x, 24);
    ctx.stroke();
  }

  // Current frame marker
  const ctfX = frameToScreenX(currentFrame, viewState, canvasWidth);
  ctx.fillStyle = '#ff4444';
  ctx.beginPath();
  ctx.moveTo(ctfX - 5, 0);
  ctx.lineTo(ctfX + 5, 0);
  ctx.lineTo(ctfX, 8);
  ctx.closePath();
  ctx.fill();
}

// ============================================================
// VALUE AXIS DRAWING
// ============================================================

/**
 * Draw the value axis
 */
export function drawValueAxis(
  ctx: CanvasRenderingContext2D,
  viewState: CurveViewState,
  canvasHeight: number
): void {
  const canvasWidth = 40;

  ctx.fillStyle = '#252525';
  ctx.fillRect(0, 0, canvasWidth, canvasHeight);

  const valueRange = viewState.valueMax - viewState.valueMin;
  const valueStep = calculateGridStep(valueRange, canvasHeight, 30);

  ctx.fillStyle = '#888';
  ctx.font = '10px system-ui';
  ctx.textAlign = 'right';

  const firstValue = Math.ceil(viewState.valueMin / valueStep) * valueStep;
  for (let value = firstValue; value <= viewState.valueMax; value += valueStep) {
    const y = valueToScreenY(value, viewState, canvasHeight);
    ctx.fillText(value.toFixed(0), 36, y + 4);
  }
}

// ============================================================
// MAIN CANVAS DRAWING
// ============================================================

/**
 * Draw the complete main canvas
 */
export function drawMainCanvas(
  ctx: CanvasRenderingContext2D,
  viewState: CurveViewState,
  visibleProperties: AnimatableProperty<any>[],
  canvasWidth: number,
  canvasHeight: number,
  margin: CurveMargin = DEFAULT_CURVE_MARGIN
): void {
  // Clear
  ctx.fillStyle = '#1a1a1a';
  ctx.fillRect(0, 0, canvasWidth, canvasHeight);

  // Draw grid
  drawGrid(ctx, viewState, canvasWidth, canvasHeight, margin);

  // Draw curves for each visible property
  for (const prop of visibleProperties) {
    drawPropertyCurve(ctx, prop, viewState, canvasWidth, canvasHeight, margin);
  }
}

// ============================================================
// COMPOSABLE EXPORT
// ============================================================

export function useCurveEditorDraw() {
  return {
    PROPERTY_COLORS,
    getPropertyColor,
    drawGrid,
    drawPropertyCurve,
    drawTimeRuler,
    drawValueAxis,
    drawMainCanvas
  };
}
