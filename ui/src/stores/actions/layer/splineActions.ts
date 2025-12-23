/**
 * Spline Actions
 *
 * Spline layer operations including control point management,
 * animation, simplification, and smoothing.
 */

import { storeLogger } from '@/utils/logger';
import type { SplineData, ControlPoint, AnimatableControlPoint, AnimatableProperty, EvaluatedControlPoint } from '@/types/project';
import { createAnimatableProperty, controlPointToAnimatable, animatableToControlPoint } from '@/types/project';
import { markLayerDirty } from '@/services/layerEvaluationCache';
import { interpolateProperty } from '@/services/interpolation';
import type { LayerStore } from '../layerActions';

// ============================================================================
// SPLINE CONTROL POINT INTERFACE
// ============================================================================

export interface SplineControlPoint {
  id: string;
  x: number;
  y: number;
  depth?: number;
  handleIn?: { x: number; y: number } | null;
  handleOut?: { x: number; y: number } | null;
  type: 'corner' | 'smooth' | 'symmetric';
}

// ============================================================================
// SPLINE CONTROL POINT OPERATIONS
// ============================================================================

/**
 * Add a control point to a spline layer
 */
export function addSplineControlPoint(store: LayerStore, layerId: string, point: SplineControlPoint): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as any;
  if (!splineData.controlPoints) {
    splineData.controlPoints = [];
  }
  splineData.controlPoints.push(point);
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Insert a control point at a specific index in a spline layer
 */
export function insertSplineControlPoint(store: LayerStore, layerId: string, point: SplineControlPoint, index: number): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as any;
  if (!splineData.controlPoints) {
    splineData.controlPoints = [];
  }
  // Clamp index to valid range
  const insertIndex = Math.max(0, Math.min(index, splineData.controlPoints.length));
  splineData.controlPoints.splice(insertIndex, 0, point);
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Update a spline control point
 */
export function updateSplineControlPoint(
  store: LayerStore,
  layerId: string,
  pointId: string,
  updates: Partial<SplineControlPoint>
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as any;
  const point = splineData.controlPoints?.find((p: any) => p.id === pointId);
  if (!point) return;

  Object.assign(point, updates);
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Delete a spline control point
 */
export function deleteSplineControlPoint(store: LayerStore, layerId: string, pointId: string): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as any;
  if (!splineData.controlPoints) return;

  const index = splineData.controlPoints.findIndex((p: any) => p.id === pointId);
  if (index >= 0) {
    splineData.controlPoints.splice(index, 1);
    store.project.meta.modified = new Date().toISOString();
  }
}

// ============================================================================
// SPLINE ANIMATION (Per-Point Keyframing)
// ============================================================================

/**
 * Enable animation mode on a spline layer
 * Converts static controlPoints to animatedControlPoints
 */
export function enableSplineAnimation(store: LayerStore, layerId: string): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;

  // Already animated?
  if (splineData.animated && splineData.animatedControlPoints) {
    storeLogger.debug('Spline already in animated mode');
    return;
  }

  // Convert static control points to animatable
  const staticPoints = splineData.controlPoints || [];
  const animatedPoints: AnimatableControlPoint[] = staticPoints.map(cp =>
    controlPointToAnimatable(cp)
  );

  // Update spline data
  splineData.animatedControlPoints = animatedPoints;
  splineData.animated = true;

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug('Enabled spline animation with', animatedPoints.length, 'control points');
}

/**
 * Add keyframe to a spline control point property at the specified frame
 * This sets the current value as a keyframe
 */
export function addSplinePointKeyframe(
  store: LayerStore,
  layerId: string,
  pointId: string,
  property: 'x' | 'y' | 'depth' | 'handleIn.x' | 'handleIn.y' | 'handleOut.x' | 'handleOut.y',
  frame: number
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;

  // Auto-enable animation if needed
  if (!splineData.animated || !splineData.animatedControlPoints) {
    enableSplineAnimation(store, layerId);
  }

  // Find the animated control point
  const point = splineData.animatedControlPoints?.find(p => p.id === pointId);
  if (!point) {
    storeLogger.warn('Control point not found:', pointId);
    return;
  }

  // Get the property to keyframe
  let animatableProp: AnimatableProperty<number> | undefined;

  switch (property) {
    case 'x':
      animatableProp = point.x;
      break;
    case 'y':
      animatableProp = point.y;
      break;
    case 'depth':
      animatableProp = point.depth;
      break;
    case 'handleIn.x':
      animatableProp = point.handleIn?.x;
      break;
    case 'handleIn.y':
      animatableProp = point.handleIn?.y;
      break;
    case 'handleOut.x':
      animatableProp = point.handleOut?.x;
      break;
    case 'handleOut.y':
      animatableProp = point.handleOut?.y;
      break;
  }

  if (!animatableProp) {
    storeLogger.warn('Property not found on control point:', property);
    return;
  }

  // Check if keyframe already exists at this frame
  const existingIdx = animatableProp.keyframes.findIndex(k => k.frame === frame);

  if (existingIdx >= 0) {
    // Update existing keyframe
    animatableProp.keyframes[existingIdx].value = animatableProp.value;
  } else {
    // Add new keyframe
    animatableProp.keyframes.push({
      id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
      frame,
      value: animatableProp.value,
      interpolation: 'bezier',
      controlMode: 'smooth',
      inHandle: { frame: -5, value: 0, enabled: true },
      outHandle: { frame: 5, value: 0, enabled: true }
    });

    // Sort keyframes by frame
    animatableProp.keyframes.sort((a, b) => a.frame - b.frame);
  }

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug('Added keyframe to control point', pointId, 'property', property, 'at frame', frame);
}

/**
 * Add keyframes to all position properties of a control point at once
 */
export function addSplinePointPositionKeyframe(
  store: LayerStore,
  layerId: string,
  pointId: string,
  frame: number
): void {
  addSplinePointKeyframe(store, layerId, pointId, 'x', frame);
  addSplinePointKeyframe(store, layerId, pointId, 'y', frame);
}

/**
 * Update a spline control point position and optionally add keyframe
 * Used when dragging control points in the editor
 */
export function updateSplinePointWithKeyframe(
  store: LayerStore,
  layerId: string,
  pointId: string,
  x: number,
  y: number,
  frame: number,
  addKeyframe: boolean = false
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;

  if (splineData.animated && splineData.animatedControlPoints) {
    // Update animated control point
    const point = splineData.animatedControlPoints.find(p => p.id === pointId);
    if (!point) return;

    point.x.value = x;
    point.y.value = y;

    if (addKeyframe) {
      addSplinePointPositionKeyframe(store, layerId, pointId, frame);
    }

    // Also update the static version for backwards compatibility
    const staticPoint = splineData.controlPoints?.find(p => p.id === pointId);
    if (staticPoint) {
      staticPoint.x = x;
      staticPoint.y = y;
    }
  } else {
    // Update static control point
    const point = splineData.controlPoints?.find(p => p.id === pointId);
    if (!point) return;

    point.x = x;
    point.y = y;
  }

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
}

/**
 * Get evaluated (interpolated) control points at a specific frame
 */
export function getEvaluatedSplinePoints(
  store: LayerStore,
  layerId: string,
  frame: number
): EvaluatedControlPoint[] {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return [];

  const splineData = layer.data as SplineData;

  // If not animated, return static points as evaluated
  if (!splineData.animated || !splineData.animatedControlPoints) {
    return (splineData.controlPoints || []).map(cp => ({
      id: cp.id,
      x: cp.x,
      y: cp.y,
      depth: cp.depth ?? 0,
      handleIn: cp.handleIn ? { ...cp.handleIn } : null,
      handleOut: cp.handleOut ? { ...cp.handleOut } : null,
      type: cp.type
    }));
  }

  // Evaluate animated control points at frame
  return splineData.animatedControlPoints.map(acp => {
    const x = interpolateProperty(acp.x, frame);
    const y = interpolateProperty(acp.y, frame);
    const depth = acp.depth ? interpolateProperty(acp.depth, frame) : 0;

    let handleIn: { x: number; y: number } | null = null;
    let handleOut: { x: number; y: number } | null = null;

    if (acp.handleIn) {
      handleIn = {
        x: interpolateProperty(acp.handleIn.x, frame),
        y: interpolateProperty(acp.handleIn.y, frame)
      };
    }

    if (acp.handleOut) {
      handleOut = {
        x: interpolateProperty(acp.handleOut.x, frame),
        y: interpolateProperty(acp.handleOut.y, frame)
      };
    }

    return {
      id: acp.id,
      x,
      y,
      depth,
      handleIn,
      handleOut,
      type: animatableToControlPoint(acp).type
    };
  });
}

/**
 * Check if a spline has animation enabled
 */
export function isSplineAnimated(store: LayerStore, layerId: string): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return false;

  const splineData = layer.data as SplineData;
  return !!splineData.animated;
}

/**
 * Check if a control point has any keyframes
 */
export function hasSplinePointKeyframes(store: LayerStore, layerId: string, pointId: string): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return false;

  const splineData = layer.data as SplineData;
  if (!splineData.animated || !splineData.animatedControlPoints) return false;

  const point = splineData.animatedControlPoints.find(p => p.id === pointId);
  if (!point) return false;

  // Check if any property has keyframes
  if (point.x.keyframes.length > 0) return true;
  if (point.y.keyframes.length > 0) return true;
  if (point.depth?.keyframes.length) return true;
  if (point.handleIn?.x.keyframes.length) return true;
  if (point.handleIn?.y.keyframes.length) return true;
  if (point.handleOut?.x.keyframes.length) return true;
  if (point.handleOut?.y.keyframes.length) return true;

  return false;
}

// ============================================================================
// SPLINE SIMPLIFICATION AND SMOOTHING
// ============================================================================

interface Point2D {
  x: number;
  y: number;
}

/**
 * Simplify a spline by reducing control points using Douglas-Peucker algorithm
 * @param tolerance - Distance threshold in pixels (higher = more simplification)
 */
export function simplifySpline(store: LayerStore, layerId: string, tolerance: number): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;
  const controlPoints = splineData.controlPoints;
  if (!controlPoints || controlPoints.length <= 2) return;

  // Convert to simple points for Douglas-Peucker
  const points: Point2D[] = controlPoints.map(cp => ({ x: cp.x, y: cp.y }));

  // Apply Douglas-Peucker simplification
  const simplified = douglasPeuckerSimplify(points, tolerance);

  // Map back to original control points (keep ones that survived simplification)
  const newControlPoints: ControlPoint[] = [];
  let simplifiedIdx = 0;

  for (const cp of controlPoints) {
    // Check if this point matches a simplified point
    if (simplifiedIdx < simplified.length) {
      const sp = simplified[simplifiedIdx];
      if (Math.abs(cp.x - sp.x) < 0.01 && Math.abs(cp.y - sp.y) < 0.01) {
        newControlPoints.push(cp);
        simplifiedIdx++;
      }
    }
  }

  // Update spline data
  splineData.controlPoints = newControlPoints;

  // Also update animated control points if present
  if (splineData.animated && splineData.animatedControlPoints) {
    const newAnimatedPoints = splineData.animatedControlPoints.filter(acp =>
      newControlPoints.some(cp => cp.id === acp.id)
    );
    splineData.animatedControlPoints = newAnimatedPoints;
  }

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug(`Simplified spline from ${controlPoints.length} to ${newControlPoints.length} points`);
}

/**
 * Douglas-Peucker line simplification algorithm
 */
function douglasPeuckerSimplify(points: Point2D[], tolerance: number): Point2D[] {
  if (points.length <= 2) return [...points];

  // Find point with maximum distance from line between first and last
  let maxDist = 0;
  let maxIndex = 0;

  const start = points[0];
  const end = points[points.length - 1];

  for (let i = 1; i < points.length - 1; i++) {
    const dist = perpendicularDist(points[i], start, end);
    if (dist > maxDist) {
      maxDist = dist;
      maxIndex = i;
    }
  }

  // If max distance exceeds tolerance, recursively simplify
  if (maxDist > tolerance) {
    const left = douglasPeuckerSimplify(points.slice(0, maxIndex + 1), tolerance);
    const right = douglasPeuckerSimplify(points.slice(maxIndex), tolerance);
    return [...left.slice(0, -1), ...right];
  } else {
    return [start, end];
  }
}

/**
 * Calculate perpendicular distance from point to line segment
 */
function perpendicularDist(point: Point2D, lineStart: Point2D, lineEnd: Point2D): number {
  const dx = lineEnd.x - lineStart.x;
  const dy = lineEnd.y - lineStart.y;
  const length = Math.sqrt(dx * dx + dy * dy);

  if (length < 0.0001) {
    return Math.sqrt((point.x - lineStart.x) ** 2 + (point.y - lineStart.y) ** 2);
  }

  // Project point onto line
  const t = ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) / (length * length);
  const closest = {
    x: lineStart.x + t * dx,
    y: lineStart.y + t * dy,
  };

  return Math.sqrt((point.x - closest.x) ** 2 + (point.y - closest.y) ** 2);
}

/**
 * Smooth spline handles to create smoother curves
 * @param amount - Smoothing amount 0-100 (100 = fully smooth bezier handles)
 */
export function smoothSplineHandles(store: LayerStore, layerId: string, amount: number): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  const splineData = layer.data as SplineData;
  const controlPoints = splineData.controlPoints;
  if (!controlPoints || controlPoints.length < 2) return;

  const factor = Math.max(0, Math.min(100, amount)) / 100;

  for (let i = 0; i < controlPoints.length; i++) {
    const cp = controlPoints[i];
    const prev = controlPoints[(i - 1 + controlPoints.length) % controlPoints.length];
    const next = controlPoints[(i + 1) % controlPoints.length];

    // Skip first/last point if path is not closed
    if (!splineData.closed && (i === 0 || i === controlPoints.length - 1)) {
      continue;
    }

    // Calculate direction vectors
    const toPrev = { x: prev.x - cp.x, y: prev.y - cp.y };
    const toNext = { x: next.x - cp.x, y: next.y - cp.y };

    // Average direction (tangent)
    const avgDir = { x: toNext.x - toPrev.x, y: toNext.y - toPrev.y };
    const avgLength = Math.sqrt(avgDir.x * avgDir.x + avgDir.y * avgDir.y);

    if (avgLength < 0.01) continue;

    // Normalize
    const normalized = { x: avgDir.x / avgLength, y: avgDir.y / avgLength };

    // Calculate ideal handle length (1/3 of distance to neighbors)
    const distPrev = Math.sqrt(toPrev.x * toPrev.x + toPrev.y * toPrev.y);
    const distNext = Math.sqrt(toNext.x * toNext.x + toNext.y * toNext.y);
    const handleLength = (distPrev + distNext) / 6;

    // Calculate ideal smooth handles
    const idealIn = { x: cp.x - normalized.x * handleLength, y: cp.y - normalized.y * handleLength };
    const idealOut = { x: cp.x + normalized.x * handleLength, y: cp.y + normalized.y * handleLength };

    // Blend current handles toward ideal
    if (cp.handleIn) {
      cp.handleIn = {
        x: cp.handleIn.x + (idealIn.x - cp.handleIn.x) * factor,
        y: cp.handleIn.y + (idealIn.y - cp.handleIn.y) * factor
      };
    } else {
      cp.handleIn = { x: idealIn.x * factor + cp.x * (1 - factor), y: idealIn.y * factor + cp.y * (1 - factor) };
    }

    if (cp.handleOut) {
      cp.handleOut = {
        x: cp.handleOut.x + (idealOut.x - cp.handleOut.x) * factor,
        y: cp.handleOut.y + (idealOut.y - cp.handleOut.y) * factor
      };
    } else {
      cp.handleOut = { x: idealOut.x * factor + cp.x * (1 - factor), y: idealOut.y * factor + cp.y * (1 - factor) };
    }

    // Set point type to smooth
    cp.type = 'smooth';
  }

  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug(`Smoothed spline handles with amount ${amount}%`);
}
