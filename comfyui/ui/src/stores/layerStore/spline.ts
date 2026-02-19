/**
 * Spline Operations
 *
 * Spline layer operations including control point management,
 * animation, simplification, and smoothing.
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import { interpolateProperty } from "@/services/interpolation";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import { generateKeyframeId } from "@/utils/uuid5";
import type {
  AnimatableControlPoint,
  AnimatableProperty,
  ControlPoint,
  EvaluatedControlPoint,
  SplineData,
} from "@/types/project";
import {
  animatableToControlPoint,
  controlPointToAnimatable,
} from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useProjectStore } from "../projectStore";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                  // spline // control // point // interface
// ═══════════════════════════════════════════════════════════════════════════

export interface SplineControlPoint {
  id: string;
  x: number;
  y: number;
  depth?: number;
  handleIn?: { x: number; y: number } | null;
  handleOut?: { x: number; y: number } | null;
  type: "corner" | "smooth" | "symmetric";
}

// ═══════════════════════════════════════════════════════════════════════════
//                                 // spline // control // point // operations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Add a control point to a spline layer
 */
export function addSplineControlPoint(
  layerId: string,
  point: SplineControlPoint,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return;

  const splineData = layer.data as SplineData;
  if (!splineData.controlPoints) {
    splineData.controlPoints = [];
  }
  splineData.controlPoints.push(point as ControlPoint);
  projectStore.project.meta.modified = new Date().toISOString();
}

/**
 * Insert a control point at a specific index in a spline layer
 */
export function insertSplineControlPoint(
  layerId: string,
  point: SplineControlPoint,
  index: number,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return;

  const splineData = layer.data as SplineData;
  if (!splineData.controlPoints) {
    splineData.controlPoints = [];
  }
  // Clamp index to valid range
  const insertIndex = Math.max(
    0,
    Math.min(index, splineData.controlPoints.length),
  );
  splineData.controlPoints.splice(insertIndex, 0, point as ControlPoint);
  projectStore.project.meta.modified = new Date().toISOString();
}

/**
 * Update a spline control point
 */
export function updateSplineControlPoint(
  layerId: string,
  pointId: string,
  updates: Partial<SplineControlPoint>,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return;

  const splineData = layer.data as SplineData;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const controlPoints = (splineData != null && typeof splineData === "object" && "controlPoints" in splineData && splineData.controlPoints != null && Array.isArray(splineData.controlPoints)) ? splineData.controlPoints : undefined;
  const point = (controlPoints != null && typeof controlPoints.find === "function") ? controlPoints.find((p) => p.id === pointId) : undefined;
  if (!point) return;

  Object.assign(point, updates);
  useProjectStore().project.meta.modified = new Date().toISOString();
}

/**
 * Delete a spline control point
 */
export function deleteSplineControlPoint(
  layerId: string,
  pointId: string,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return;

  const splineData = layer.data as SplineData;
  if (!splineData.controlPoints) return;

  const index = splineData.controlPoints.findIndex((p) => p.id === pointId);
  if (index >= 0) {
    splineData.controlPoints.splice(index, 1);
    useProjectStore().project.meta.modified = new Date().toISOString();
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// SPLINE ANIMATION (Per-Point Keyframing)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Enable animation mode on a spline layer
 * Converts static controlPoints to animatedControlPoints
 */
export function enableSplineAnimation(
  layerId: string,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return;

  const splineData = layer.data as SplineData;

  // Already animated?
  if (splineData.animated && splineData.animatedControlPoints) {
    storeLogger.debug("Spline already in animated mode");
    return;
  }

  // Convert static control points to animatable
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
  const controlPointsRaw = splineData.controlPoints;
  const staticPoints = (controlPointsRaw !== null && controlPointsRaw !== undefined && Array.isArray(controlPointsRaw)) ? controlPointsRaw : [];
  const animatedPoints: AnimatableControlPoint[] = staticPoints.map((cp) =>
    controlPointToAnimatable(cp),
  );

  // Update spline data
  splineData.animatedControlPoints = animatedPoints;
  splineData.animated = true;

  useProjectStore().project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug(
    "Enabled spline animation with",
    animatedPoints.length,
    "control points",
  );
}

/**
 * Add keyframe to a spline control point property at the specified frame
 * This sets the current value as a keyframe
 */
export function addSplinePointKeyframe(
  layerId: string,
  pointId: string,
  property:
    | "x"
    | "y"
    | "depth"
    | "handleIn.x"
    | "handleIn.y"
    | "handleOut.x"
    | "handleOut.y",
  frame: number,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return;

  const splineData = layer.data as SplineData;

  // Auto-enable animation if needed
  if (!splineData.animated || !splineData.animatedControlPoints) {
    enableSplineAnimation(layerId);
  }

  // Find the animated control point
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const animatedControlPoints = (splineData != null && typeof splineData === "object" && "animatedControlPoints" in splineData && splineData.animatedControlPoints != null && Array.isArray(splineData.animatedControlPoints)) ? splineData.animatedControlPoints : undefined;
  const point = (animatedControlPoints != null && typeof animatedControlPoints.find === "function") ? animatedControlPoints.find((p) => p.id === pointId) : undefined;
  if (!point) {
    storeLogger.warn("Control point not found:", pointId);
    return;
  }

  // Get the property to keyframe
  let animatableProp: AnimatableProperty<number> | undefined;

  switch (property) {
    case "x":
      animatableProp = point.x;
      break;
    case "y":
      animatableProp = point.y;
      break;
    case "depth":
      animatableProp = point.depth;
      break;
    case "handleIn.x":
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      animatableProp = (point != null && typeof point === "object" && "handleIn" in point && point.handleIn != null && typeof point.handleIn === "object" && "x" in point.handleIn) ? point.handleIn.x : undefined;
      break;
    case "handleIn.y":
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      animatableProp = (point != null && typeof point === "object" && "handleIn" in point && point.handleIn != null && typeof point.handleIn === "object" && "y" in point.handleIn) ? point.handleIn.y : undefined;
      break;
    case "handleOut.x":
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      animatableProp = (point != null && typeof point === "object" && "handleOut" in point && point.handleOut != null && typeof point.handleOut === "object" && "x" in point.handleOut) ? point.handleOut.x : undefined;
      break;
    case "handleOut.y":
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      animatableProp = (point != null && typeof point === "object" && "handleOut" in point && point.handleOut != null && typeof point.handleOut === "object" && "y" in point.handleOut) ? point.handleOut.y : undefined;
      break;
  }

  if (!animatableProp) {
    storeLogger.warn("Property not found on control point:", property);
    return;
  }

  // Check if keyframe already exists at this frame
  const existingIdx = animatableProp.keyframes.findIndex(
    (k) => k.frame === frame,
  );

  const propertyPath = `spline.${pointId}.${property}`;
  // Deterministic ID generation: same layer/property/frame/value always produces same ID
  // Explicit check: animatableProp.value is number (never null/undefined per type system)
  const valueStr = String(animatableProp.value);

  if (existingIdx >= 0) {
    // Update existing keyframe value and regenerate ID for determinism
    // Same layer/property/frame but different value should produce different ID
    const existingKf = animatableProp.keyframes[existingIdx];
    existingKf.value = animatableProp.value;
    existingKf.id = generateKeyframeId(layerId, propertyPath, frame, valueStr);
  } else {
    // Add new keyframe with deterministic ID
    const keyframeId = generateKeyframeId(layerId, propertyPath, frame, valueStr);
    
    animatableProp.keyframes.push({
      id: keyframeId,
      frame,
      value: animatableProp.value,
      interpolation: "bezier",
      controlMode: "smooth",
      inHandle: { frame: -5, value: 0, enabled: true },
      outHandle: { frame: 5, value: 0, enabled: true },
    });

    // Sort keyframes by frame
    animatableProp.keyframes.sort((a, b) => a.frame - b.frame);
  }

  useProjectStore().project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug(
    "Added keyframe to control point",
    pointId,
    "property",
    property,
    "at frame",
    frame,
  );
}

/**
 * Add keyframes to all position properties of a control point at once
 */
export function addSplinePointPositionKeyframe(
  layerId: string,
  pointId: string,
  frame: number,
): void {
  addSplinePointKeyframe(layerId, pointId, "x", frame);
  addSplinePointKeyframe(layerId, pointId, "y", frame);
}

/**
 * Update a spline control point position and optionally add keyframe
 * Used when dragging control points in the editor
 */
export function updateSplinePointWithKeyframe(
  layerId: string,
  pointId: string,
  x: number,
  y: number,
  frame: number,
  addKeyframe: boolean = false,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return;

  const splineData = layer.data as SplineData;

  if (splineData.animated && splineData.animatedControlPoints) {
    // Update animated control point
    const point = splineData.animatedControlPoints.find(
      (p) => p.id === pointId,
    );
    if (!point) return;

    point.x.value = x;
    point.y.value = y;

    if (addKeyframe) {
      addSplinePointPositionKeyframe(layerId, pointId, frame);
    }

    // Also update the static version for backwards compatibility
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const controlPoints = (splineData != null && typeof splineData === "object" && "controlPoints" in splineData && splineData.controlPoints != null && Array.isArray(splineData.controlPoints)) ? splineData.controlPoints : undefined;
    const staticPoint = (controlPoints != null && typeof controlPoints.find === "function") ? controlPoints.find((p) => p.id === pointId) : undefined;
    if (staticPoint) {
      staticPoint.x = x;
      staticPoint.y = y;
    }
  } else {
    // Update static control point
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const controlPoints = (splineData != null && typeof splineData === "object" && "controlPoints" in splineData && splineData.controlPoints != null && Array.isArray(splineData.controlPoints)) ? splineData.controlPoints : undefined;
    const point = (controlPoints != null && typeof controlPoints.find === "function") ? controlPoints.find((p) => p.id === pointId) : undefined;
    if (!point) return;

    point.x = x;
    point.y = y;
  }

  useProjectStore().project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
}

/**
 * Get evaluated (interpolated) control points at a specific frame
 */
export function getEvaluatedSplinePoints(
  layerId: string,
  frame: number,
): EvaluatedControlPoint[] {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return [];

  const splineData = layer.data as SplineData;

  // If not animated, return static points as evaluated
  if (!splineData.animated || !splineData.animatedControlPoints) {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
    const controlPointsRaw = splineData.controlPoints;
    const controlPoints = (controlPointsRaw !== null && controlPointsRaw !== undefined && Array.isArray(controlPointsRaw)) ? controlPointsRaw : [];
    return controlPoints.map((cp) => ({
      id: cp.id,
      x: cp.x,
      y: cp.y,
      // Type proof: depth ∈ ℝ ∪ {undefined} → ℝ
      depth: (() => {
        const depthValue = cp.depth;
        return isFiniteNumber(depthValue) ? depthValue : 0;
      })(),
      handleIn: cp.handleIn ? { ...cp.handleIn } : null,
      handleOut: cp.handleOut ? { ...cp.handleOut } : null,
      type: cp.type,
    }));
  }

  // Evaluate animated control points at frame
  return splineData.animatedControlPoints.map((acp) => {
    const x = interpolateProperty(acp.x, frame);
    const y = interpolateProperty(acp.y, frame);
    const depth = acp.depth ? interpolateProperty(acp.depth, frame) : 0;

    let handleIn: { x: number; y: number } | null = null;
    let handleOut: { x: number; y: number } | null = null;

    if (acp.handleIn) {
      handleIn = {
        x: interpolateProperty(acp.handleIn.x, frame),
        y: interpolateProperty(acp.handleIn.y, frame),
      };
    }

    if (acp.handleOut) {
      handleOut = {
        x: interpolateProperty(acp.handleOut.x, frame),
        y: interpolateProperty(acp.handleOut.y, frame),
      };
    }

    return {
      id: acp.id,
      x,
      y,
      depth,
      handleIn,
      handleOut,
      type: animatableToControlPoint(acp).type,
    };
  });
}

/**
 * Check if a spline has animation enabled
 */
export function isSplineAnimated(
  layerId: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return false;

  const splineData = layer.data as SplineData;
  return !!splineData.animated;
}

/**
 * Check if a control point has any keyframes
 */
export function hasSplinePointKeyframes(
  layerId: string,
  pointId: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return false;

  const splineData = layer.data as SplineData;
  if (!splineData.animated || !splineData.animatedControlPoints) return false;

  const point = splineData.animatedControlPoints.find((p) => p.id === pointId);
  if (!point) return false;

  // Check if any property has keyframes
  if (point.x.keyframes.length > 0) return true;
  if (point.y.keyframes.length > 0) return true;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const depth = (point != null && typeof point === "object" && "depth" in point && point.depth != null && typeof point.depth === "object" && "keyframes" in point.depth && Array.isArray(point.depth.keyframes)) ? point.depth : undefined;
  if (depth != null && depth.keyframes.length > 0) return true;
  const handleIn = (point != null && typeof point === "object" && "handleIn" in point && point.handleIn != null && typeof point.handleIn === "object") ? point.handleIn : undefined;
  const handleInX = (handleIn != null && typeof handleIn === "object" && "x" in handleIn && handleIn.x != null && typeof handleIn.x === "object" && "keyframes" in handleIn.x && Array.isArray(handleIn.x.keyframes)) ? handleIn.x : undefined;
  if (handleInX != null && handleInX.keyframes.length > 0) return true;
  const handleInY = (handleIn != null && typeof handleIn === "object" && "y" in handleIn && handleIn.y != null && typeof handleIn.y === "object" && "keyframes" in handleIn.y && Array.isArray(handleIn.y.keyframes)) ? handleIn.y : undefined;
  if (handleInY != null && handleInY.keyframes.length > 0) return true;
  const handleOut = (point != null && typeof point === "object" && "handleOut" in point && point.handleOut != null && typeof point.handleOut === "object") ? point.handleOut : undefined;
  const handleOutX = (handleOut != null && typeof handleOut === "object" && "x" in handleOut && handleOut.x != null && typeof handleOut.x === "object" && "keyframes" in handleOut.x && Array.isArray(handleOut.x.keyframes)) ? handleOut.x : undefined;
  if (handleOutX != null && handleOutX.keyframes.length > 0) return true;
  const handleOutY = (handleOut != null && typeof handleOut === "object" && "y" in handleOut && handleOut.y != null && typeof handleOut.y === "object" && "keyframes" in handleOut.y && Array.isArray(handleOut.y.keyframes)) ? handleOut.y : undefined;
  if (handleOutY != null && handleOutY.keyframes.length > 0) return true;

  return false;
}

// ═══════════════════════════════════════════════════════════════════════════
//                             // spline // simplification // and // smoothing
// ═══════════════════════════════════════════════════════════════════════════

interface Point2D {
  x: number;
  y: number;
}

/**
 * Simplify a spline by reducing control points using Douglas-Peucker algorithm
 * @param tolerance - Distance threshold in pixels (higher = more simplification)
 */
export function simplifySpline(
  layerId: string,
  tolerance: number,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return;

  const splineData = layer.data as SplineData;
  const controlPoints = splineData.controlPoints;
  if (!controlPoints || controlPoints.length <= 2) return;

  // Convert to simple points for Douglas-Peucker
  const points: Point2D[] = controlPoints.map((cp) => ({ x: cp.x, y: cp.y }));

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
    const newAnimatedPoints = splineData.animatedControlPoints.filter((acp) =>
      newControlPoints.some((cp) => cp.id === acp.id),
    );
    splineData.animatedControlPoints = newAnimatedPoints;
  }

  useProjectStore().project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug(
    `Simplified spline from ${controlPoints.length} to ${newControlPoints.length} points`,
  );
}

/**
 * Douglas-Peucker line simplification algorithm
 */
function douglasPeuckerSimplify(
  points: Point2D[],
  tolerance: number,
): Point2D[] {
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
    const left = douglasPeuckerSimplify(
      points.slice(0, maxIndex + 1),
      tolerance,
    );
    const right = douglasPeuckerSimplify(points.slice(maxIndex), tolerance);
    return [...left.slice(0, -1), ...right];
  } else {
    return [start, end];
  }
}

/**
 * Calculate perpendicular distance from point to line segment
 */
function perpendicularDist(
  point: Point2D,
  lineStart: Point2D,
  lineEnd: Point2D,
): number {
  const dx = lineEnd.x - lineStart.x;
  const dy = lineEnd.y - lineStart.y;
  const length = Math.sqrt(dx * dx + dy * dy);

  if (length < 0.0001) {
    return Math.sqrt(
      (point.x - lineStart.x) ** 2 + (point.y - lineStart.y) ** 2,
    );
  }

  // Project point onto line
  const t =
    ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) /
    (length * length);
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
export function smoothSplineHandles(
  layerId: string,
  amount: number,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "spline" || !layer.data) return;

  const splineData = layer.data as SplineData;
  const controlPoints = splineData.controlPoints;
  if (!controlPoints || controlPoints.length < 2) return;

  const factor = Math.max(0, Math.min(100, amount)) / 100;

  for (let i = 0; i < controlPoints.length; i++) {
    const cp = controlPoints[i];
    const prev =
      controlPoints[(i - 1 + controlPoints.length) % controlPoints.length];
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
    const idealIn = {
      x: cp.x - normalized.x * handleLength,
      y: cp.y - normalized.y * handleLength,
    };
    const idealOut = {
      x: cp.x + normalized.x * handleLength,
      y: cp.y + normalized.y * handleLength,
    };

    // Blend current handles toward ideal
    if (cp.handleIn) {
      cp.handleIn = {
        x: cp.handleIn.x + (idealIn.x - cp.handleIn.x) * factor,
        y: cp.handleIn.y + (idealIn.y - cp.handleIn.y) * factor,
      };
    } else {
      cp.handleIn = {
        x: idealIn.x * factor + cp.x * (1 - factor),
        y: idealIn.y * factor + cp.y * (1 - factor),
      };
    }

    if (cp.handleOut) {
      cp.handleOut = {
        x: cp.handleOut.x + (idealOut.x - cp.handleOut.x) * factor,
        y: cp.handleOut.y + (idealOut.y - cp.handleOut.y) * factor,
      };
    } else {
      cp.handleOut = {
        x: idealOut.x * factor + cp.x * (1 - factor),
        y: idealOut.y * factor + cp.y * (1 - factor),
      };
    }

    // Set point type to smooth
    cp.type = "smooth";
  }

  useProjectStore().project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);

  storeLogger.debug(`Smoothed spline handles with amount ${amount}%`);
}
