/**
 * Path Operations
 *
 * Operations for copying spline paths to position keyframes.
 */

import type { ControlPoint, Keyframe, SplineData } from "@/types/project";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import { storeLogger } from "@/utils/logger";
import { useProjectStore } from "../projectStore";

// ============================================================================
// COPY PATH TO POSITION
// ============================================================================

export interface CopyPathToPositionOptions {
  /** Use the full composition duration for the motion (default: true) */
  useFullDuration?: boolean;
  /** Start frame for keyframes (if not using full duration) */
  startFrame?: number;
  /** End frame for keyframes (if not using full duration) */
  endFrame?: number;
  /** Number of keyframes to create (default: auto based on path complexity) */
  keyframeCount?: number;
  /** Interpolation type for keyframes (default: 'bezier') */
  interpolation?: "linear" | "bezier" | "hold";
  /** Apply spatial tangents from path handles (default: true) */
  useSpatialTangents?: boolean;
  /** Reverse the path direction (default: false) */
  reversed?: boolean;
}

/**
 * Copy a path from a spline layer and paste it as position keyframes on a target layer.
 * This creates a motion path where the layer follows the spline's shape over time.
 *
 * @param sourceSplineLayerId - The spline layer to copy the path from
 * @param targetLayerId - The layer to apply position keyframes to
 * @param options - Configuration options
 * @returns Number of keyframes created, or null if failed
 */
export function copyPathToPosition(
  sourceSplineLayerId: string,
  targetLayerId: string,
  options: CopyPathToPositionOptions = {},
): number | null {
  const projectStore = useProjectStore();
  const comp = projectStore.getActiveComp();
  if (!comp) {
    storeLogger.error("copyPathToPosition: No active composition");
    return null;
  }

  // Get source spline layer
  const sourceLayer = comp.layers.find((l) => l.id === sourceSplineLayerId);
  if (!sourceLayer || sourceLayer.type !== "spline" || !sourceLayer.data) {
    storeLogger.error(
      "copyPathToPosition: Source layer not found or not a spline",
    );
    return null;
  }

  // Get target layer
  const targetLayer = comp.layers.find((l) => l.id === targetLayerId);
  if (!targetLayer) {
    storeLogger.error("copyPathToPosition: Target layer not found");
    return null;
  }

  const splineData = sourceLayer.data as SplineData;
  const controlPoints = splineData.controlPoints || [];

  if (controlPoints.length < 2) {
    storeLogger.error(
      "copyPathToPosition: Path needs at least 2 control points",
    );
    return null;
  }

  // Configuration
  const useFullDuration = options.useFullDuration ?? true;
  const startFrame = options.startFrame ?? 0;
  const endFrame = options.endFrame ?? comp.settings.frameCount - 1;
  const interpolation = options.interpolation ?? "bezier";
  const useSpatialTangents = options.useSpatialTangents ?? true;
  const reversed = options.reversed ?? false;

  // Calculate frame range
  const frameStart = useFullDuration ? 0 : startFrame;
  const frameEnd = useFullDuration ? comp.settings.frameCount - 1 : endFrame;
  const frameDuration = frameEnd - frameStart;

  // Determine keyframe count based on path complexity or use specified value
  const defaultKeyframeCount = Math.max(
    controlPoints.length,
    Math.ceil(frameDuration / 5), // At least one keyframe every 5 frames
  );
  const keyframeCount = options.keyframeCount ?? defaultKeyframeCount;

  // Sample points along the path
  const sampledPoints = samplePathPoints(
    controlPoints,
    keyframeCount,
    splineData.closed ?? false,
  );
  if (reversed) {
    sampledPoints.reverse();
  }

  // Create keyframes with proper BezierHandle structure
  const keyframes: Array<{
    id: string;
    frame: number;
    value: { x: number; y: number; z: number };
    interpolation: "linear" | "bezier" | "hold";
    inHandle: { frame: number; value: number; enabled: boolean };
    outHandle: { frame: number; value: number; enabled: boolean };
    controlMode: "symmetric" | "smooth" | "corner";
    spatialInTangent?: { x: number; y: number; z: number };
    spatialOutTangent?: { x: number; y: number; z: number };
  }> = [];

  for (let i = 0; i < sampledPoints.length; i++) {
    const t = sampledPoints.length > 1 ? i / (sampledPoints.length - 1) : 0;
    const frame = Math.round(frameStart + t * frameDuration);
    const point = sampledPoints[i];

    // Calculate frame distance to neighboring keyframes for handle influence
    const prevFrame = i > 0 ? (keyframes[i - 1]?.frame ?? 0) : 0;
    const nextFrame =
      i < sampledPoints.length - 1
        ? Math.round(
            frameStart + ((i + 1) / (sampledPoints.length - 1)) * frameDuration,
          )
        : frameDuration;

    const inInfluence = (frame - prevFrame) * 0.33;
    const outInfluence = (nextFrame - frame) * 0.33;

    const keyframe: (typeof keyframes)[0] = {
      id: `kf_${Date.now()}_${i}`,
      frame,
      value: { x: point.x, y: point.y, z: point.depth ?? 0 },
      interpolation,
      inHandle: { frame: -inInfluence, value: 0, enabled: true },
      outHandle: { frame: outInfluence, value: 0, enabled: true },
      controlMode: "smooth",
    };

    // Apply spatial tangents from path handles if available
    if (useSpatialTangents && point.handleIn && point.handleOut) {
      keyframe.spatialInTangent = {
        x: point.handleIn.x - point.x,
        y: point.handleIn.y - point.y,
        z: 0,
      };
      keyframe.spatialOutTangent = {
        x: point.handleOut.x - point.x,
        y: point.handleOut.y - point.y,
        z: 0,
      };
    }

    keyframes.push(keyframe);
  }

  // Apply keyframes to target layer's position
  projectStore.pushHistory();

  targetLayer.transform.position.animated = true;
  // Type assertion needed: our keyframes match Keyframe<{x,y,z}> structure
  targetLayer.transform.position.keyframes = keyframes as Keyframe<{
    x: number;
    y: number;
    z: number;
  }>[];

  // Mark layer dirty for re-evaluation
  markLayerDirty(targetLayerId);
  projectStore.project.meta.modified = new Date().toISOString();

  storeLogger.info(
    `copyPathToPosition: Created ${keyframes.length} position keyframes on layer "${targetLayer.name}"`,
  );
  return keyframes.length;
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

interface SampledPoint {
  x: number;
  y: number;
  depth?: number;
  handleIn?: { x: number; y: number };
  handleOut?: { x: number; y: number };
}

/**
 * Sample points along a path at regular intervals.
 * Uses arc-length parameterization for even spacing.
 */
function samplePathPoints(
  controlPoints: ControlPoint[],
  count: number,
  closed: boolean,
): SampledPoint[] {
  if (controlPoints.length === 0) return [];
  if (controlPoints.length === 1) {
    return [
      {
        x: controlPoints[0].x,
        y: controlPoints[0].y,
        depth: controlPoints[0].depth,
      },
    ];
  }

  // Build path segments
  const segments: Array<{
    p0: { x: number; y: number; depth?: number };
    p1: { x: number; y: number };
    p2: { x: number; y: number };
    p3: { x: number; y: number; depth?: number };
    length: number;
  }> = [];

  let totalLength = 0;

  for (let i = 0; i < controlPoints.length - 1; i++) {
    const curr = controlPoints[i];
    const next = controlPoints[i + 1];

    // Get bezier control points
    const p0 = { x: curr.x, y: curr.y, depth: curr.depth };
    const p3 = { x: next.x, y: next.y, depth: next.depth };

    // Control points (handle out from curr, handle in to next)
    const p1 = curr.handleOut
      ? { x: curr.handleOut.x, y: curr.handleOut.y }
      : { x: curr.x, y: curr.y };
    const p2 = next.handleIn
      ? { x: next.handleIn.x, y: next.handleIn.y }
      : { x: next.x, y: next.y };

    // Approximate segment length
    const length = approximateBezierLength(p0, p1, p2, p3);
    totalLength += length;

    segments.push({ p0, p1, p2, p3, length });
  }

  // Handle closed path
  if (closed && controlPoints.length > 2) {
    const last = controlPoints[controlPoints.length - 1];
    const first = controlPoints[0];

    const p0 = { x: last.x, y: last.y, depth: last.depth };
    const p3 = { x: first.x, y: first.y, depth: first.depth };
    const p1 = last.handleOut
      ? { x: last.handleOut.x, y: last.handleOut.y }
      : { x: last.x, y: last.y };
    const p2 = first.handleIn
      ? { x: first.handleIn.x, y: first.handleIn.y }
      : { x: first.x, y: first.y };

    const length = approximateBezierLength(p0, p1, p2, p3);
    totalLength += length;
    segments.push({ p0, p1, p2, p3, length });
  }

  // Sample along path
  const result: SampledPoint[] = [];

  // Guard against division by zero (count must be at least 2)
  if (count < 2) {
    const cp = controlPoints[0];
    return [{ x: cp.x, y: cp.y, depth: cp.depth }];
  }

  const step = totalLength / (count - 1);

  let currentDist = 0;
  let segIndex = 0;
  let segDist = 0;

  for (let i = 0; i < count; i++) {
    const targetDist = i * step;

    // Find the segment containing this distance
    while (
      segIndex < segments.length - 1 &&
      currentDist + segments[segIndex].length < targetDist
    ) {
      currentDist += segments[segIndex].length;
      segIndex++;
    }

    const seg = segments[segIndex];
    if (!seg) {
      // Past the end, use last point
      const lastCp = controlPoints[controlPoints.length - 1];
      result.push({ x: lastCp.x, y: lastCp.y, depth: lastCp.depth });
      continue;
    }

    // Calculate t within this segment
    segDist = targetDist - currentDist;
    const t = seg.length > 0 ? Math.min(1, segDist / seg.length) : 0;

    // Evaluate cubic bezier
    const point = evaluateCubicBezier(seg.p0, seg.p1, seg.p2, seg.p3, t);

    // Interpolate depth
    const depth =
      seg.p0.depth !== undefined && seg.p3.depth !== undefined
        ? seg.p0.depth + (seg.p3.depth - seg.p0.depth) * t
        : undefined;

    // Calculate tangent for handles
    const tangent = evaluateCubicBezierDerivative(
      seg.p0,
      seg.p1,
      seg.p2,
      seg.p3,
      t,
    );
    const handleScale = 20; // Scale factor for handle length

    result.push({
      x: point.x,
      y: point.y,
      depth,
      handleIn: {
        x: point.x - tangent.x * handleScale,
        y: point.y - tangent.y * handleScale,
      },
      handleOut: {
        x: point.x + tangent.x * handleScale,
        y: point.y + tangent.y * handleScale,
      },
    });
  }

  return result;
}

/**
 * Approximate the length of a cubic bezier curve using chord length approximation
 */
function approximateBezierLength(
  p0: { x: number; y: number },
  p1: { x: number; y: number },
  p2: { x: number; y: number },
  p3: { x: number; y: number },
  samples: number = 10,
): number {
  let length = 0;
  let prev = p0;

  for (let i = 1; i <= samples; i++) {
    const t = i / samples;
    const curr = evaluateCubicBezier(p0, p1, p2, p3, t);
    length += Math.sqrt((curr.x - prev.x) ** 2 + (curr.y - prev.y) ** 2);
    prev = curr;
  }

  return length;
}

/**
 * Evaluate a cubic bezier curve at parameter t
 */
function evaluateCubicBezier(
  p0: { x: number; y: number },
  p1: { x: number; y: number },
  p2: { x: number; y: number },
  p3: { x: number; y: number },
  t: number,
): { x: number; y: number } {
  const t2 = t * t;
  const t3 = t2 * t;
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;

  return {
    x: mt3 * p0.x + 3 * mt2 * t * p1.x + 3 * mt * t2 * p2.x + t3 * p3.x,
    y: mt3 * p0.y + 3 * mt2 * t * p1.y + 3 * mt * t2 * p2.y + t3 * p3.y,
  };
}

/**
 * Evaluate the derivative (tangent) of a cubic bezier curve at parameter t
 */
function evaluateCubicBezierDerivative(
  p0: { x: number; y: number },
  p1: { x: number; y: number },
  p2: { x: number; y: number },
  p3: { x: number; y: number },
  t: number,
): { x: number; y: number } {
  const t2 = t * t;
  const mt = 1 - t;
  const mt2 = mt * mt;

  const dx =
    3 * mt2 * (p1.x - p0.x) +
    6 * mt * t * (p2.x - p1.x) +
    3 * t2 * (p3.x - p2.x);
  const dy =
    3 * mt2 * (p1.y - p0.y) +
    6 * mt * t * (p2.y - p1.y) +
    3 * t2 * (p3.y - p2.y);

  // Normalize
  const len = Math.sqrt(dx * dx + dy * dy);
  if (len === 0) return { x: 0, y: 0 };

  return { x: dx / len, y: dy / len };
}
