/**
 * Path Operations
 *
 * Operations for copying spline paths to position keyframes.
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import type { ControlPoint, Keyframe, SplineData } from "@/types/project";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import { storeLogger } from "@/utils/logger";
import { useProjectStore } from "../projectStore";
import { generateKeyframeId } from "@/utils/uuid5";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                           // copy // path // to // position
// ═══════════════════════════════════════════════════════════════════════════

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
): number {
  const projectStore = useProjectStore();
  const comp = projectStore.getActiveComp();
  if (!comp) {
    throw new Error("[LayerStore] Cannot copy path to position: No active composition found");
  }

  // Get source spline layer
  const sourceLayer = comp.layers.find((l) => l.id === sourceSplineLayerId);
  if (!sourceLayer || sourceLayer.type !== "spline" || !sourceLayer.data) {
    throw new Error(`[LayerStore] Cannot copy path to position: Source layer "${sourceSplineLayerId}" not found or is not a spline layer`);
  }

  // Get target layer
  const targetLayer = comp.layers.find((l) => l.id === targetLayerId);
  if (!targetLayer) {
    throw new Error(`[LayerStore] Cannot copy path to position: Target layer "${targetLayerId}" not found`);
  }

  const splineData = sourceLayer.data as SplineData;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
  const controlPointsRaw = splineData.controlPoints;
  const controlPoints = (controlPointsRaw !== null && controlPointsRaw !== undefined && Array.isArray(controlPointsRaw)) ? controlPointsRaw : [];

  if (controlPoints.length < 2) {
    throw new Error(`[LayerStore] Cannot copy path to position: Path needs at least 2 control points (found ${controlPoints.length})`);
  }

  // Configuration
  // Type proof: useFullDuration ∈ boolean | undefined → boolean
  const useFullDurationValue = options.useFullDuration;
  const useFullDuration = useFullDurationValue === true;
  // Type proof: startFrame ∈ ℕ ∪ {undefined} → ℕ
  const startFrameValue = options.startFrame;
  const startFrame = isFiniteNumber(startFrameValue) && Number.isInteger(startFrameValue) && startFrameValue >= 0 ? startFrameValue : 0;
  // Type proof: endFrame ∈ ℕ ∪ {undefined} → ℕ
  const endFrameValue = options.endFrame;
  const frameCountValue = comp.settings.frameCount;
  const defaultEndFrame = isFiniteNumber(frameCountValue) && Number.isInteger(frameCountValue) && frameCountValue > 0 ? frameCountValue - 1 : 0;
  const endFrame = isFiniteNumber(endFrameValue) && Number.isInteger(endFrameValue) && endFrameValue >= 0 ? endFrameValue : defaultEndFrame;
  // Type proof: interpolation ∈ "linear" | "bezier" | "hold" | undefined → "linear" | "bezier" | "hold"
  const interpolationValue = options.interpolation;
  const interpolation = interpolationValue === "linear" || interpolationValue === "bezier" || interpolationValue === "hold" ? interpolationValue : "bezier";
  // Type proof: useSpatialTangents ∈ boolean | undefined → boolean
  const useSpatialTangentsValue = options.useSpatialTangents;
  const useSpatialTangents = useSpatialTangentsValue === true;
  // Type proof: reversed ∈ boolean | undefined → boolean
  const reversedValue = options.reversed;
  const reversed = reversedValue === true;

  // Calculate frame range
  const frameStart = useFullDuration ? 0 : startFrame;
  const frameEnd = useFullDuration ? comp.settings.frameCount - 1 : endFrame;
  const frameDuration = frameEnd - frameStart;

  // Determine keyframe count based on path complexity or use specified value
  const defaultKeyframeCount = Math.max(
    controlPoints.length,
    Math.ceil(frameDuration / 5), // At least one keyframe every 5 frames
  );
  // Type proof: keyframeCount ∈ ℕ ∪ {undefined} → ℕ
  const keyframeCountValue = options.keyframeCount;
  const keyframeCount = isFiniteNumber(keyframeCountValue) && Number.isInteger(keyframeCountValue) && keyframeCountValue > 0 ? keyframeCountValue : defaultKeyframeCount;

  // Sample points along the path
  const sampledPoints = samplePathPoints(
    controlPoints,
    keyframeCount,
    (() => {
      // Type proof: closed ∈ boolean | undefined → boolean
      const closedValue = splineData.closed;
      return closedValue === true;
    })(),
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
    // Type proof: prevFrame ∈ ℕ ∪ {undefined} → ℕ
    const prevFrame = i > 0 ? (() => {
      const prevKeyframe = keyframes[i - 1];
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const prevFrameValue = (prevKeyframe != null && typeof prevKeyframe === "object" && "frame" in prevKeyframe && typeof prevKeyframe.frame === "number") ? prevKeyframe.frame : undefined;
      return isFiniteNumber(prevFrameValue) && Number.isInteger(prevFrameValue) && prevFrameValue >= 0 ? prevFrameValue : 0;
    })() : 0;
    const nextFrame =
      i < sampledPoints.length - 1
        ? Math.round(
            frameStart + ((i + 1) / (sampledPoints.length - 1)) * frameDuration,
          )
        : frameDuration;

    const inInfluence = (frame - prevFrame) * 0.33;
    const outInfluence = (nextFrame - frame) * 0.33;

    // Type proof: depth ∈ ℝ ∪ {undefined} → z ∈ ℝ
    const depthValue = point.depth;
    const z = isFiniteNumber(depthValue) ? depthValue : 0;
    const value = { x: point.x, y: point.y, z: z };
    
    // Deterministic ID generation: same layer/property/frame/value always produces same ID
    const propertyPath = "transform.position";
    const valueStr = `${value.x},${value.y},${value.z}`;
    
    const keyframe: (typeof keyframes)[0] = {
      id: generateKeyframeId(targetLayerId, propertyPath, frame, valueStr),
      frame,
      value,
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // helper // functions
// ═══════════════════════════════════════════════════════════════════════════

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
