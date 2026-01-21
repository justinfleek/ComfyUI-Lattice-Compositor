/**
 * AI-Powered Camera Tracking Service
 *
 * Integrates VLM-based camera motion understanding with depth estimation
 * to provide camera tracking capabilities for Uni3C and other workflows.
 *
 * Approaches:
 * 1. Semantic: VLM detects camera motion type → maps to trajectory preset
 * 2. Geometric: Depth estimation + optical flow → precise camera path
 * 3. Hybrid: Combines both for best results
 */

import type {
  CameraIntrinsics,
  CameraPose,
  CameraTrackingSolve,
} from "@/types/cameraTracking";
import { isFiniteNumber, safeNonNegativeDefault } from "@/utils/typeGuards";

/**
 * Camera motion primitives taxonomy (from CameraBench)
 * VLMs can classify video clips into these categories
 */
export type CameraMotionPrimitive =
  // Static
  | "static"
  | "zoom_in"
  | "zoom_out"
  // Translation
  | "push_in"
  | "pull_out"
  | "truck_left"
  | "truck_right"
  | "pedestal_up"
  | "pedestal_down"
  | "arc_left"
  | "arc_right"
  // Rotation
  | "pan_left"
  | "pan_right"
  | "tilt_up"
  | "tilt_down"
  | "roll_clockwise"
  | "roll_counter_clockwise"
  // Complex
  | "tracking_shot"
  | "crane_up"
  | "crane_down"
  | "random_motion"
  | "unknown";

/**
 * Map camera motion primitives to Lattice trajectory presets
 */
export const MOTION_TO_TRAJECTORY: Record<
  CameraMotionPrimitive,
  string | null
> = {
  static: null,
  zoom_in: "dollyIn",
  zoom_out: "dollyOut",
  push_in: "dollyIn",
  pull_out: "dollyOut",
  truck_left: "truckLeft",
  truck_right: "truckRight",
  pedestal_up: "pedestalUp",
  pedestal_down: "pedestalDown",
  arc_left: "orbit",
  arc_right: "orbit",
  pan_left: "whipPan",
  pan_right: "whipPan",
  tilt_up: "craneUp",
  tilt_down: "craneDown",
  roll_clockwise: null,
  roll_counter_clockwise: null,
  tracking_shot: "dollyIn",
  crane_up: "craneUp",
  crane_down: "craneDown",
  random_motion: "shake",
  unknown: null,
};

/**
 * VLM camera motion analysis request
 */
export interface CameraMotionAnalysisRequest {
  /** Video frames as base64 or URLs */
  frames: string[];
  /** Frame rate */
  fps: number;
  /** Analysis mode */
  mode: "semantic" | "geometric" | "hybrid";
  /** Optional: known camera intrinsics */
  intrinsics?: CameraIntrinsics;
}

/**
 * VLM camera motion analysis result
 */
export interface CameraMotionAnalysisResult {
  /** Detected motion primitives per segment */
  segments: Array<{
    startFrame: number;
    endFrame: number;
    motion: CameraMotionPrimitive;
    confidence: number;
    description: string;
  }>;
  /** Overall motion summary */
  summary: string;
  /** Suggested trajectory preset */
  suggestedPreset: string | null;
  /** If geometric mode, includes camera solve */
  solve?: CameraTrackingSolve;
}

/**
 * System prompt for VLM camera motion analysis
 * Based on CameraBench taxonomy
 */
export const CAMERA_MOTION_SYSTEM_PROMPT = `You are an expert cinematographer analyzing camera motion in video footage.

Analyze the provided video frames and identify the camera movement using this taxonomy:

STATIC MOVEMENTS:
- static: Camera is stationary, no movement
- zoom_in: Optical zoom toward subject (focal length changes, position fixed)
- zoom_out: Optical zoom away from subject

TRANSLATION MOVEMENTS (camera position changes):
- push_in: Camera physically moves toward subject (dolly in)
- pull_out: Camera physically moves away from subject (dolly out)
- truck_left: Camera moves left parallel to subject
- truck_right: Camera moves right parallel to subject
- pedestal_up: Camera moves vertically up
- pedestal_down: Camera moves vertically down
- arc_left: Camera moves in arc around subject (left)
- arc_right: Camera moves in arc around subject (right)

ROTATION MOVEMENTS (camera orientation changes):
- pan_left: Camera rotates left on vertical axis
- pan_right: Camera rotates right on vertical axis
- tilt_up: Camera rotates up on horizontal axis
- tilt_down: Camera rotates down on horizontal axis
- roll_clockwise: Camera rotates clockwise on lens axis
- roll_counter_clockwise: Camera rotates counter-clockwise

COMPLEX MOVEMENTS:
- tracking_shot: Camera follows a moving subject
- crane_up: Combined vertical movement + tilt
- crane_down: Combined vertical movement + tilt
- random_motion: Handheld, unstable, or unpredictable motion

For each distinct segment of camera motion, provide:
1. Frame range (start_frame to end_frame)
2. Motion type from the taxonomy above
3. Confidence (0.0 to 1.0)
4. Brief description of the movement

Respond in JSON format:
{
  "segments": [
    {"startFrame": 0, "endFrame": 30, "motion": "push_in", "confidence": 0.9, "description": "Slow dolly toward subject's face"}
  ],
  "summary": "Overall camera motion description",
  "suggestedPreset": "dollyIn"
}`;

/**
 * Analyze camera motion using VLM
 *
 * This sends frames to the backend which proxies to OpenAI/Anthropic
 */
export async function analyzeWithVLM(
  request: CameraMotionAnalysisRequest,
): Promise<CameraMotionAnalysisResult> {
  // Sample frames evenly (max 8 for VLM context)
  const sampledFrames = sampleFrames(request.frames, 8);

  const response = await fetch("/lattice/api/ai/camera-motion", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({
      frames: sampledFrames,
      fps: request.fps,
      systemPrompt: CAMERA_MOTION_SYSTEM_PROMPT,
    }),
  });

  if (!response.ok) {
    throw new Error(`Camera motion analysis failed: ${response.statusText}`);
  }

  const result = await response.json();
  return parseVLMResponse(result);
}

/**
 * Sample frames evenly from array
 */
function sampleFrames(frames: string[], maxFrames: number): string[] {
  if (frames.length <= maxFrames) return frames;

  const step = (frames.length - 1) / (maxFrames - 1);
  const sampled: string[] = [];

  for (let i = 0; i < maxFrames; i++) {
    const index = Math.round(i * step);
    sampled.push(frames[index]);
  }

  return sampled;
}

/**
 * VLM API response structure
 */
interface VLMResponseSegment {
  startFrame?: number | string;
  endFrame?: number | string;
  motion?: string;
  confidence?: number | string;
  description?: string;
}

interface VLMResponse {
  segments?: VLMResponseSegment[];
  summary?: string;
}

import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

/**
 * Parse VLM JSON response
 */
function parseVLMResponse(raw: RuntimeValue): CameraMotionAnalysisResult {
  if (typeof raw !== "object" || raw === null) {
    return {
      segments: [],
      summary: "Invalid response",
      suggestedPreset: null,
    };
  }

  const data = raw as VLMResponse;

  // Type proof: segments ∈ VLMResponseSegment[] | undefined → VLMResponseSegment[]
  const segmentsData = Array.isArray(data.segments) ? data.segments : [];
  const segments = segmentsData.map((seg) => {
    // Type proof: frame numbers ∈ number | NaN → number (≥ 0, frame index)
    const startFrameValue = typeof seg.startFrame === "number" ? seg.startFrame : Number(seg.startFrame);
    const endFrameValue = typeof seg.endFrame === "number" ? seg.endFrame : Number(seg.endFrame);
    const startFrame = Number.isFinite(startFrameValue) && startFrameValue >= 0 ? startFrameValue : 0;
    const endFrame = Number.isFinite(endFrameValue) && endFrameValue >= 0 ? endFrameValue : 0;
    
    // Type proof: confidence ∈ number | NaN → number (0-1 range, non-negative)
    const confidenceValue = typeof seg.confidence === "number" ? seg.confidence : Number(seg.confidence);
    const confidence = Number.isFinite(confidenceValue) && confidenceValue >= 0 && confidenceValue <= 1
      ? confidenceValue
      : 0.5;
    
    return {
      startFrame,
      endFrame,
      motion: (seg.motion as CameraMotionPrimitive) || "unknown",
      confidence,
      description: String(seg.description || ""),
    };
  });

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const firstSegment = (segments != null && Array.isArray(segments) && segments.length > 0) ? segments[0] : undefined;
  const firstSegmentMotion = (firstSegment != null && typeof firstSegment === "object" && "motion" in firstSegment && typeof firstSegment.motion === "string") ? firstSegment.motion : undefined;
  const motionKey = firstSegmentMotion != null ? firstSegmentMotion : "unknown";
  return {
    segments,
    summary: String(data.summary || "No motion detected"),
    suggestedPreset: MOTION_TO_TRAJECTORY[motionKey],
  };
}

/**
 * Depth-based camera tracking (geometric approach)
 *
 * Uses monocular depth estimation to derive camera motion.
 * This is what Uni3C's PCDController expects.
 */
export interface DepthBasedTrackingRequest {
  /** Depth maps per frame (from Depth Anything, etc.) */
  depthMaps: ImageData[];
  /** RGB frames for feature matching */
  rgbFrames: ImageData[];
  /** Frame rate */
  fps: number;
  /** Camera intrinsics (focal length, principal point) */
  intrinsics: CameraIntrinsics;
}

/**
 * Estimate camera path from depth maps
 *
 * This is a simplified implementation. For production use:
 * - COLMAP for full SfM
 * - ORB-SLAM for real-time
 * - RAFT + depth for optical flow based
 */
export function estimateCameraPosesFromDepth(
  request: DepthBasedTrackingRequest,
): CameraTrackingSolve {
  const cameraPath: CameraPose[] = [];
  const frameCount = request.depthMaps.length;

  // First frame is reference (identity pose)
  cameraPath.push({
    frame: 0,
    position: { x: 0, y: 0, z: 0 },
    rotation: { w: 1, x: 0, y: 0, z: 0 },
  });

  // For each subsequent frame, estimate relative pose
  for (let i = 1; i < frameCount; i++) {
    // In a real implementation, this would:
    // 1. Extract features from RGB frames
    // 2. Match features between frames
    // 3. Use depth to get 3D positions
    // 4. Estimate rigid transformation (ICP or similar)

    // Placeholder: accumulate small forward motion
    const prevPoint = cameraPath[i - 1];
    cameraPath.push({
      frame: i,
      position: {
        x: prevPoint.position.x,
        y: prevPoint.position.y,
        z: prevPoint.position.z + 0.01, // Small forward motion
      },
      rotation: prevPoint.rotation,
    });
  }

  return {
    version: "1.0",
    source: "lattice-depth-tracker",
    metadata: {
      sourceWidth: request.intrinsics.width,
      sourceHeight: request.intrinsics.height,
      frameRate: request.fps,
      frameCount,
      solveMethod: "depth-based",
    },
    intrinsics: request.intrinsics,
    cameraPath,
    trackPoints2D: [],
    trackPoints3D: [],
  };
}

/**
 * Convert Uni3C PCDController format to Lattice tracking format
 *
 * Uni3C uses a specific JSON format for camera data
 */
export interface Uni3CCameraData {
  /** Camera intrinsic matrix (3x3) */
  K: number[][];
  /** Camera poses per frame (4x4 extrinsic matrices) */
  poses: number[][][];
  /** Depth maps (paths or base64) */
  depth_maps?: string[];
  /** Point cloud data */
  point_cloud?: {
    points: number[][];
    colors?: number[][];
  };
}

export function parseUni3CFormat(
  data: Uni3CCameraData,
  fps: number = 16,
): CameraTrackingSolve {
  const cameraPath: CameraPose[] = [];

  for (let i = 0; i < data.poses.length; i++) {
    const mat = data.poses[i];

    // Extract position from 4x4 matrix (last column)
    const position = {
      x: mat[0][3],
      y: mat[1][3],
      z: mat[2][3],
    };

    // Extract rotation (convert 3x3 rotation matrix to quaternion)
    const rotation = matrixToQuaternion(mat);

    cameraPath.push({
      frame: i,
      position,
      rotation,
    });
  }

  // Extract intrinsics from K matrix
  // Assume 1920x1080 if not specified (common for video)
  const width = 1920;
  const height = 1080;
  const intrinsics: CameraIntrinsics = {
    focalLength: data.K[0][0], // fx
    principalPoint: {
      x: data.K[0][2], // cx
      y: data.K[1][2], // cy
    },
    width,
    height,
  };

  return {
    version: "1.0",
    source: "uni3c",
    metadata: {
      sourceWidth: width,
      sourceHeight: height,
      frameRate: fps,
      frameCount: data.poses.length,
      solveMethod: "uni3c-import",
    },
    intrinsics,
    cameraPath,
    trackPoints2D: [],
    trackPoints3D: data.point_cloud
      ? data.point_cloud.points.map((p, i) => ({
          id: `pt_${i}`,
          position: { x: p[0], y: p[1], z: p[2] },
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          color: (() => {
            const pointCloud = (data != null && typeof data === "object" && "point_cloud" in data && data.point_cloud != null && typeof data.point_cloud === "object") ? data.point_cloud : undefined;
            const pointCloudColors = (pointCloud != null && typeof pointCloud === "object" && "colors" in pointCloud && pointCloud.colors != null && Array.isArray(pointCloud.colors)) ? pointCloud.colors : undefined;
            const colorAtIndex = (pointCloudColors != null && Array.isArray(pointCloudColors) && i >= 0 && i < pointCloudColors.length) ? pointCloudColors[i] : undefined;
            if (colorAtIndex != null && Array.isArray(colorAtIndex) && colorAtIndex.length >= 3) {
              return {
                r: Math.round(colorAtIndex[0] * 255),
                g: Math.round(colorAtIndex[1] * 255),
                b: Math.round(colorAtIndex[2] * 255),
              };
            }
            return { r: 255, g: 255, b: 255 };
          })(),
          track2DIDs: [],
        }))
      : [],
  };
}

/**
 * Convert 3x3 rotation matrix to quaternion
 * Returns { w, x, y, z } to match CameraPose.rotation type
 */
function matrixToQuaternion(mat: number[][]): {
  w: number;
  x: number;
  y: number;
  z: number;
} {
  // Extract 3x3 rotation part
  const m00 = mat[0][0],
    m01 = mat[0][1],
    m02 = mat[0][2];
  const m10 = mat[1][0],
    m11 = mat[1][1],
    m12 = mat[1][2];
  const m20 = mat[2][0],
    m21 = mat[2][1],
    m22 = mat[2][2];

  const trace = m00 + m11 + m22;
  let x: number, y: number, z: number, w: number;

  if (trace > 0) {
    const s = 0.5 / Math.sqrt(trace + 1.0);
    w = 0.25 / s;
    x = (m21 - m12) * s;
    y = (m02 - m20) * s;
    z = (m10 - m01) * s;
  } else if (m00 > m11 && m00 > m22) {
    const s = 2.0 * Math.sqrt(1.0 + m00 - m11 - m22);
    w = (m21 - m12) / s;
    x = 0.25 * s;
    y = (m01 + m10) / s;
    z = (m02 + m20) / s;
  } else if (m11 > m22) {
    const s = 2.0 * Math.sqrt(1.0 + m11 - m00 - m22);
    w = (m02 - m20) / s;
    x = (m01 + m10) / s;
    y = 0.25 * s;
    z = (m12 + m21) / s;
  } else {
    const s = 2.0 * Math.sqrt(1.0 + m22 - m00 - m11);
    w = (m10 - m01) / s;
    x = (m02 + m20) / s;
    y = (m12 + m21) / s;
    z = 0.25 * s;
  }

  return { w, x, y, z };
}

/**
 * Export camera tracking to Uni3C format
 */
export function exportToUni3CFormat(
  solve: CameraTrackingSolve,
): Uni3CCameraData {
  // Get first intrinsics if array
  const intrinsics = Array.isArray(solve.intrinsics)
    ? solve.intrinsics[0]
    : solve.intrinsics;

  // Build K matrix from intrinsics
  const fx = intrinsics.focalLength;
  const fy = intrinsics.focalLength; // Assume square pixels
  // Type proof: principalPoint.x ∈ number | undefined → number
  const cx = intrinsics.principalPoint && isFiniteNumber(intrinsics.principalPoint.x)
    ? intrinsics.principalPoint.x
    : 960;
  // Type proof: principalPoint.y ∈ number | undefined → number
  const cy = intrinsics.principalPoint && isFiniteNumber(intrinsics.principalPoint.y)
    ? intrinsics.principalPoint.y
    : 540;

  const K = [
    [fx, 0, cx],
    [0, fy, cy],
    [0, 0, 1],
  ];

  // Convert camera path to 4x4 matrices (Uni3C expects 'poses')
  const poses = solve.cameraPath.map((pose) => {
    const rotMat = quaternionToMatrix(pose.rotation);
    return [
      [rotMat[0][0], rotMat[0][1], rotMat[0][2], pose.position.x],
      [rotMat[1][0], rotMat[1][1], rotMat[1][2], pose.position.y],
      [rotMat[2][0], rotMat[2][1], rotMat[2][2], pose.position.z],
      [0, 0, 0, 1],
    ];
  });

  // Convert 3D track points to point cloud
  // Type proof: trackPoints3D ∈ TrackPoint3D[] | undefined → TrackPoint3D[]
  const trackPoints = Array.isArray(solve.trackPoints3D) ? solve.trackPoints3D : [];
  const point_cloud =
    trackPoints.length > 0
      ? {
          points: trackPoints.map((p) => [
            p.position.x,
            p.position.y,
            p.position.z,
          ]),
          colors: trackPoints.map((p) => {
            // Color is typed as { r, g, b } | undefined - convert to 0-1 range
            const color = p.color;
            if (color) {
              return [color.r / 255, color.g / 255, color.b / 255];
            }
            // Default white color
            return [1, 1, 1];
          }),
        }
      : undefined;

  return { K, poses, point_cloud };
}

/**
 * Convert quaternion to 3x3 rotation matrix
 */
function quaternionToMatrix(q: {
  w: number;
  x: number;
  y: number;
  z: number;
}): number[][] {
  const { w, x, y, z } = q;

  return [
    [1 - 2 * y * y - 2 * z * z, 2 * x * y - 2 * z * w, 2 * x * z + 2 * y * w],
    [2 * x * y + 2 * z * w, 1 - 2 * x * x - 2 * z * z, 2 * y * z - 2 * x * w],
    [2 * x * z - 2 * y * w, 2 * y * z + 2 * x * w, 1 - 2 * x * x - 2 * y * y],
  ];
}

/**
 * Hybrid analysis: VLM semantic + depth geometric
 */
export async function analyzeHybrid(
  request: CameraMotionAnalysisRequest & { depthMaps?: ImageData[] },
): Promise<CameraMotionAnalysisResult> {
  // Get semantic analysis from VLM
  const semanticResult = await analyzeWithVLM(request);

  // If we have depth maps, enhance with geometric tracking
  if (request.depthMaps && request.depthMaps.length > 0 && request.intrinsics) {
    // This would require RGB frames as ImageData
    // For now, just return semantic result with a note
    console.log(
      "Hybrid mode: depth maps provided but RGB ImageData required for geometric tracking",
    );
  }

  return semanticResult;
}
