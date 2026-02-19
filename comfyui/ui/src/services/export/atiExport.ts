/**
 * ATI (Any-point Trajectory Inference) Export Service
 *
 * Exports trajectory data in ATI-compatible format for
 * ComfyUI-WanVideoWrapper's WanVideoATITracks node.
 *
 * ATI Format Requirements:
 * - JSON string input with tracks as `[[{x, y}, ...], ...]`
 * - Fixed 121 frames (FIXED_LENGTH constant)
 * - Coordinates centered around frame center
 * - Normalized to [-1, 1] based on SHORT EDGE
 * - Visibility encoded as float: 1.0 = visible, 0.0 = hidden
 *   (converted to -1/1 internally by process_tracks)
 *
 * @see https://github.com/kijai/ComfyUI-WanVideoWrapper/blob/main/ATI/nodes.py
 * @see https://github.com/kijai/ComfyUI-WanVideoWrapper/blob/main/ATI/motion.py
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import type { WanMoveTrajectory } from "./wanMoveExport";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                // constants
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Fixed frame count for ATI model
 * Must match FIXED_LENGTH in ATI/nodes.py
 */
export const ATI_FIXED_FRAMES = 121;

// ═══════════════════════════════════════════════════════════════════════════
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

/**
 * ATI track point with x, y coordinates
 */
export interface ATITrackPoint {
  x: number;
  y: number;
}

/**
 * ATI export result
 */
export interface ATIExportResult {
  /** JSON string for track_coords input */
  tracks: string;
  /** Width used for normalization */
  width: number;
  /** Height used for normalization */
  height: number;
  /** Number of tracks */
  numTracks: number;
  /** Original frame count before padding */
  originalFrames: number;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // export // functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Export trajectory as ATI-compatible JSON string
 *
 * This function:
 * 1. Pads or truncates tracks to exactly 121 frames
 * 2. Keeps coordinates in PIXEL space (normalization is done by the ATI node)
 * 3. Formats as `[[{x, y}, ...], ...]`
 *
 * Note: The ATI node does normalization internally via process_tracks().
 * The JSON input should contain RAW PIXEL coordinates, not normalized ones.
 *
 * @param trajectory - WanMove trajectory to convert
 * @returns JSON string ready for WanVideoATITracks node
 */
export function exportATITrackCoordsJSON(trajectory: WanMoveTrajectory): string {
  const { tracks, visibility, metadata } = trajectory;
  const { numFrames } = metadata;

  // Convert tracks to ATI format with 121 frame padding/truncation
  const atiTracks: ATITrackPoint[][] = tracks.map((track, trackIdx) => {
    const atiTrack: ATITrackPoint[] = [];

    for (let f = 0; f < ATI_FIXED_FRAMES; f++) {
      if (f < numFrames && f < track.length) {
        // Use actual track data
        const [x, y] = track[f];
        atiTrack.push({ x, y });
      } else if (track.length > 0) {
        // Pad with last known position (hold last frame)
        const lastFrame = track[track.length - 1];
        atiTrack.push({ x: lastFrame[0], y: lastFrame[1] });
      } else {
        // Empty track - use origin
        atiTrack.push({ x: 0, y: 0 });
      }
    }

    return atiTrack;
  });

  return JSON.stringify(atiTracks);
}

/**
 * Export trajectory with full ATI metadata
 *
 * Returns the complete export package including the JSON string
 * and metadata about the export.
 */
export function exportATIPackage(
  trajectory: WanMoveTrajectory,
): ATIExportResult {
  const { metadata } = trajectory;

  return {
    tracks: exportATITrackCoordsJSON(trajectory),
    width: metadata.width,
    height: metadata.height,
    numTracks: metadata.numPoints,
    originalFrames: metadata.numFrames,
  };
}

/**
 * Export trajectory as normalized ATI format
 *
 * This function pre-normalizes coordinates to [-1, 1] range as expected
 * by ATI's internal processing. Use this if you need the normalized values
 * directly (e.g., for visualization or debugging).
 *
 * Normalization formula (from ATI motion.py):
 * 1. Center: coords - [width/2, height/2]
 * 2. Normalize: coords / short_edge * 2
 *
 * @param trajectory - WanMove trajectory to convert
 * @returns Object with normalized tracks and visibility
 */
export function exportAsNormalizedATI(trajectory: WanMoveTrajectory): {
  /** Normalized tracks: [numTracks][121][{x, y, visible}] */
  tracks: Array<Array<{ x: number; y: number; visible: number }>>;
  /** Time range values: [121] values from -1 to 1 */
  timeRange: number[];
  /** Metadata */
  metadata: {
    width: number;
    height: number;
    shortEdge: number;
    numTracks: number;
  };
} {
  const { tracks, visibility, metadata } = trajectory;
  const { width, height, numFrames } = metadata;
  const shortEdge = Math.min(width, height);

  // Generate time range: -1 to 1 across 121 frames
  const timeRange: number[] = [];
  for (let f = 0; f < ATI_FIXED_FRAMES; f++) {
    const t = (f - ATI_FIXED_FRAMES / 2) / (ATI_FIXED_FRAMES / 2);
    timeRange.push(t);
  }

  // Normalize tracks
  const normalizedTracks = tracks.map((track, trackIdx) => {
    const normalizedTrack: Array<{ x: number; y: number; visible: number }> =
      [];

    for (let f = 0; f < ATI_FIXED_FRAMES; f++) {
      let x: number, y: number;
      let vis: boolean;

      if (f < numFrames && f < track.length) {
        [x, y] = track[f];
        // Type proof: visibility[trackIdx]?.[f] ∈ boolean | undefined → boolean
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const visibilityTrack = (visibility != null && Array.isArray(visibility) && trackIdx >= 0 && trackIdx < visibility.length) ? visibility[trackIdx] : undefined;
        const visValue = (visibilityTrack != null && Array.isArray(visibilityTrack) && f >= 0 && f < visibilityTrack.length) ? visibilityTrack[f] : undefined;
        vis = typeof visValue === "boolean" ? visValue : true;
      } else if (track.length > 0) {
        // Pad with last known position
        const lastIdx = Math.min(numFrames - 1, track.length - 1);
        [x, y] = track[lastIdx];
        // Type proof: visibility[trackIdx]?.[lastIdx] ∈ boolean | undefined → boolean
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const visibilityTrack = (visibility != null && Array.isArray(visibility) && trackIdx >= 0 && trackIdx < visibility.length) ? visibility[trackIdx] : undefined;
        const visLastValue = (visibilityTrack != null && Array.isArray(visibilityTrack) && lastIdx >= 0 && lastIdx < visibilityTrack.length) ? visibilityTrack[lastIdx] : undefined;
        vis = typeof visLastValue === "boolean" ? visLastValue : true;
      } else {
        x = width / 2;
        y = height / 2;
        vis = false;
      }

      // Center around frame center
      const centeredX = x - width / 2;
      const centeredY = y - height / 2;

      // Normalize by short edge to [-1, 1] range
      const normX = (centeredX / shortEdge) * 2;
      const normY = (centeredY / shortEdge) * 2;

      // Visibility: ATI node converts 0/1 to -1/1 via (vis * 2 - 1)
      // We store as 0/1 here, matching the input to process_tracks
      const visFloat = vis ? 1.0 : 0.0;

      normalizedTrack.push({ x: normX, y: normY, visible: visFloat });
    }

    return normalizedTrack;
  });

  return {
    tracks: normalizedTracks,
    timeRange,
    metadata: {
      width,
      height,
      shortEdge,
      numTracks: tracks.length,
    },
  };
}

/**
 * Validate trajectory for ATI compatibility
 *
 * Checks if the trajectory meets ATI requirements and returns
 * warnings for potential issues.
 */
export function validateForATI(trajectory: WanMoveTrajectory): {
  valid: boolean;
  warnings: string[];
  errors: string[];
} {
  const warnings: string[] = [];
  const errors: string[] = [];

  const { tracks, metadata } = trajectory;
  const { numFrames, numPoints, width, height } = metadata;

  // Check track count
  if (numPoints === 0) {
    errors.push("No tracks provided");
  }

  // Check frame count
  if (numFrames > ATI_FIXED_FRAMES) {
    warnings.push(
      `Trajectory has ${numFrames} frames but ATI uses ${ATI_FIXED_FRAMES}. ` +
        `Frames beyond ${ATI_FIXED_FRAMES} will be truncated.`,
    );
  } else if (numFrames < ATI_FIXED_FRAMES) {
    warnings.push(
      `Trajectory has ${numFrames} frames but ATI expects ${ATI_FIXED_FRAMES}. ` +
        `Last frame will be held to pad the remaining ${ATI_FIXED_FRAMES - numFrames} frames.`,
    );
  }

  // Check dimensions
  if (width <= 0 || height <= 0) {
    errors.push(`Invalid dimensions: ${width}x${height}`);
  }

  // Check for out-of-bounds coordinates
  let outOfBoundsCount = 0;
  for (const track of tracks) {
    for (const [x, y] of track) {
      if (x < 0 || x > width || y < 0 || y > height) {
        outOfBoundsCount++;
      }
    }
  }

  if (outOfBoundsCount > 0) {
    warnings.push(
      `${outOfBoundsCount} track points are outside the frame bounds (${width}x${height}). ` +
        `These will be normalized but may produce unexpected results.`,
    );
  }

  return {
    valid: errors.length === 0,
    warnings,
    errors,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // helper // functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Create an ATI-compatible trajectory from raw point data
 *
 * Convenience function for creating trajectories from simple point arrays.
 */
export function createATITrajectory(
  points: Array<{ x: number; y: number }[]>,
  width: number,
  height: number,
  fps: number = 16,
): WanMoveTrajectory {
  const numPoints = points.length;
  // Type proof: points[0]?.length ∈ number | undefined → number
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const firstPoint = (points != null && Array.isArray(points) && points.length > 0) ? points[0] : undefined;
  const firstPointLength = (firstPoint != null && Array.isArray(firstPoint)) ? firstPoint.length : undefined;
  const numFrames = isFiniteNumber(firstPointLength) && Number.isInteger(firstPointLength) && firstPointLength >= 0 ? firstPointLength : 0;

  // Convert to WanMove format
  const tracks: number[][][] = points.map((track) =>
    track.map((pt) => [pt.x, pt.y]),
  );

  // All visible by default
  const visibility: boolean[][] = tracks.map((track) =>
    track.map(() => true),
  );

  return {
    tracks,
    visibility,
    metadata: {
      numPoints,
      numFrames,
      width,
      height,
      fps,
    },
  };
}
