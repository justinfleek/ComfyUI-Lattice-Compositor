/**
 * Export to WorkflowParams Transformation
 *
 * Transforms UnifiedExportResult into WorkflowParams.motionData.
 * This ensures property names match what workflow templates expect.
 *
 * CRITICAL: This is the boundary where export function outputs become
 * workflow template inputs. Property names MUST match exactly.
 */

import type { UnifiedExportResult } from "@/services/modelExport";
import type { WanMoveTrajectory } from "@/services/export/wanMoveExport";
import {
  validateWanMoveMotionData,
  validateATIMotionData,
  type WanMoveMotionData,
  type ATIMotionData,
} from "@/schemas/exports/workflow-params-schema";

// ============================================================================
// Transformation Functions
// ============================================================================

/**
 * Transform WanMove export result to WorkflowParams.motionData
 *
 * Converts WanMoveTrajectory (tracks: number[][][]) to motionData format
 * (tracks: Array<Array<{x, y}>>) that workflow templates expect.
 */
export function transformWanMoveToMotionData(
  exportResult: UnifiedExportResult & { data: WanMoveTrajectory },
): WanMoveMotionData {
  const { tracks } = exportResult.data;

  // Convert from number[][][] to {x, y}[][]
  // Lattice format: tracks[pointIdx][frameIdx][0=x, 1=y]
  // Workflow format: tracks[trackIdx][frameIdx] = {x, y}
  const formattedTracks: Array<Array<{ x: number; y: number }>> = tracks.map(
    (track: number[][]) => track.map((point: number[]) => {
      const [x, y] = point;
      return { x, y };
    }),
  );

  const motionData: WanMoveMotionData = { tracks: formattedTracks };

  // Validate before returning
  return validateWanMoveMotionData(motionData);
}

/**
 * Transform ATI export result to WorkflowParams.motionData
 *
 * Converts WanMoveTrajectory to ATI motionData format.
 * ATI uses same structure as WanMove but property name is "trajectories".
 */
export function transformATIToMotionData(
  exportResult: UnifiedExportResult & { data: WanMoveTrajectory },
): ATIMotionData {
  const { tracks } = exportResult.data;

  // Convert from number[][][] to {x, y}[][]
  const formattedTrajectories: Array<Array<{ x: number; y: number }>> =
    tracks.map((track: number[][]) => track.map((point: number[]) => {
      const [x, y] = point;
      return { x, y };
    }));

  const motionData: ATIMotionData = {
    trajectories: formattedTrajectories,
  };

  // Validate before returning
  return validateATIMotionData(motionData);
}

/**
 * Transform export result to WorkflowParams.motionData based on target
 */
export function transformExportToMotionData(
  target: "wan-move" | "ati",
  exportResult: UnifiedExportResult,
): WanMoveMotionData | ATIMotionData {
  if (!exportResult.success || !exportResult.data) {
    throw new Error(
      `Cannot transform failed export result to motionData for target: ${target}`,
    );
  }

  switch (target) {
    case "wan-move":
      return transformWanMoveToMotionData(
        exportResult as UnifiedExportResult & { data: WanMoveTrajectory },
      );

    case "ati":
      return transformATIToMotionData(
        exportResult as UnifiedExportResult & { data: WanMoveTrajectory },
      );

    default:
      throw new Error(`Unknown export target for motionData transformation: ${target}`);
  }
}
