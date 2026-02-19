/**
 * WorkflowParams Schema Tests
 *
 * Tests that motionData schemas match what workflow templates expect.
 * CRITICAL: These tests ensure property names match model requirements.
 */

import { describe, it, expect } from "vitest";
import {
  WanMoveMotionDataSchema,
  ATIMotionDataSchema,
  validateWanMoveMotionData,
  validateATIMotionData,
  safeValidateWanMoveMotionData,
  safeValidateATIMotionData,
} from "@/schemas/exports/workflow-params-schema";
import { transformWanMoveToMotionData, transformATIToMotionData } from "@/services/export/exportToWorkflowParams";
import type { UnifiedExportResult } from "@/services/modelExport";
import type { WanMoveTrajectory } from "@/services/export/wanMoveExport";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Test Data
// ═══════════════════════════════════════════════════════════════════════════

const createWanMoveTrajectory = (): WanMoveTrajectory => ({
  tracks: [
    [
      [100, 200],
      [110, 210],
      [120, 220],
    ],
    [
      [300, 400],
      [310, 410],
      [320, 420],
    ],
  ],
  visibility: [
    [true, true, true],
    [true, true, true],
  ],
  metadata: {
    numPoints: 2,
    numFrames: 3,
    width: 1920,
    height: 1080,
    fps: 24,
  },
});

const createUnifiedExportResult = (
  data: WanMoveTrajectory,
): UnifiedExportResult & { data: WanMoveTrajectory } => ({
  success: true,
  target: "wan-move",
  data,
  files: [],
});

// ═══════════════════════════════════════════════════════════════════════════
// WanMove MotionData Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("WanMoveMotionDataSchema", () => {
  it("validates correct WanMove motionData structure", () => {
    const validData = {
      tracks: [
        [{ x: 100, y: 200 }, { x: 110, y: 210 }],
        [{ x: 300, y: 400 }, { x: 310, y: 410 }],
      ],
    };

    const result = WanMoveMotionDataSchema.safeParse(validData);
    expect(result.success).toBe(true);
    if (result.success) {
      expect(result.data.tracks).toHaveLength(2);
      expect(result.data.tracks[0]).toHaveLength(2);
      expect(result.data.tracks[0][0]).toEqual({ x: 100, y: 200 });
    }
  });

  it("rejects invalid track point structure", () => {
    const invalidData = {
      tracks: [
        [[100, 200], [110, 210]], // Array format instead of {x, y}
      ],
    };

    const result = WanMoveMotionDataSchema.safeParse(invalidData);
    expect(result.success).toBe(false);
  });

  it("rejects missing tracks property", () => {
    const invalidData = {};

    const result = WanMoveMotionDataSchema.safeParse(invalidData);
    expect(result.success).toBe(false);
  });

  it("rejects non-finite numbers", () => {
    const invalidData = {
      tracks: [
        [{ x: Infinity, y: 200 }],
      ],
    };

    const result = WanMoveMotionDataSchema.safeParse(invalidData);
    expect(result.success).toBe(false);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// ATI MotionData Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("ATIMotionDataSchema", () => {
  it("validates correct ATI motionData structure", () => {
    const validData = {
      trajectories: [
        [{ x: 100, y: 200 }, { x: 110, y: 210 }],
        [{ x: 300, y: 400 }, { x: 310, y: 410 }],
      ],
    };

    const result = ATIMotionDataSchema.safeParse(validData);
    expect(result.success).toBe(true);
    if (result.success) {
      expect(result.data.trajectories).toHaveLength(2);
      expect(result.data.trajectories[0]).toHaveLength(2);
      expect(result.data.trajectories[0][0]).toEqual({ x: 100, y: 200 });
    }
  });

  it("rejects tracks property (should be trajectories)", () => {
    const invalidData = {
      tracks: [
        [{ x: 100, y: 200 }],
      ],
    };

    const result = ATIMotionDataSchema.safeParse(invalidData);
    expect(result.success).toBe(false);
  });

  it("rejects missing trajectories property", () => {
    const invalidData = {};

    const result = ATIMotionDataSchema.safeParse(invalidData);
    expect(result.success).toBe(false);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Transformation Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("transformWanMoveToMotionData", () => {
  it("transforms WanMoveTrajectory to motionData format", () => {
    const trajectory = createWanMoveTrajectory();
    const exportResult = createUnifiedExportResult(trajectory);

    const motionData = transformWanMoveToMotionData(exportResult);

    expect(motionData.tracks).toHaveLength(2);
    expect(motionData.tracks[0]).toHaveLength(3);
    expect(motionData.tracks[0][0]).toEqual({ x: 100, y: 200 });
    expect(motionData.tracks[0][1]).toEqual({ x: 110, y: 210 });
    expect(motionData.tracks[0][2]).toEqual({ x: 120, y: 220 });
  });

  it("validates output matches schema", () => {
    const trajectory = createWanMoveTrajectory();
    const exportResult = createUnifiedExportResult(trajectory);

    const motionData = transformWanMoveToMotionData(exportResult);
    const validation = safeValidateWanMoveMotionData(motionData);

    expect(validation.success).toBe(true);
  });
});

describe("transformATIToMotionData", () => {
  it("transforms WanMoveTrajectory to ATI motionData format", () => {
    const trajectory = createWanMoveTrajectory();
    const exportResult = createUnifiedExportResult(trajectory);

    const motionData = transformATIToMotionData(exportResult);

    expect(motionData.trajectories).toHaveLength(2);
    expect(motionData.trajectories[0]).toHaveLength(3);
    expect(motionData.trajectories[0][0]).toEqual({ x: 100, y: 200 });
  });

  it("validates output matches schema", () => {
    const trajectory = createWanMoveTrajectory();
    const exportResult = createUnifiedExportResult(trajectory);

    const motionData = transformATIToMotionData(exportResult);
    const validation = safeValidateATIMotionData(motionData);

    expect(validation.success).toBe(true);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Property Name Verification
// ═══════════════════════════════════════════════════════════════════════════

describe("Property name verification", () => {
  it("WanMove motionData has 'tracks' property (not 'trajectories')", () => {
    const trajectory = createWanMoveTrajectory();
    const exportResult = createUnifiedExportResult(trajectory);
    const motionData = transformWanMoveToMotionData(exportResult);

    expect(motionData).toHaveProperty("tracks");
    expect(motionData).not.toHaveProperty("trajectories");
  });

  it("ATI motionData has 'trajectories' property (not 'tracks')", () => {
    const trajectory = createWanMoveTrajectory();
    const exportResult = createUnifiedExportResult(trajectory);
    const motionData = transformATIToMotionData(exportResult);

    expect(motionData).toHaveProperty("trajectories");
    expect(motionData).not.toHaveProperty("tracks");
  });
});
