/**
 * ATI (Any-point Trajectory Inference) Export Tests
 *
 * Tests for ATI-compatible export format used by
 * ComfyUI-WanVideoWrapper's WanVideoATITracks node.
 *
 * @audit P0 CRITICAL - ATI format compliance for WanVideoWrapper
 */

import { describe, it, expect } from "vitest";
import {
  ATI_FIXED_FRAMES,
  exportATITrackCoordsJSON,
  exportATIPackage,
  exportAsNormalizedATI,
  validateForATI,
  createATITrajectory,
  type ATITrackPoint,
  type ATIExportResult,
} from "@/services/export/atiExport";
import type { WanMoveTrajectory } from "@/services/export/wanMoveExport";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Test Helpers
// ═══════════════════════════════════════════════════════════════════════════

function createTestTrajectory(
  numPoints: number,
  numFrames: number,
  width: number = 1920,
  height: number = 1080
): WanMoveTrajectory {
  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let p = 0; p < numPoints; p++) {
    const track: number[][] = [];
    const vis: boolean[] = [];
    for (let f = 0; f < numFrames; f++) {
      // Create simple linear motion for testing
      track.push([100 + f * 10 + p * 50, 100 + f * 5 + p * 30]);
      vis.push(true);
    }
    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: {
      numPoints,
      numFrames,
      width,
      height,
      fps: 16,
    },
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// Constants Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("ATI_FIXED_FRAMES", () => {
  it("should be exactly 121 frames", () => {
    expect(ATI_FIXED_FRAMES).toBe(121);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// exportATITrackCoordsJSON Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("exportATITrackCoordsJSON", () => {
  it("should export as valid JSON string", () => {
    const trajectory = createTestTrajectory(3, 50);

    const json = exportATITrackCoordsJSON(trajectory);

    expect(typeof json).toBe("string");
    expect(() => JSON.parse(json)).not.toThrow();
  });

  it("should produce exactly 121 frames per track", () => {
    const trajectory = createTestTrajectory(5, 50);

    const json = exportATITrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json) as ATITrackPoint[][];

    expect(parsed.length).toBe(5); // 5 tracks
    for (const track of parsed) {
      expect(track.length).toBe(121); // Each track has exactly 121 frames
    }
  });

  it("should use {x, y} object format", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [[[100, 200]]],
      visibility: [[true]],
      metadata: {
        numPoints: 1,
        numFrames: 1,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const json = exportATITrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json);

    expect(parsed[0][0]).toEqual({ x: 100, y: 200 });
  });

  it("should pad short trajectories by holding last frame", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [
        [[10, 20], [30, 40], [50, 60]], // Only 3 frames
      ],
      visibility: [[true, true, true]],
      metadata: {
        numPoints: 1,
        numFrames: 3,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const json = exportATITrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json) as ATITrackPoint[][];

    // First 3 frames should be original data
    expect(parsed[0][0]).toEqual({ x: 10, y: 20 });
    expect(parsed[0][1]).toEqual({ x: 30, y: 40 });
    expect(parsed[0][2]).toEqual({ x: 50, y: 60 });

    // Remaining frames should hold last position
    expect(parsed[0][3]).toEqual({ x: 50, y: 60 });
    expect(parsed[0][120]).toEqual({ x: 50, y: 60 });
  });

  it("should truncate long trajectories to 121 frames", () => {
    const trajectory = createTestTrajectory(2, 200); // 200 frames > 121

    const json = exportATITrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json) as ATITrackPoint[][];

    expect(parsed[0].length).toBe(121);
    expect(parsed[1].length).toBe(121);
  });

  it("should handle empty track gracefully", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [[]],
      visibility: [[]],
      metadata: {
        numPoints: 1,
        numFrames: 0,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const json = exportATITrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json) as ATITrackPoint[][];

    expect(parsed[0].length).toBe(121);
    // Empty tracks default to origin
    expect(parsed[0][0]).toEqual({ x: 0, y: 0 });
  });

  it("should preserve exact coordinate values", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [[[123.456, 789.012]]],
      visibility: [[true]],
      metadata: {
        numPoints: 1,
        numFrames: 1,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const json = exportATITrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json);

    expect(parsed[0][0].x).toBe(123.456);
    expect(parsed[0][0].y).toBe(789.012);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// exportATIPackage Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("exportATIPackage", () => {
  it("should return complete ATIExportResult", () => {
    const trajectory = createTestTrajectory(5, 60, 1920, 1080);

    const result = exportATIPackage(trajectory);

    expect(result).toHaveProperty("tracks");
    expect(result).toHaveProperty("width");
    expect(result).toHaveProperty("height");
    expect(result).toHaveProperty("numTracks");
    expect(result).toHaveProperty("originalFrames");
  });

  it("should include correct metadata", () => {
    const trajectory = createTestTrajectory(10, 80, 1280, 720);

    const result = exportATIPackage(trajectory);

    expect(result.width).toBe(1280);
    expect(result.height).toBe(720);
    expect(result.numTracks).toBe(10);
    expect(result.originalFrames).toBe(80);
  });

  it("should have tracks as valid JSON string", () => {
    const trajectory = createTestTrajectory(3, 50);

    const result = exportATIPackage(trajectory);

    expect(typeof result.tracks).toBe("string");
    expect(() => JSON.parse(result.tracks)).not.toThrow();
  });

  it("should match exportATITrackCoordsJSON output", () => {
    const trajectory = createTestTrajectory(5, 100);

    const result = exportATIPackage(trajectory);
    const direct = exportATITrackCoordsJSON(trajectory);

    expect(result.tracks).toBe(direct);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// exportAsNormalizedATI Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("exportAsNormalizedATI", () => {
  it("should return normalized tracks with visibility", () => {
    const trajectory = createTestTrajectory(3, 50, 1920, 1080);

    const result = exportAsNormalizedATI(trajectory);

    expect(result.tracks.length).toBe(3);
    expect(result.tracks[0].length).toBe(121); // Always 121 frames
    expect(result.tracks[0][0]).toHaveProperty("x");
    expect(result.tracks[0][0]).toHaveProperty("y");
    expect(result.tracks[0][0]).toHaveProperty("visible");
  });

  it("should center coordinates around frame center", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [
        [[960, 540]], // Center of 1920x1080
      ],
      visibility: [[true]],
      metadata: {
        numPoints: 1,
        numFrames: 1,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const result = exportAsNormalizedATI(trajectory);

    // Center point should be at (0, 0) after centering
    expect(result.tracks[0][0].x).toBeCloseTo(0);
    expect(result.tracks[0][0].y).toBeCloseTo(0);
  });

  it("should normalize by short edge", () => {
    // For 1920x1080, short edge is 1080
    // Point at (1500, 540) = center + (540, 0)
    // Normalized: (540/1080)*2 = 1.0 for x, 0 for y
    const trajectory: WanMoveTrajectory = {
      tracks: [
        [[1500, 540]], // 540 pixels right of center
      ],
      visibility: [[true]],
      metadata: {
        numPoints: 1,
        numFrames: 1,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const result = exportAsNormalizedATI(trajectory);

    // (1500 - 960) / 1080 * 2 = 540 / 1080 * 2 = 1.0
    expect(result.tracks[0][0].x).toBeCloseTo(1.0);
    expect(result.tracks[0][0].y).toBeCloseTo(0);
  });

  it("should include time range from -1 to 1", () => {
    const trajectory = createTestTrajectory(1, 10);

    const result = exportAsNormalizedATI(trajectory);

    expect(result.timeRange.length).toBe(121);
    expect(result.timeRange[0]).toBeLessThan(0);
    expect(result.timeRange[60]).toBeCloseTo(0, 1); // Middle should be near 0
    expect(result.timeRange[120]).toBeGreaterThan(0);
  });

  it("should include correct metadata", () => {
    const trajectory = createTestTrajectory(5, 30, 1280, 720);

    const result = exportAsNormalizedATI(trajectory);

    expect(result.metadata.width).toBe(1280);
    expect(result.metadata.height).toBe(720);
    expect(result.metadata.shortEdge).toBe(720);
    expect(result.metadata.numTracks).toBe(5);
  });

  it("should encode visibility as 0 or 1", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [[[100, 100]]],
      visibility: [[true]],
      metadata: {
        numPoints: 1,
        numFrames: 1,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const result = exportAsNormalizedATI(trajectory);

    expect(result.tracks[0][0].visible).toBe(1.0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// validateForATI Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("validateForATI", () => {
  it("should return valid for proper trajectory", () => {
    const trajectory = createTestTrajectory(5, 121);

    const result = validateForATI(trajectory);

    expect(result.valid).toBe(true);
    expect(result.errors.length).toBe(0);
  });

  it("should error for empty tracks", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [],
      visibility: [],
      metadata: {
        numPoints: 0,
        numFrames: 0,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const result = validateForATI(trajectory);

    expect(result.valid).toBe(false);
    expect(result.errors).toContain("No tracks provided");
  });

  it("should warn for frames exceeding 121", () => {
    const trajectory = createTestTrajectory(3, 200);

    const result = validateForATI(trajectory);

    expect(result.valid).toBe(true);
    expect(result.warnings.length).toBeGreaterThan(0);
    expect(result.warnings[0]).toContain("truncated");
  });

  it("should warn for frames less than 121", () => {
    const trajectory = createTestTrajectory(3, 50);

    const result = validateForATI(trajectory);

    expect(result.valid).toBe(true);
    expect(result.warnings.length).toBeGreaterThan(0);
    expect(result.warnings[0]).toContain("pad");
  });

  it("should not warn for exactly 121 frames", () => {
    const trajectory = createTestTrajectory(5, 121);

    const result = validateForATI(trajectory);

    // Should have no frame-related warnings
    const frameWarnings = result.warnings.filter(
      (w) => w.includes("frame") || w.includes("Frame")
    );
    expect(frameWarnings.length).toBe(0);
  });

  it("should error for invalid dimensions", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [[[100, 100]]],
      visibility: [[true]],
      metadata: {
        numPoints: 1,
        numFrames: 1,
        width: 0,
        height: -1,
        fps: 16,
      },
    };

    const result = validateForATI(trajectory);

    expect(result.valid).toBe(false);
    expect(result.errors.some((e) => e.includes("dimensions"))).toBe(true);
  });

  it("should warn for out-of-bounds coordinates", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [
        [
          [-100, 50], // Negative X
          [2000, 50], // X > width
          [100, 1200], // Y > height
        ],
      ],
      visibility: [[true, true, true]],
      metadata: {
        numPoints: 1,
        numFrames: 3,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const result = validateForATI(trajectory);

    expect(result.valid).toBe(true);
    expect(result.warnings.some((w) => w.includes("outside"))).toBe(true);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createATITrajectory Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("createATITrajectory", () => {
  it("should create valid WanMoveTrajectory from point arrays", () => {
    const points = [
      [
        { x: 100, y: 100 },
        { x: 110, y: 110 },
        { x: 120, y: 120 },
      ],
      [
        { x: 200, y: 200 },
        { x: 210, y: 210 },
        { x: 220, y: 220 },
      ],
    ];

    const trajectory = createATITrajectory(points, 1920, 1080);

    expect(trajectory.tracks.length).toBe(2);
    expect(trajectory.tracks[0].length).toBe(3);
    expect(trajectory.tracks[0][0]).toEqual([100, 100]);
    expect(trajectory.metadata.numPoints).toBe(2);
    expect(trajectory.metadata.numFrames).toBe(3);
  });

  it("should set all visibility to true", () => {
    const points = [
      [{ x: 100, y: 100 }],
    ];

    const trajectory = createATITrajectory(points, 1920, 1080);

    expect(trajectory.visibility[0][0]).toBe(true);
  });

  it("should use provided dimensions", () => {
    const points = [[{ x: 50, y: 50 }]];

    const trajectory = createATITrajectory(points, 1280, 720, 30);

    expect(trajectory.metadata.width).toBe(1280);
    expect(trajectory.metadata.height).toBe(720);
    expect(trajectory.metadata.fps).toBe(30);
  });

  it("should default fps to 16", () => {
    const points = [[{ x: 50, y: 50 }]];

    const trajectory = createATITrajectory(points, 1920, 1080);

    expect(trajectory.metadata.fps).toBe(16);
  });

  it("should handle empty points array", () => {
    const trajectory = createATITrajectory([], 1920, 1080);

    expect(trajectory.tracks.length).toBe(0);
    expect(trajectory.metadata.numPoints).toBe(0);
    expect(trajectory.metadata.numFrames).toBe(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Round-trip Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("Round-trip export", () => {
  it("should produce consistent output for same input", () => {
    const trajectory = createTestTrajectory(10, 100);

    const result1 = exportATITrackCoordsJSON(trajectory);
    const result2 = exportATITrackCoordsJSON(trajectory);

    expect(result1).toBe(result2);
  });

  it("should be parseable back to ATITrackPoint format", () => {
    const trajectory = createTestTrajectory(5, 50);

    const json = exportATITrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json) as ATITrackPoint[][];

    // Verify structure
    expect(Array.isArray(parsed)).toBe(true);
    expect(parsed.length).toBe(5);

    for (const track of parsed) {
      expect(track.length).toBe(121);
      for (const point of track) {
        expect(typeof point.x).toBe("number");
        expect(typeof point.y).toBe("number");
        expect(Number.isFinite(point.x)).toBe(true);
        expect(Number.isFinite(point.y)).toBe(true);
      }
    }
  });
});
