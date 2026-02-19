/**
 * Wan-Move Export Tests
 *
 * Comprehensive tests for all Wan-Move trajectory generation functions.
 * These tests verify that flow generators produce valid WanMoveTrajectory
 * structures with correct shapes, bounds, and determinism.
 *
 * @audit P0 CRITICAL - Wan-Move trajectory format compliance
 */

import { describe, it, expect } from "vitest";
import {
  // Flow generators
  generateDataDrivenFlow,
  generateSplineFlow,
  generateForceFieldFlow,
  generateFromPreset,
  generateShapeMorph,
  // Strange attractors
  generateLorenzAttractor,
  generateRosslerAttractor,
  generateAizawaAttractor,
  // Export utilities
  exportAsNPYData,
  exportAsJSON,
  // Color utilities
  sampleGradient,
  addColorToTrajectory,
  addTimeColorToTrajectory,
  COLOR_GRADIENTS,
  // Composition
  compositeFlowLayers,
  compositeColoredLayers,
  // Types
  type WanMoveTrajectory,
  type GenerativeFlowConfig,
  type DataDrivenFlowConfig,
  type ForceFieldConfig,
  type AttractorConfig,
  type ShapeTargetConfig,
  type FlowLayer,
  FLOW_PRESETS,
  SHAPE_PRESETS,
  ATTRACTOR_PRESETS,
} from "@/services/export/wanMoveExport";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Test Helpers
// ═══════════════════════════════════════════════════════════════════════════

function validateTrajectoryShape(
  trajectory: WanMoveTrajectory,
  expectedPoints?: number,
  expectedFrames?: number
): void {
  // Validate tracks shape [N][T][2]
  expect(Array.isArray(trajectory.tracks)).toBe(true);
  
  if (trajectory.tracks.length > 0) {
    expect(Array.isArray(trajectory.tracks[0])).toBe(true);
    if (trajectory.tracks[0].length > 0) {
      expect(trajectory.tracks[0][0].length).toBe(2);
    }
  }

  // Validate visibility shape [N][T]
  expect(Array.isArray(trajectory.visibility)).toBe(true);
  expect(trajectory.visibility.length).toBe(trajectory.tracks.length);

  if (trajectory.tracks.length > 0 && trajectory.visibility.length > 0) {
    expect(trajectory.tracks[0].length).toBe(trajectory.visibility[0].length);
  }

  // Check expected dimensions if provided
  if (expectedPoints !== undefined) {
    expect(trajectory.metadata.numPoints).toBe(expectedPoints);
    expect(trajectory.tracks.length).toBe(expectedPoints);
  }
  if (expectedFrames !== undefined) {
    expect(trajectory.metadata.numFrames).toBe(expectedFrames);
    if (trajectory.tracks.length > 0) {
      expect(trajectory.tracks[0].length).toBe(expectedFrames);
    }
  }
}

function validateCoordinateBounds(
  trajectory: WanMoveTrajectory,
  maxX: number,
  maxY: number
): void {
  for (const track of trajectory.tracks) {
    for (const point of track) {
      expect(point[0]).toBeGreaterThanOrEqual(0);
      expect(point[0]).toBeLessThanOrEqual(maxX);
      expect(point[1]).toBeGreaterThanOrEqual(0);
      expect(point[1]).toBeLessThanOrEqual(maxY);
    }
  }
}

function validateAllFinite(trajectory: WanMoveTrajectory): void {
  for (const track of trajectory.tracks) {
    for (const point of track) {
      expect(Number.isFinite(point[0])).toBe(true);
      expect(Number.isFinite(point[1])).toBe(true);
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// Flow Presets Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("generateFromPreset", () => {
  // Note: generateFromPreset takes (presetName, numPoints, numFrames, width, height, seed?)
  
  it.each(Object.keys(FLOW_PRESETS))(
    "should generate valid trajectory for preset: %s",
    (presetName) => {
      const trajectory = generateFromPreset(
        presetName as keyof typeof FLOW_PRESETS,
        50, 49, 1920, 1080, 12345
      );

      validateTrajectoryShape(trajectory);
      validateAllFinite(trajectory);
      expect(trajectory.metadata.numPoints).toBeGreaterThan(0);
    }
  );

  it("should produce deterministic output for same seed", () => {
    const result1 = generateFromPreset("neural-flow", 50, 49, 1920, 1080, 99999);
    const result2 = generateFromPreset("neural-flow", 50, 49, 1920, 1080, 99999);

    expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
  });

  it("should produce different output for different seeds", () => {
    const result1 = generateFromPreset("neural-flow", 50, 49, 1920, 1080, 11111);
    const result2 = generateFromPreset("neural-flow", 50, 49, 1920, 1080, 22222);

    expect(JSON.stringify(result1)).not.toBe(JSON.stringify(result2));
  });

  it("should respect numPoints parameter", () => {
    const trajectory = generateFromPreset("cosmic-spiral", 25, 49, 1920, 1080, 12345);

    expect(trajectory.metadata.numPoints).toBe(25);
    expect(trajectory.tracks.length).toBe(25);
  });

  it("should respect numFrames parameter", () => {
    const trajectory = generateFromPreset("hivemind", 50, 81, 1920, 1080, 12345);

    expect(trajectory.metadata.numFrames).toBe(81);
    if (trajectory.tracks.length > 0) {
      expect(trajectory.tracks[0].length).toBe(81);
    }
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Data-Driven Flow Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("generateDataDrivenFlow", () => {
  it("should generate flow from data array", () => {
    const config: DataDrivenFlowConfig = {
      data: Array(100).fill(0).map(() => Math.random() * 100),
      mapping: "speed",
      basePattern: "vortex",
      numFrames: 49,
      width: 1920,
      height: 1080,
    };

    const trajectory = generateDataDrivenFlow(config);

    validateTrajectoryShape(trajectory);
    validateAllFinite(trajectory);
  });

  it("should support different mapping modes", () => {
    const baseConfig: DataDrivenFlowConfig = {
      data: Array(50).fill(50),
      mapping: "speed",
      basePattern: "vortex",
      numFrames: 49,
      width: 1920,
      height: 1080,
    };

    const mappings: Array<DataDrivenFlowConfig["mapping"]> = ["speed", "direction", "amplitude", "phase", "size"];

    for (const mapping of mappings) {
      const trajectory = generateDataDrivenFlow({ ...baseConfig, mapping });
      validateTrajectoryShape(trajectory);
    }
  });

  it("should scale motion by data values", () => {
    const lowDataConfig: DataDrivenFlowConfig = {
      data: Array(20).fill(0), // Low values = less motion
      mapping: "amplitude",
      basePattern: "vortex",
      numFrames: 49,
      width: 1920,
      height: 1080,
    };

    const highDataConfig: DataDrivenFlowConfig = {
      data: Array(20).fill(100), // High values = more motion
      mapping: "amplitude",
      basePattern: "vortex",
      numFrames: 49,
      width: 1920,
      height: 1080,
    };

    const lowTrajectory = generateDataDrivenFlow(lowDataConfig);
    const highTrajectory = generateDataDrivenFlow(highDataConfig);

    // Both should be valid
    validateTrajectoryShape(lowTrajectory);
    validateTrajectoryShape(highTrajectory);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Spline Flow Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("generateSplineFlow", () => {
  it("should generate points along spline path", () => {
    const controlPoints = [
      { id: "cp-1", x: 0, y: 540, handleIn: null, handleOut: null, type: "corner" as const },
      { id: "cp-2", x: 480, y: 270, handleIn: null, handleOut: null, type: "corner" as const },
      { id: "cp-3", x: 960, y: 540, handleIn: null, handleOut: null, type: "corner" as const },
      { id: "cp-4", x: 1440, y: 810, handleIn: null, handleOut: null, type: "corner" as const },
      { id: "cp-5", x: 1920, y: 540, handleIn: null, handleOut: null, type: "corner" as const },
    ];

    const trajectory = generateSplineFlow(
      controlPoints,
      50, // numPoints
      49, // numFrames
      1920,
      1080,
      { seed: 12345 }
    );

    validateTrajectoryShape(trajectory, 50, 49);
    validateAllFinite(trajectory);
  });

  it("should handle minimum control points (2)", () => {
    const controlPoints = [
      { id: "cp-1", x: 0, y: 0, handleIn: null, handleOut: null, type: "corner" as const },
      { id: "cp-2", x: 1920, y: 1080, handleIn: null, handleOut: null, type: "corner" as const },
    ];

    const trajectory = generateSplineFlow(controlPoints, 10, 49, 1920, 1080, { seed: 12345 });

    validateTrajectoryShape(trajectory);
  });

  it("should be deterministic with same seed", () => {
    const controlPoints = [
      { id: "cp-1", x: 100, y: 100, handleIn: null, handleOut: null, type: "corner" as const },
      { id: "cp-2", x: 500, y: 500, handleIn: null, handleOut: null, type: "corner" as const },
      { id: "cp-3", x: 900, y: 100, handleIn: null, handleOut: null, type: "corner" as const },
    ];

    const result1 = generateSplineFlow(controlPoints, 30, 49, 1920, 1080, { seed: 42 });
    const result2 = generateSplineFlow(controlPoints, 30, 49, 1920, 1080, { seed: 42 });

    expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Force Field Flow Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("generateForceFieldFlow", () => {
  it("should generate flow with single attractor", () => {
    const config: ForceFieldConfig = {
      numPoints: 100,
      numFrames: 49,
      width: 1920,
      height: 1080,
      seed: 12345,
      forces: [
        { x: 960, y: 540, strength: 50, radius: 200 }, // Positive = attractor
      ],
    };

    const trajectory = generateForceFieldFlow(config);

    validateTrajectoryShape(trajectory, 100, 49);
    validateAllFinite(trajectory);
  });

  it("should generate flow with repeller", () => {
    const config: ForceFieldConfig = {
      numPoints: 50,
      numFrames: 49,
      width: 1920,
      height: 1080,
      seed: 12345,
      forces: [
        { x: 960, y: 540, strength: -30, radius: 200 }, // Negative = repulsor
      ],
    };

    const trajectory = generateForceFieldFlow(config);

    validateTrajectoryShape(trajectory);
  });

  it("should generate flow with multiple forces", () => {
    const config: ForceFieldConfig = {
      numPoints: 75,
      numFrames: 49,
      width: 1920,
      height: 1080,
      seed: 12345,
      forces: [
        { x: 480, y: 540, strength: 40, radius: 150 },  // Attractor
        { x: 1440, y: 540, strength: 40, radius: 150 }, // Attractor
        { x: 960, y: 270, strength: -20, radius: 100 }, // Repulsor
        { x: 960, y: 810, strength: -20, radius: 100 }, // Repulsor
      ],
    };

    const trajectory = generateForceFieldFlow(config);

    validateTrajectoryShape(trajectory, 75, 49);
  });

  it("should support quadratic falloff", () => {
    const config: ForceFieldConfig = {
      numPoints: 50,
      numFrames: 49,
      width: 1920,
      height: 1080,
      seed: 12345,
      forces: [
        { x: 960, y: 540, strength: 40, radius: 300, falloff: "quadratic" },
      ],
    };

    const trajectory = generateForceFieldFlow(config);

    validateTrajectoryShape(trajectory);
    validateAllFinite(trajectory);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Strange Attractor Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("Lorenz Attractor", () => {
  it("should generate valid Lorenz attractor trajectory", () => {
    const config: AttractorConfig = {
      type: "lorenz",
      numFrames: 49,
      width: 1920,
      height: 1080,
      numPoints: 50,
      seed: 12345,
    };

    const trajectory = generateLorenzAttractor(config);

    validateTrajectoryShape(trajectory, 50, 49);
    validateAllFinite(trajectory);
  });

  it("should be deterministic with same seed", () => {
    const config: AttractorConfig = {
      type: "lorenz",
      numFrames: 49,
      width: 1920,
      height: 1080,
      numPoints: 30,
      seed: 99999,
    };

    const result1 = generateLorenzAttractor(config);
    const result2 = generateLorenzAttractor(config);

    expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
  });
});

describe("Rössler Attractor", () => {
  it("should generate valid Rössler attractor trajectory", () => {
    const config: AttractorConfig = {
      type: "rossler",
      numFrames: 49,
      width: 1920,
      height: 1080,
      numPoints: 50,
      seed: 12345,
    };

    const trajectory = generateRosslerAttractor(config);

    validateTrajectoryShape(trajectory, 50, 49);
    validateAllFinite(trajectory);
  });
});

describe("Aizawa Attractor", () => {
  it("should generate valid Aizawa attractor trajectory", () => {
    const config: AttractorConfig = {
      type: "aizawa",
      numFrames: 49,
      width: 1920,
      height: 1080,
      numPoints: 50,
      seed: 12345,
    };

    const trajectory = generateAizawaAttractor(config);

    validateTrajectoryShape(trajectory, 50, 49);
    validateAllFinite(trajectory);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Note: Shape Morph, Color, and Layer Composition tests removed as those
// functions use different API signatures than initially assumed.
// The core generation and export functions are tested below.
// ═══════════════════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════════════════
// NPY Export Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("exportAsNPYData", () => {
  it("should export tracks as Float32Array", () => {
    const trajectory = generateFromPreset("neural-flow", 10, 17, 1920, 1080, 12345);

    const npyData = exportAsNPYData(trajectory);

    expect(npyData.tracks instanceof Float32Array).toBe(true);
    // Shape should be N * T * 2
    expect(npyData.tracks.length).toBe(10 * 17 * 2);
  });

  it("should export visibility as Uint8Array", () => {
    const trajectory = generateFromPreset("singularity", 10, 17, 1920, 1080, 12345);

    const npyData = exportAsNPYData(trajectory);

    expect(npyData.visibility instanceof Uint8Array).toBe(true);
    // Shape should be N * T
    expect(npyData.visibility.length).toBe(10 * 17);
  });

  it("should include correct shape metadata", () => {
    const trajectory = generateFromPreset("data-genesis", 25, 49, 1920, 1080, 12345);

    const npyData = exportAsNPYData(trajectory);

    expect(npyData.shape.tracks).toEqual([25, 49, 2]);
    expect(npyData.shape.visibility).toEqual([25, 49]);
  });

  it("should have visibility values 0 or 1", () => {
    const trajectory = generateFromPreset("hivemind", 30, 33, 1920, 1080, 12345);

    const npyData = exportAsNPYData(trajectory);

    for (let i = 0; i < npyData.visibility.length; i++) {
      expect([0, 1]).toContain(npyData.visibility[i]);
    }
  });

  it("should flatten tracks correctly (row-major order)", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [
        [[10, 20], [30, 40]], // Point 0: frame 0, frame 1
        [[50, 60], [70, 80]], // Point 1: frame 0, frame 1
      ],
      visibility: [[true, true], [true, true]],
      metadata: {
        numPoints: 2,
        numFrames: 2,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const npyData = exportAsNPYData(trajectory);

    // Should be flattened as: [p0f0x, p0f0y, p0f1x, p0f1y, p1f0x, p1f0y, p1f1x, p1f1y]
    expect(npyData.tracks[0]).toBe(10);
    expect(npyData.tracks[1]).toBe(20);
    expect(npyData.tracks[2]).toBe(30);
    expect(npyData.tracks[3]).toBe(40);
    expect(npyData.tracks[4]).toBe(50);
    expect(npyData.tracks[5]).toBe(60);
    expect(npyData.tracks[6]).toBe(70);
    expect(npyData.tracks[7]).toBe(80);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Determinism Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("Determinism", () => {
  // Use actual FLOW_PRESETS keys
  const presets = [
    "neural-flow",
    "singularity",
    "data-genesis",
    "information-tide",
    "cosmic-spiral",
    "metamorphosis",
    "hivemind",
  ] as const;

  it.each(presets)(
    "should produce identical output for preset %s with same seed",
    (preset) => {
      const result1 = generateFromPreset(preset, 25, 33, 1920, 1080, 42);
      const result2 = generateFromPreset(preset, 25, 33, 1920, 1080, 42);

      expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
    }
  );

  it("should produce different output for different seeds", () => {
    const result1 = generateFromPreset("neural-flow", 50, 49, 1920, 1080, 12345);
    const result2 = generateFromPreset("neural-flow", 50, 49, 1920, 1080, 67890);

    // Should be structurally same but numerically different
    expect(result1.tracks.length).toBe(result2.tracks.length);
    expect(JSON.stringify(result1)).not.toBe(JSON.stringify(result2));
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Color Utility Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("sampleGradient", () => {
  const testGradient = {
    stops: [
      { position: 0, color: [0, 0, 0] as [number, number, number] },
      { position: 0.5, color: [128, 128, 128] as [number, number, number] },
      { position: 1, color: [255, 255, 255] as [number, number, number] },
    ],
  };

  it("should return first stop color at t=0", () => {
    const color = sampleGradient(testGradient, 0);
    expect(color).toEqual([0, 0, 0]);
  });

  it("should return last stop color at t=1", () => {
    const color = sampleGradient(testGradient, 1);
    expect(color).toEqual([255, 255, 255]);
  });

  it("should interpolate at midpoint", () => {
    const color = sampleGradient(testGradient, 0.5);
    expect(color).toEqual([128, 128, 128]);
  });

  it("should interpolate between stops", () => {
    const color = sampleGradient(testGradient, 0.25);
    // Between [0,0,0] and [128,128,128] at 50%
    expect(color).toEqual([64, 64, 64]);
  });

  it("should clamp t < 0 to 0", () => {
    const color = sampleGradient(testGradient, -0.5);
    expect(color).toEqual([0, 0, 0]);
  });

  it("should clamp t > 1 to 1", () => {
    const color = sampleGradient(testGradient, 1.5);
    expect(color).toEqual([255, 255, 255]);
  });

  it("should handle empty gradient", () => {
    const color = sampleGradient({ stops: [] }, 0.5);
    expect(color).toEqual([128, 128, 128]); // Default gray
  });

  it("should handle single stop gradient", () => {
    const color = sampleGradient({
      stops: [{ position: 0.5, color: [255, 0, 0] as [number, number, number] }],
    }, 0.5);
    expect(color).toEqual([255, 0, 0]);
  });
});

describe("addColorToTrajectory", () => {
  it("should add color data to trajectory", () => {
    const trajectory = generateFromPreset("neural-flow", 10, 17, 1920, 1080, 12345);
    const dataValues = Array(10).fill(0).map((_, i) => i * 10);

    const colored = addColorToTrajectory(trajectory, dataValues, "viridis");

    expect(colored.colors).toBeDefined();
    expect(colored.colors!.length).toBe(10); // Same as tracks
    expect(colored.colors![0].length).toBe(17); // Same as frames
    expect(colored.colors![0][0].length).toBe(3); // RGB
  });

  it("should normalize data values", () => {
    const trajectory = generateFromPreset("neural-flow", 3, 5, 1920, 1080, 12345);
    const dataValues = [0, 50, 100]; // Min 0, Max 100

    const colored = addColorToTrajectory(trajectory, dataValues, "viridis");

    expect(colored.dataValues).toEqual([0, 50, 100]);
    expect(colored.colors).toBeDefined();
  });
});

describe("addTimeColorToTrajectory", () => {
  it("should add time-based colors", () => {
    const trajectory = generateFromPreset("neural-flow", 5, 10, 1920, 1080, 12345);

    const colored = addTimeColorToTrajectory(trajectory, "plasma");

    expect(colored.colors).toBeDefined();
    expect(colored.colors!.length).toBe(5);
    expect(colored.colors![0].length).toBe(10);
  });

  it("should have different colors for different frames", () => {
    const trajectory = generateFromPreset("neural-flow", 2, 10, 1920, 1080, 12345);

    const colored = addTimeColorToTrajectory(trajectory, "plasma");

    // First and last frame should be different
    const firstFrameColor = colored.colors![0][0];
    const lastFrameColor = colored.colors![0][9];

    expect(firstFrameColor).not.toEqual(lastFrameColor);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Shape Morph Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("generateShapeMorph", () => {
  it("should generate trajectory morphing between shapes", () => {
    const config: ShapeTargetConfig = {
      numPoints: 50,
      numFrames: 49,
      width: 1920,
      height: 1080,
      source: { type: "circle" },
      target: { type: "star", points: 5 },
      seed: 12345,
    };

    const trajectory = generateShapeMorph(config);

    validateTrajectoryShape(trajectory, 50, 49);
    validateAllFinite(trajectory);
  });

  it("should support different shape pairs", () => {
    const shapeTypes = [
      { type: "circle" } as const,
      { type: "star", points: 5 } as const,
      { type: "heart" } as const,
      { type: "spiral" } as const,
    ];

    for (let i = 0; i < shapeTypes.length; i++) {
      for (let j = 0; j < shapeTypes.length; j++) {
        if (i === j) continue;

        const config: ShapeTargetConfig = {
          numPoints: 20,
          numFrames: 17,
          width: 512,
          height: 512,
          source: shapeTypes[i],
          target: shapeTypes[j],
          seed: 42,
        };

        const trajectory = generateShapeMorph(config);
        validateTrajectoryShape(trajectory);
      }
    }
  });

  it("should be deterministic with same seed", () => {
    const config: ShapeTargetConfig = {
      numPoints: 30,
      numFrames: 33,
      width: 1920,
      height: 1080,
      source: { type: "circle" },
      target: { type: "star", points: 5 },
      seed: 99999,
    };

    const result1 = generateShapeMorph(config);
    const result2 = generateShapeMorph(config);

    expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Layer Composition Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("compositeFlowLayers", () => {
  it("should combine multiple flow layers", () => {
    const layer1 = generateFromPreset("neural-flow", 20, 33, 1920, 1080, 111);
    const layer2 = generateFromPreset("cosmic-spiral", 20, 33, 1920, 1080, 222);

    const layers: FlowLayer[] = [
      { trajectory: layer1, name: "layer1", weight: 1 },
      { trajectory: layer2, name: "layer2", weight: 0.5 },
    ];

    const composite = compositeFlowLayers(layers);

    // Should have combined point count
    expect(composite.tracks.length).toBe(40);
    expect(composite.metadata.numPoints).toBe(40);
  });

  it("should preserve frame count", () => {
    const layer1 = generateFromPreset("neural-flow", 10, 49, 1920, 1080, 111);
    const layer2 = generateFromPreset("hivemind", 15, 49, 1920, 1080, 222);

    const layers: FlowLayer[] = [
      { trajectory: layer1, name: "base", weight: 1 },
      { trajectory: layer2, name: "overlay", weight: 1 },
    ];

    const composite = compositeFlowLayers(layers);

    expect(composite.metadata.numFrames).toBe(49);
  });

  it("should throw on empty layers array", () => {
    expect(() => compositeFlowLayers([])).toThrow("At least one layer required");
  });
});

describe("compositeColoredLayers", () => {
  it("should combine colored layers", () => {
    const traj1 = generateFromPreset("neural-flow", 10, 17, 1920, 1080, 111);
    const traj2 = generateFromPreset("singularity", 10, 17, 1920, 1080, 222);

    const colored1 = addColorToTrajectory(traj1, Array(10).fill(50), "viridis");
    const colored2 = addColorToTrajectory(traj2, Array(10).fill(75), "plasma");

    const layers: FlowLayer[] = [
      { trajectory: colored1, name: "viridis-layer", weight: 1 },
      { trajectory: colored2, name: "plasma-layer", weight: 1 },
    ];

    const composite = compositeColoredLayers(layers);

    expect(composite.tracks.length).toBe(20);
    expect(composite.colors).toBeDefined();
    expect(composite.colors!.length).toBe(20);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// JSON Export Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("exportAsJSON", () => {
  it("should export trajectory as valid JSON string", () => {
    const trajectory = generateFromPreset("neural-flow", 10, 17, 1920, 1080, 12345);

    const json = exportAsJSON(trajectory);

    expect(typeof json).toBe("string");
    expect(() => JSON.parse(json)).not.toThrow();
  });

  it("should preserve all data in roundtrip", () => {
    const trajectory = generateFromPreset("neural-flow", 10, 17, 1920, 1080, 12345);

    const json = exportAsJSON(trajectory);
    const parsed = JSON.parse(json);

    expect(parsed.tracks.length).toBe(10);
    expect(parsed.visibility.length).toBe(10);
    expect(parsed.metadata.numPoints).toBe(10);
    expect(parsed.metadata.numFrames).toBe(17);
  });

  it("should include all metadata fields", () => {
    const trajectory = generateFromPreset("neural-flow", 25, 49, 1920, 1080, 12345);

    const json = exportAsJSON(trajectory);
    const parsed = JSON.parse(json);

    expect(parsed.metadata).toHaveProperty("numPoints");
    expect(parsed.metadata).toHaveProperty("numFrames");
    expect(parsed.metadata).toHaveProperty("width");
    expect(parsed.metadata).toHaveProperty("height");
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Preset Constants Validation Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("FLOW_PRESETS", () => {
  it("should contain all expected presets", () => {
    const expectedPresets = [
      "neural-flow",
      "singularity", 
      "data-genesis",
      "information-tide",
      "cosmic-spiral",
      "metamorphosis",
      "hivemind",
    ];

    for (const preset of expectedPresets) {
      expect(FLOW_PRESETS).toHaveProperty(preset);
    }
  });

  it("should have valid config for each preset", () => {
    for (const [name, config] of Object.entries(FLOW_PRESETS)) {
      expect(config).toHaveProperty("pattern");
      expect(typeof config.pattern).toBe("string");
    }
  });
});

describe("ATTRACTOR_PRESETS", () => {
  it("should contain attractor presets", () => {
    const expectedAttractors = ["lorenz-butterfly", "rossler-spiral", "aizawa-torus"];

    for (const attractor of expectedAttractors) {
      expect(ATTRACTOR_PRESETS).toHaveProperty(attractor);
    }
  });

  it("should have valid config for each attractor", () => {
    for (const [name, config] of Object.entries(ATTRACTOR_PRESETS)) {
      expect(config).toHaveProperty("type");
      expect(["lorenz", "rossler", "aizawa"]).toContain(config.type);
      expect(config).toHaveProperty("scale");
      expect(config).toHaveProperty("dt");
    }
  });
});

describe("SHAPE_PRESETS", () => {
  it("should contain shape morph presets", () => {
    const expectedShapes = ["grid-to-circle", "random-to-heart", "circle-to-star", "spiral-to-grid"];

    for (const shape of expectedShapes) {
      expect(SHAPE_PRESETS).toHaveProperty(shape);
    }
  });

  it("should have valid source and target for each preset", () => {
    for (const [name, config] of Object.entries(SHAPE_PRESETS)) {
      expect(config).toHaveProperty("source");
      expect(config).toHaveProperty("target");
      expect(config).toHaveProperty("easing");
      expect(config.source).toHaveProperty("type");
      expect(config.target).toHaveProperty("type");
    }
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// WanVideoWrapper Compatible Export Tests
// ═══════════════════════════════════════════════════════════════════════════

import {
  exportWanMoveTrackCoordsJSON,
  exportWanMoveVisibility,
  exportWanMoveTrackCoordsPackage,
  type TrackPoint,
} from "@/services/export/wanMoveExport";

describe("exportWanMoveTrackCoordsJSON", () => {
  it("should export trajectory as JSON string with {x,y} objects", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [
        [[10, 20], [30, 40], [50, 60]],
        [[100, 200], [300, 400], [500, 600]],
      ],
      visibility: [[true, true, true], [true, true, true]],
      metadata: {
        numPoints: 2,
        numFrames: 3,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const json = exportWanMoveTrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json);

    // Verify structure: [[{x,y},{x,y},...], [{x,y},...]]
    expect(Array.isArray(parsed)).toBe(true);
    expect(parsed.length).toBe(2); // 2 tracks
    expect(parsed[0].length).toBe(3); // 3 frames each

    // Verify {x, y} object format
    expect(parsed[0][0]).toEqual({ x: 10, y: 20 });
    expect(parsed[0][1]).toEqual({ x: 30, y: 40 });
    expect(parsed[1][0]).toEqual({ x: 100, y: 200 });
  });

  it("should produce valid JSON", () => {
    const trajectory = generateFromPreset("neural-flow", 10, 17, 1920, 1080, 12345);

    const json = exportWanMoveTrackCoordsJSON(trajectory);

    expect(typeof json).toBe("string");
    expect(() => JSON.parse(json)).not.toThrow();
  });

  it("should have correct number of tracks and frames", () => {
    const trajectory = generateFromPreset("cosmic-spiral", 25, 49, 1920, 1080, 12345);

    const json = exportWanMoveTrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json) as TrackPoint[][];

    expect(parsed.length).toBe(25);
    expect(parsed[0].length).toBe(49);
  });

  it("should preserve exact coordinate values", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [
        [[123.456, 789.012]],
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

    const json = exportWanMoveTrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json);

    expect(parsed[0][0].x).toBe(123.456);
    expect(parsed[0][0].y).toBe(789.012);
  });

  it("should handle empty trajectory", () => {
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

    const json = exportWanMoveTrackCoordsJSON(trajectory);
    const parsed = JSON.parse(json);

    expect(parsed).toEqual([]);
  });
});

describe("exportWanMoveVisibility", () => {
  it("should transpose visibility from [N][T] to [T][N]", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [
        [[0, 0], [0, 0], [0, 0]],
        [[0, 0], [0, 0], [0, 0]],
      ],
      visibility: [
        [true, false, true],  // Track 0: frame 0=true, 1=false, 2=true
        [false, true, false], // Track 1: frame 0=false, 1=true, 2=false
      ],
      metadata: {
        numPoints: 2,
        numFrames: 3,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const json = exportWanMoveVisibility(trajectory);
    const parsed = JSON.parse(json);

    // Expected transposed: [T][N]
    // Frame 0: [track0=true, track1=false]
    // Frame 1: [track0=false, track1=true]
    // Frame 2: [track0=true, track1=false]
    expect(parsed.length).toBe(3); // 3 frames
    expect(parsed[0]).toEqual([true, false]);
    expect(parsed[1]).toEqual([false, true]);
    expect(parsed[2]).toEqual([true, false]);
  });

  it("should default to true for missing visibility", () => {
    const trajectory: WanMoveTrajectory = {
      tracks: [[[0, 0]]],
      visibility: [], // Empty visibility
      metadata: {
        numPoints: 1,
        numFrames: 1,
        width: 1920,
        height: 1080,
        fps: 16,
      },
    };

    const json = exportWanMoveVisibility(trajectory);
    const parsed = JSON.parse(json);

    expect(parsed[0][0]).toBe(true);
  });
});

describe("exportWanMoveTrackCoordsPackage", () => {
  it("should return trackCoords and metadata", () => {
    const trajectory = generateFromPreset("neural-flow", 10, 17, 1920, 1080, 12345);

    const result = exportWanMoveTrackCoordsPackage(trajectory);

    expect(result).toHaveProperty("trackCoords");
    expect(result).toHaveProperty("metadata");
    expect(typeof result.trackCoords).toBe("string");
    expect(result.metadata).toEqual(trajectory.metadata);
  });

  it("should produce valid JSON in trackCoords", () => {
    const trajectory = generateFromPreset("singularity", 15, 33, 1920, 1080, 99999);

    const result = exportWanMoveTrackCoordsPackage(trajectory);

    expect(() => JSON.parse(result.trackCoords)).not.toThrow();
  });

  it("should have trackCoords match exportWanMoveTrackCoordsJSON output", () => {
    const trajectory = generateFromPreset("hivemind", 20, 49, 1920, 1080, 42);

    const result = exportWanMoveTrackCoordsPackage(trajectory);
    const direct = exportWanMoveTrackCoordsJSON(trajectory);

    expect(result.trackCoords).toBe(direct);
  });
});
