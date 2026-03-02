/**
 * Property tests for ui/src/services/export/wanMoveExport.ts
 * Tests: exportAsJSON, exportAsNPYData, sampleGradient, addColorToTrajectory,
 *        addTimeColorToTrajectory, generateLorenzAttractor, generateRosslerAttractor,
 *        generateAizawaAttractor, compositeFlowLayers
 * 
 * Audit: 2026-01-06
 * 
 * CRITICAL: These tests verify Wan-Move format compatibility for AI video generation
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  exportAsJSON,
  exportAsNPYData,
  sampleGradient,
  addColorToTrajectory,
  addTimeColorToTrajectory,
  generateLorenzAttractor,
  generateRosslerAttractor,
  generateAizawaAttractor,
  compositeFlowLayers,
  COLOR_GRADIENTS,
  type WanMoveTrajectory,
  type ColorGradient,
  type AttractorConfig,
  type FlowLayer,
} from "@/services/export/wanMoveExport";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // test // fixtures
// ════════════════════════════════════════════════════════════════════════════

function createTestTrajectory(numPoints: number, numFrames: number, width = 512, height = 512): WanMoveTrajectory {
  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];
  
  for (let i = 0; i < numPoints; i++) {
    const track: number[][] = [];
    const vis: boolean[] = [];
    for (let f = 0; f < numFrames; f++) {
      // Simple linear motion for testing
      track.push([
        (i * 50 + f * 2) % width,
        (i * 30 + f * 3) % height,
      ]);
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

// ════════════════════════════════════════════════════════════════════════════
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

const trajectoryArb = fc.record({
  numPoints: fc.integer({ min: 1, max: 20 }),
  numFrames: fc.integer({ min: 1, max: 50 }),
  width: fc.integer({ min: 64, max: 1024 }),
  height: fc.integer({ min: 64, max: 1024 }),
}).map(({ numPoints, numFrames, width, height }) => 
  createTestTrajectory(numPoints, numFrames, width, height)
);

const gradientNameArb = fc.constantFrom(
  "viridis", "plasma", "inferno", "cool-warm", "rainbow", "depth"
) as fc.Arbitrary<keyof typeof COLOR_GRADIENTS>;

// ════════════════════════════════════════════════════════════════════════════
// exportAsJSON TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: exportAsJSON", () => {
  it("returns valid JSON string", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const json = exportAsJSON(trajectory);
        expect(() => JSON.parse(json)).not.toThrow();
      })
    );
  });

  it("JSON contains tracks, visibility, and metadata", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const json = exportAsJSON(trajectory);
        const parsed = JSON.parse(json);
        
        expect(parsed).toHaveProperty("tracks");
        expect(parsed).toHaveProperty("visibility");
        expect(parsed).toHaveProperty("metadata");
      })
    );
  });

  it("tracks array matches original dimensions", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const json = exportAsJSON(trajectory);
        const parsed = JSON.parse(json);
        
        expect(parsed.tracks.length).toBe(trajectory.metadata.numPoints);
        if (trajectory.metadata.numPoints > 0) {
          expect(parsed.tracks[0].length).toBe(trajectory.metadata.numFrames);
          if (trajectory.metadata.numFrames > 0) {
            expect(parsed.tracks[0][0].length).toBe(2); // x, y
          }
        }
      })
    );
  });

  it("visibility array matches original dimensions", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const json = exportAsJSON(trajectory);
        const parsed = JSON.parse(json);
        
        expect(parsed.visibility.length).toBe(trajectory.metadata.numPoints);
        if (trajectory.metadata.numPoints > 0) {
          expect(parsed.visibility[0].length).toBe(trajectory.metadata.numFrames);
        }
      })
    );
  });

  it("is deterministic (same input → same output)", () => {
    const trajectory = createTestTrajectory(5, 10);
    const json1 = exportAsJSON(trajectory);
    const json2 = exportAsJSON(trajectory);
    expect(json1).toBe(json2);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// exportAsNPYData TESTS - CRITICAL FOR ML MODEL COMPATIBILITY
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: exportAsNPYData", () => {
  it("returns Float32Array for tracks", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const result = exportAsNPYData(trajectory);
        expect(result.tracks).toBeInstanceOf(Float32Array);
      })
    );
  });

  it("returns Uint8Array for visibility", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const result = exportAsNPYData(trajectory);
        expect(result.visibility).toBeInstanceOf(Uint8Array);
      })
    );
  });

  it("tracks shape is [N, T, 2]", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const result = exportAsNPYData(trajectory);
        const { numPoints, numFrames } = trajectory.metadata;
        
        expect(result.shape.tracks).toEqual([numPoints, numFrames, 2]);
      })
    );
  });

  it("visibility shape is [N, T]", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const result = exportAsNPYData(trajectory);
        const { numPoints, numFrames } = trajectory.metadata;
        
        expect(result.shape.visibility).toEqual([numPoints, numFrames]);
      })
    );
  });

  it("tracks array has correct length (N * T * 2)", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const result = exportAsNPYData(trajectory);
        const { numPoints, numFrames } = trajectory.metadata;
        
        expect(result.tracks.length).toBe(numPoints * numFrames * 2);
      })
    );
  });

  it("visibility array has correct length (N * T)", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const result = exportAsNPYData(trajectory);
        const { numPoints, numFrames } = trajectory.metadata;
        
        expect(result.visibility.length).toBe(numPoints * numFrames);
      })
    );
  });

  it("visibility values are 0 or 1", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const result = exportAsNPYData(trajectory);
        
        for (let i = 0; i < result.visibility.length; i++) {
          expect(result.visibility[i]).toBeGreaterThanOrEqual(0);
          expect(result.visibility[i]).toBeLessThanOrEqual(1);
        }
      })
    );
  });

  it("flattened tracks preserve coordinate order (x, y)", () => {
    const trajectory = createTestTrajectory(2, 3);
    // Set known values
    trajectory.tracks[0][0] = [100, 200];
    trajectory.tracks[0][1] = [101, 201];
    
    const result = exportAsNPYData(trajectory);
    
    // First point, first frame: x=100, y=200
    expect(result.tracks[0]).toBe(100);
    expect(result.tracks[1]).toBe(200);
    // First point, second frame: x=101, y=201
    expect(result.tracks[2]).toBe(101);
    expect(result.tracks[3]).toBe(201);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// sampleGradient TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: sampleGradient", () => {
  it("returns array of 3 integers (RGB)", () => {
    fc.assert(
      fc.property(
        gradientNameArb,
        fc.double({ min: 0, max: 1, noNaN: true }),
        (gradientName, t) => {
          const color = sampleGradient(COLOR_GRADIENTS[gradientName], t);
          
          expect(color.length).toBe(3);
          expect(Number.isInteger(color[0])).toBe(true);
          expect(Number.isInteger(color[1])).toBe(true);
          expect(Number.isInteger(color[2])).toBe(true);
        }
      )
    );
  });

  it("RGB values are in range 0-255", () => {
    fc.assert(
      fc.property(
        gradientNameArb,
        fc.double({ min: 0, max: 1, noNaN: true }),
        (gradientName, t) => {
          const color = sampleGradient(COLOR_GRADIENTS[gradientName], t);
          
          expect(color[0]).toBeGreaterThanOrEqual(0);
          expect(color[0]).toBeLessThanOrEqual(255);
          expect(color[1]).toBeGreaterThanOrEqual(0);
          expect(color[1]).toBeLessThanOrEqual(255);
          expect(color[2]).toBeGreaterThanOrEqual(0);
          expect(color[2]).toBeLessThanOrEqual(255);
        }
      )
    );
  });

  it("clamps t to [0, 1] range", () => {
    fc.assert(
      fc.property(
        gradientNameArb,
        fc.double({ min: -10, max: 10, noNaN: true }),
        (gradientName, t) => {
          const gradient = COLOR_GRADIENTS[gradientName];
          const color = sampleGradient(gradient, t);
          
          // Should not throw and should return valid RGB
          expect(color.length).toBe(3);
        }
      )
    );
  });

  it("t=0 returns first stop color", () => {
    for (const name of Object.keys(COLOR_GRADIENTS)) {
      const gradient = COLOR_GRADIENTS[name as keyof typeof COLOR_GRADIENTS];
      const color = sampleGradient(gradient, 0);
      expect(color).toEqual(gradient.stops[0].color);
    }
  });

  it("t=1 returns last stop color", () => {
    for (const name of Object.keys(COLOR_GRADIENTS)) {
      const gradient = COLOR_GRADIENTS[name as keyof typeof COLOR_GRADIENTS];
      const color = sampleGradient(gradient, 1);
      expect(color).toEqual(gradient.stops[gradient.stops.length - 1].color);
    }
  });

  it("is deterministic", () => {
    const gradient = COLOR_GRADIENTS.viridis;
    const color1 = sampleGradient(gradient, 0.5);
    const color2 = sampleGradient(gradient, 0.5);
    expect(color1).toEqual(color2);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// addColorToTrajectory TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: addColorToTrajectory", () => {
  it("returns ColoredTrajectory with colors array", () => {
    fc.assert(
      fc.property(
        trajectoryArb,
        gradientNameArb,
        (trajectory, gradientName) => {
          const dataValues = Array.from(
            { length: trajectory.metadata.numPoints },
            (_, i) => i / trajectory.metadata.numPoints
          );
          const colored = addColorToTrajectory(trajectory, dataValues, gradientName);
          
          expect(colored.colors).toBeDefined();
          expect(colored.dataValues).toBeDefined();
        }
      )
    );
  });

  it("colors array has correct dimensions [N][T][3]", () => {
    const trajectory = createTestTrajectory(5, 10);
    const dataValues = [0, 0.25, 0.5, 0.75, 1];
    const colored = addColorToTrajectory(trajectory, dataValues);
    
    expect(colored.colors!.length).toBe(5); // N points
    expect(colored.colors![0].length).toBe(10); // T frames
    expect(colored.colors![0][0].length).toBe(3); // RGB
  });

  it("preserves original trajectory data", () => {
    const trajectory = createTestTrajectory(3, 5);
    const dataValues = [0, 0.5, 1];
    const colored = addColorToTrajectory(trajectory, dataValues);
    
    expect(colored.tracks).toEqual(trajectory.tracks);
    expect(colored.visibility).toEqual(trajectory.visibility);
    expect(colored.metadata).toEqual(trajectory.metadata);
  });

  it("each point has same color across all frames", () => {
    const trajectory = createTestTrajectory(3, 5);
    const dataValues = [0, 0.5, 1];
    const colored = addColorToTrajectory(trajectory, dataValues);
    
    for (let i = 0; i < 3; i++) {
      const firstFrameColor = colored.colors![i][0];
      for (let f = 1; f < 5; f++) {
        expect(colored.colors![i][f]).toEqual(firstFrameColor);
      }
    }
  });
});

// ════════════════════════════════════════════════════════════════════════════
// addTimeColorToTrajectory TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: addTimeColorToTrajectory", () => {
  it("returns ColoredTrajectory with colors array", () => {
    fc.assert(
      fc.property(trajectoryArb, (trajectory) => {
        const colored = addTimeColorToTrajectory(trajectory);
        expect(colored.colors).toBeDefined();
      })
    );
  });

  it("colors change across frames (time-based)", () => {
    const trajectory = createTestTrajectory(2, 10);
    const colored = addTimeColorToTrajectory(trajectory);
    
    // First frame and last frame should have different colors
    const firstColor = colored.colors![0][0];
    const lastColor = colored.colors![0][9];
    
    expect(firstColor).not.toEqual(lastColor);
  });

  it("all points at same frame have same color", () => {
    const trajectory = createTestTrajectory(5, 10);
    const colored = addTimeColorToTrajectory(trajectory);
    
    // At frame 5, all points should have the same time-based color
    const colorAtFrame5 = colored.colors![0][5];
    for (let i = 1; i < 5; i++) {
      expect(colored.colors![i][5]).toEqual(colorAtFrame5);
    }
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                        // attractor // tests
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: generateLorenzAttractor", () => {
  it("generates trajectory with correct dimensions", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 20 }),
        fc.integer({ min: 10, max: 100 }),
        fc.integer({ min: 128, max: 512 }),
        fc.integer({ min: 128, max: 512 }),
        (numPoints, numFrames, width, height) => {
          const config: AttractorConfig = {
            type: "lorenz",
            numPoints,
            numFrames,
            width,
            height,
            seed: 42,
          };
          const trajectory = generateLorenzAttractor(config);
          
          expect(trajectory.tracks.length).toBe(numPoints);
          expect(trajectory.visibility.length).toBe(numPoints);
          expect(trajectory.metadata.numPoints).toBe(numPoints);
          expect(trajectory.metadata.numFrames).toBe(numFrames);
        }
      )
    );
  });

  it("is deterministic with same seed", () => {
    const config: AttractorConfig = {
      type: "lorenz",
      numPoints: 5,
      numFrames: 20,
      width: 256,
      height: 256,
      seed: 12345,
    };
    
    const t1 = generateLorenzAttractor(config);
    const t2 = generateLorenzAttractor(config);
    
    expect(t1.tracks).toEqual(t2.tracks);
  });

  it("different seeds produce different trajectories", () => {
    const config1: AttractorConfig = {
      type: "lorenz",
      numPoints: 5,
      numFrames: 20,
      width: 256,
      height: 256,
      seed: 111,
    };
    const config2: AttractorConfig = { ...config1, seed: 222 };
    
    const t1 = generateLorenzAttractor(config1);
    const t2 = generateLorenzAttractor(config2);
    
    // At least some tracks should differ
    expect(t1.tracks).not.toEqual(t2.tracks);
  });

  it("coordinates are within canvas bounds", () => {
    const config: AttractorConfig = {
      type: "lorenz",
      numPoints: 10,
      numFrames: 50,
      width: 256,
      height: 256,
      seed: 42,
    };
    const trajectory = generateLorenzAttractor(config);
    
    for (const track of trajectory.tracks) {
      for (const [x, y] of track) {
        expect(x).toBeGreaterThanOrEqual(0);
        expect(x).toBeLessThanOrEqual(config.width);
        expect(y).toBeGreaterThanOrEqual(0);
        expect(y).toBeLessThanOrEqual(config.height);
      }
    }
  });
});

describe("PROPERTY: generateRosslerAttractor", () => {
  it("generates trajectory with correct dimensions", () => {
    const config: AttractorConfig = {
      type: "rossler",
      numPoints: 5,
      numFrames: 30,
      width: 256,
      height: 256,
      seed: 42,
    };
    const trajectory = generateRosslerAttractor(config);
    
    expect(trajectory.tracks.length).toBe(5);
    expect(trajectory.metadata.numFrames).toBe(30);
  });

  it("is deterministic with same seed", () => {
    const config: AttractorConfig = {
      type: "rossler",
      numPoints: 3,
      numFrames: 20,
      width: 256,
      height: 256,
      seed: 99999,
    };
    
    const t1 = generateRosslerAttractor(config);
    const t2 = generateRosslerAttractor(config);
    
    expect(t1.tracks).toEqual(t2.tracks);
  });
});

describe("PROPERTY: generateAizawaAttractor", () => {
  it("generates trajectory with correct dimensions", () => {
    const config: AttractorConfig = {
      type: "aizawa",
      numPoints: 5,
      numFrames: 30,
      width: 256,
      height: 256,
      seed: 42,
    };
    const trajectory = generateAizawaAttractor(config);
    
    expect(trajectory.tracks.length).toBe(5);
    expect(trajectory.metadata.numFrames).toBe(30);
  });

  it("is deterministic with same seed", () => {
    const config: AttractorConfig = {
      type: "aizawa",
      numPoints: 3,
      numFrames: 20,
      width: 256,
      height: 256,
      seed: 77777,
    };
    
    const t1 = generateAizawaAttractor(config);
    const t2 = generateAizawaAttractor(config);
    
    expect(t1.tracks).toEqual(t2.tracks);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// compositeFlowLayers TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: compositeFlowLayers", () => {
  it("combines multiple trajectories", () => {
    const layer1: FlowLayer = {
      trajectory: createTestTrajectory(3, 10),
      name: "layer1",
      weight: 1,
    };
    const layer2: FlowLayer = {
      trajectory: createTestTrajectory(2, 10),
      name: "layer2",
      weight: 1,
    };

    const composite = compositeFlowLayers([layer1, layer2]);

    // Should have combined points
    expect(composite.tracks.length).toBe(5); // 3 + 2
    expect(composite.metadata.numPoints).toBe(5);
  });

  it("preserves frame count from first layer", () => {
    const layer1: FlowLayer = {
      trajectory: createTestTrajectory(3, 10),
      name: "layer1",
      weight: 1,
    };
    const layer2: FlowLayer = {
      trajectory: createTestTrajectory(2, 10),
      name: "layer2",
      weight: 1,
    };

    const composite = compositeFlowLayers([layer1, layer2]);

    expect(composite.metadata.numFrames).toBe(10);
  });

  it("throws for empty layers array", () => {
    expect(() => compositeFlowLayers([])).toThrow("At least one layer required");
  });

  it("single layer returns same data", () => {
    const trajectory = createTestTrajectory(5, 10);
    const layer: FlowLayer = {
      trajectory,
      name: "solo",
      weight: 1,
    };

    const composite = compositeFlowLayers([layer]);

    expect(composite.tracks.length).toBe(5);
    expect(composite.metadata.numPoints).toBe(5);
  });
});
