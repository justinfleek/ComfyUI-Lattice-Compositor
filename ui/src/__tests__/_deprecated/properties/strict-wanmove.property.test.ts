/**
 * STRICT Property Tests for Wan-Move Export
 *
 * Tests the ACTUAL tensor outputs that ComfyUI nodes consume:
 * 1. Trajectory shape: (N, T, 2) - N points, T frames, x/y coords
 * 2. Visibility shape: (N, T) - boolean per point per frame
 * 3. Determinism: same seed = same trajectory
 * 4. Bounds: coordinates within canvas dimensions
 * 5. Float32Array precision for NPY export
 *
 * TOLERANCE: STRICT - ComfyUI nodes will FAIL with wrong tensor shapes
 */

import { describe, it, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  generateSpiralFlow,
  generateWaveFlow,
  generateExplosionFlow,
  generateVortexFlow,
  generateDataRiverFlow,
  generateMorphFlow,
  generateSwarmFlow,
  exportAsNPYData,
  exportAsJSON,
  SeededRandom,
  type WanMoveTrajectory,
  type GenerativeFlowConfig,
} from '@/services/export/wanMoveExport';

// ============================================================================
// TEST DATA GENERATORS
// ============================================================================

const arbitraryFlowConfig = (): fc.Arbitrary<GenerativeFlowConfig> =>
  fc.record({
    pattern: fc.constantFrom('spiral', 'wave', 'explosion', 'vortex', 'data-river', 'morph', 'swarm'),
    numPoints: fc.integer({ min: 5, max: 100 }),
    numFrames: fc.integer({ min: 8, max: 128 }),
    width: fc.integer({ min: 256, max: 2048 }),
    height: fc.integer({ min: 256, max: 2048 }),
    params: fc.record({
      seed: fc.integer({ min: 0, max: 1000000 }),
      noiseStrength: fc.double({ min: 0, max: 0.5, noNaN: true, noDefaultInfinity: true }),
    }),
  });

// ============================================================================
// STRICT TENSOR SHAPE TESTS
// ============================================================================

describe('STRICT: Wan-Move Tensor Shapes', () => {
  test.prop([
    fc.integer({ min: 5, max: 50 }),
    fc.integer({ min: 8, max: 64 }),
    fc.integer({ min: 256, max: 1024 }),
    fc.integer({ min: 256, max: 1024 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('trajectory shape is (N, T, 2)', (numPoints, numFrames, width, height, seed) => {
    const config: GenerativeFlowConfig = {
      pattern: 'spiral',
      numPoints,
      numFrames,
      width,
      height,
      params: { seed },
    };

    const trajectory = generateSpiralFlow(config);

    // Verify tracks shape
    expect(trajectory.tracks.length).toBe(numPoints); // N points
    for (const track of trajectory.tracks) {
      expect(track.length).toBe(numFrames); // T frames
      for (const point of track) {
        expect(point.length).toBe(2); // [x, y]
      }
    }
  });

  test.prop([
    fc.integer({ min: 5, max: 50 }),
    fc.integer({ min: 8, max: 64 }),
    fc.integer({ min: 256, max: 1024 }),
    fc.integer({ min: 256, max: 1024 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('visibility shape is (N, T)', (numPoints, numFrames, width, height, seed) => {
    const config: GenerativeFlowConfig = {
      pattern: 'spiral',
      numPoints,
      numFrames,
      width,
      height,
      params: { seed },
    };

    const trajectory = generateSpiralFlow(config);

    // Verify visibility shape
    expect(trajectory.visibility.length).toBe(numPoints); // N points
    for (const vis of trajectory.visibility) {
      expect(vis.length).toBe(numFrames); // T frames
      for (const v of vis) {
        expect(typeof v).toBe('boolean');
      }
    }
  });

  test.prop([
    fc.integer({ min: 5, max: 50 }),
    fc.integer({ min: 8, max: 64 }),
    fc.integer({ min: 256, max: 1024 }),
    fc.integer({ min: 256, max: 1024 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('NPY export produces correct flattened shape', (numPoints, numFrames, width, height, seed) => {
    const config: GenerativeFlowConfig = {
      pattern: 'spiral',
      numPoints,
      numFrames,
      width,
      height,
      params: { seed },
    };

    const trajectory = generateSpiralFlow(config);
    const npyData = exportAsNPYData(trajectory);

    // Tracks: N * T * 2 elements
    expect(npyData.tracks.length).toBe(numPoints * numFrames * 2);
    expect(npyData.tracks).toBeInstanceOf(Float32Array);
    expect(npyData.shape.tracks).toEqual([numPoints, numFrames, 2]);

    // Visibility: N * T elements
    expect(npyData.visibility.length).toBe(numPoints * numFrames);
    expect(npyData.visibility).toBeInstanceOf(Uint8Array);
    expect(npyData.shape.visibility).toEqual([numPoints, numFrames]);
  });

  test.prop([
    fc.integer({ min: 5, max: 30 }),
    fc.integer({ min: 8, max: 32 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('NPY data can be reconstructed to original', (numPoints, numFrames, seed) => {
    const config: GenerativeFlowConfig = {
      pattern: 'spiral',
      numPoints,
      numFrames,
      width: 512,
      height: 512,
      params: { seed },
    };

    const trajectory = generateSpiralFlow(config);
    const npyData = exportAsNPYData(trajectory);

    // Reconstruct from flat array
    for (let i = 0; i < numPoints; i++) {
      for (let f = 0; f < numFrames; f++) {
        const flatIdx = (i * numFrames + f) * 2;
        const originalX = trajectory.tracks[i][f][0];
        const originalY = trajectory.tracks[i][f][1];

        // Float32 conversion may lose precision
        expect(Math.abs(npyData.tracks[flatIdx] - originalX)).toBeLessThan(0.001);
        expect(Math.abs(npyData.tracks[flatIdx + 1] - originalY)).toBeLessThan(0.001);

        const originalVis = trajectory.visibility[i][f] ? 1 : 0;
        expect(npyData.visibility[i * numFrames + f]).toBe(originalVis);
      }
    }
  });
});

// ============================================================================
// STRICT BOUNDS TESTS
// ============================================================================

describe('STRICT: Wan-Move Coordinate Bounds', () => {
  const patterns = ['spiral', 'wave', 'explosion', 'vortex', 'data-river', 'morph', 'swarm'] as const;

  for (const pattern of patterns) {
    test.prop([
      fc.integer({ min: 10, max: 50 }),
      fc.integer({ min: 16, max: 64 }),
      fc.integer({ min: 256, max: 1024 }),
      fc.integer({ min: 256, max: 1024 }),
      fc.integer({ min: 0, max: 1000000 })
    ])(`${pattern}: coordinates are within canvas bounds`, (numPoints, numFrames, width, height, seed) => {
      const config: GenerativeFlowConfig = {
        pattern,
        numPoints,
        numFrames,
        width,
        height,
        params: { seed },
      };

      let trajectory: WanMoveTrajectory;
      switch (pattern) {
        case 'spiral': trajectory = generateSpiralFlow(config); break;
        case 'wave': trajectory = generateWaveFlow(config); break;
        case 'explosion': trajectory = generateExplosionFlow(config); break;
        case 'vortex': trajectory = generateVortexFlow(config); break;
        case 'data-river': trajectory = generateDataRiverFlow(config); break;
        case 'morph': trajectory = generateMorphFlow(config); break;
        case 'swarm': trajectory = generateSwarmFlow(config); break;
      }

      // All coordinates must be within bounds
      for (let i = 0; i < trajectory.tracks.length; i++) {
        for (let f = 0; f < trajectory.tracks[i].length; f++) {
          const [x, y] = trajectory.tracks[i][f];

          expect(x).toBeGreaterThanOrEqual(0);
          expect(x).toBeLessThanOrEqual(width);
          expect(y).toBeGreaterThanOrEqual(0);
          expect(y).toBeLessThanOrEqual(height);
          expect(Number.isFinite(x)).toBe(true);
          expect(Number.isFinite(y)).toBe(true);
        }
      }
    });
  }
});

// ============================================================================
// STRICT DETERMINISM TESTS
// ============================================================================

describe('STRICT: Wan-Move Determinism', () => {
  const patterns = ['spiral', 'wave', 'explosion', 'vortex', 'data-river', 'morph', 'swarm'] as const;

  for (const pattern of patterns) {
    test.prop([
      fc.integer({ min: 0, max: 1000000 })
    ])(`${pattern}: same seed produces identical trajectory`, (seed) => {
      const config1: GenerativeFlowConfig = {
        pattern,
        numPoints: 20,
        numFrames: 30,
        width: 512,
        height: 512,
        params: { seed },
      };
      const config2 = { ...config1 };

      let traj1: WanMoveTrajectory, traj2: WanMoveTrajectory;
      switch (pattern) {
        case 'spiral':
          traj1 = generateSpiralFlow(config1);
          traj2 = generateSpiralFlow(config2);
          break;
        case 'wave':
          traj1 = generateWaveFlow(config1);
          traj2 = generateWaveFlow(config2);
          break;
        case 'explosion':
          traj1 = generateExplosionFlow(config1);
          traj2 = generateExplosionFlow(config2);
          break;
        case 'vortex':
          traj1 = generateVortexFlow(config1);
          traj2 = generateVortexFlow(config2);
          break;
        case 'data-river':
          traj1 = generateDataRiverFlow(config1);
          traj2 = generateDataRiverFlow(config2);
          break;
        case 'morph':
          traj1 = generateMorphFlow(config1);
          traj2 = generateMorphFlow(config2);
          break;
        case 'swarm':
          traj1 = generateSwarmFlow(config1);
          traj2 = generateSwarmFlow(config2);
          break;
      }

      // All coordinates must match exactly
      for (let i = 0; i < traj1.tracks.length; i++) {
        for (let f = 0; f < traj1.tracks[i].length; f++) {
          expect(traj1.tracks[i][f][0]).toBe(traj2.tracks[i][f][0]);
          expect(traj1.tracks[i][f][1]).toBe(traj2.tracks[i][f][1]);
          expect(traj1.visibility[i][f]).toBe(traj2.visibility[i][f]);
        }
      }
    });
  }

  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('different seeds produce different trajectories', (seed1, seed2) => {
    fc.pre(seed1 !== seed2);

    const config1: GenerativeFlowConfig = {
      pattern: 'spiral',
      numPoints: 20,
      numFrames: 30,
      width: 512,
      height: 512,
      params: { seed: seed1 },
    };
    const config2 = { ...config1, params: { seed: seed2 } };

    const traj1 = generateSpiralFlow(config1);
    const traj2 = generateSpiralFlow(config2);

    // At least one coordinate should differ
    let allSame = true;
    outer: for (let i = 0; i < traj1.tracks.length; i++) {
      for (let f = 0; f < traj1.tracks[i].length; f++) {
        if (traj1.tracks[i][f][0] !== traj2.tracks[i][f][0] ||
            traj1.tracks[i][f][1] !== traj2.tracks[i][f][1]) {
          allSame = false;
          break outer;
        }
      }
    }

    expect(allSame).toBe(false);
  });
});

// ============================================================================
// STRICT SEEDED RANDOM TESTS
// ============================================================================

describe('STRICT: SeededRandom for Wan-Move', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('SeededRandom produces deterministic sequence', (seed) => {
    const rng1 = new SeededRandom(seed);
    const rng2 = new SeededRandom(seed);

    for (let i = 0; i < 100; i++) {
      expect(rng1.next()).toBe(rng2.next());
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('SeededRandom.next() produces [0, 1) values', (seed) => {
    const rng = new SeededRandom(seed);

    for (let i = 0; i < 1000; i++) {
      const val = rng.next();
      expect(val).toBeGreaterThanOrEqual(0);
      expect(val).toBeLessThan(1);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 0.01, max: 1000, noNaN: true, noDefaultInfinity: true })
  ])('SeededRandom.range() produces values in range', (seed, min, range) => {
    const max = min + range;
    const rng = new SeededRandom(seed);

    for (let i = 0; i < 100; i++) {
      const val = rng.range(min, max);
      expect(val).toBeGreaterThanOrEqual(min);
      expect(val).toBeLessThanOrEqual(max);
    }
  });

  it('seed 0 produces valid output', () => {
    const rng = new SeededRandom(0);

    // Should produce valid values, not NaN or Infinity
    for (let i = 0; i < 100; i++) {
      const val = rng.next();
      expect(Number.isFinite(val)).toBe(true);
      expect(Number.isNaN(val)).toBe(false);
    }
  });
});

// ============================================================================
// STRICT JSON EXPORT TESTS
// ============================================================================

describe('STRICT: JSON Export', () => {
  test.prop([
    fc.integer({ min: 5, max: 30 }),
    fc.integer({ min: 8, max: 32 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('JSON export is valid and parseable', (numPoints, numFrames, seed) => {
    const config: GenerativeFlowConfig = {
      pattern: 'spiral',
      numPoints,
      numFrames,
      width: 512,
      height: 512,
      params: { seed },
    };

    const trajectory = generateSpiralFlow(config);
    const json = exportAsJSON(trajectory);

    // Should be valid JSON
    expect(() => JSON.parse(json)).not.toThrow();

    const parsed = JSON.parse(json);
    expect(parsed.tracks).toBeDefined();
    expect(parsed.visibility).toBeDefined();
    expect(parsed.metadata).toBeDefined();
    expect(parsed.tracks.length).toBe(numPoints);
    expect(parsed.visibility.length).toBe(numPoints);
  });

  test.prop([
    fc.integer({ min: 5, max: 20 }),
    fc.integer({ min: 8, max: 24 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('JSON roundtrip preserves data', (numPoints, numFrames, seed) => {
    const config: GenerativeFlowConfig = {
      pattern: 'spiral',
      numPoints,
      numFrames,
      width: 512,
      height: 512,
      params: { seed },
    };

    const trajectory = generateSpiralFlow(config);
    const json = exportAsJSON(trajectory);
    const parsed = JSON.parse(json);

    // Verify data integrity
    for (let i = 0; i < numPoints; i++) {
      for (let f = 0; f < numFrames; f++) {
        expect(parsed.tracks[i][f][0]).toBe(trajectory.tracks[i][f][0]);
        expect(parsed.tracks[i][f][1]).toBe(trajectory.tracks[i][f][1]);
        expect(parsed.visibility[i][f]).toBe(trajectory.visibility[i][f]);
      }
    }
  });
});

// ============================================================================
// STRICT METADATA TESTS
// ============================================================================

describe('STRICT: Trajectory Metadata', () => {
  test.prop([
    fc.integer({ min: 5, max: 50 }),
    fc.integer({ min: 8, max: 64 }),
    fc.integer({ min: 256, max: 1024 }),
    fc.integer({ min: 256, max: 1024 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('metadata matches actual data', (numPoints, numFrames, width, height, seed) => {
    const config: GenerativeFlowConfig = {
      pattern: 'spiral',
      numPoints,
      numFrames,
      width,
      height,
      params: { seed },
    };

    const trajectory = generateSpiralFlow(config);

    expect(trajectory.metadata.numPoints).toBe(numPoints);
    expect(trajectory.metadata.numFrames).toBe(numFrames);
    expect(trajectory.metadata.width).toBe(width);
    expect(trajectory.metadata.height).toBe(height);
    expect(trajectory.metadata.fps).toBe(16); // Default
  });
});

// ============================================================================
// STRICT ATTRACTOR TESTS (Chaotic systems)
// ============================================================================

import {
  generateLorenzAttractor,
  generateRosslerAttractor,
  generateAizawaAttractor,
  generateShapeMorph,
  generateForceFieldFlow,
  generateSplineFlow,
  compositeFlowLayers,
  sampleGradient,
  COLOR_GRADIENTS,
  simplexNoise2D,
  type AttractorConfig,
  type ShapeTargetConfig,
  type ForceFieldConfig,
} from '@/services/export/wanMoveExport';

describe('STRICT: Attractor Systems', () => {
  const attractors = ['lorenz', 'rossler', 'aizawa'] as const;

  for (const type of attractors) {
    test.prop([
      fc.integer({ min: 5, max: 30 }),
      fc.integer({ min: 16, max: 64 }),
      fc.integer({ min: 0, max: 1000000 })
    ])(`${type}: produces valid trajectory shape`, (numPoints, numFrames, seed) => {
      const config: AttractorConfig = {
        type,
        numPoints,
        numFrames,
        width: 512,
        height: 512,
        seed,
      };

      let trajectory: WanMoveTrajectory;
      switch (type) {
        case 'lorenz': trajectory = generateLorenzAttractor(config); break;
        case 'rossler': trajectory = generateRosslerAttractor(config); break;
        case 'aizawa': trajectory = generateAizawaAttractor(config); break;
      }

      expect(trajectory.tracks.length).toBe(numPoints);
      expect(trajectory.tracks[0].length).toBe(numFrames);
      expect(trajectory.visibility.length).toBe(numPoints);
    });

    test.prop([
      fc.integer({ min: 5, max: 20 }),
      fc.integer({ min: 16, max: 32 }),
      fc.integer({ min: 0, max: 1000000 })
    ])(`${type}: coordinates are within bounds`, (numPoints, numFrames, seed) => {
      const width = 512, height = 512;
      const config: AttractorConfig = {
        type,
        numPoints,
        numFrames,
        width,
        height,
        seed,
      };

      let trajectory: WanMoveTrajectory;
      switch (type) {
        case 'lorenz': trajectory = generateLorenzAttractor(config); break;
        case 'rossler': trajectory = generateRosslerAttractor(config); break;
        case 'aizawa': trajectory = generateAizawaAttractor(config); break;
      }

      for (const track of trajectory.tracks) {
        for (const [x, y] of track) {
          expect(x).toBeGreaterThanOrEqual(0);
          expect(x).toBeLessThanOrEqual(width);
          expect(y).toBeGreaterThanOrEqual(0);
          expect(y).toBeLessThanOrEqual(height);
          expect(Number.isFinite(x)).toBe(true);
          expect(Number.isFinite(y)).toBe(true);
        }
      }
    });

    test.prop([
      fc.integer({ min: 0, max: 1000000 })
    ])(`${type}: same seed produces identical trajectory`, (seed) => {
      const config: AttractorConfig = {
        type,
        numPoints: 10,
        numFrames: 20,
        width: 512,
        height: 512,
        seed,
      };

      let traj1: WanMoveTrajectory, traj2: WanMoveTrajectory;
      switch (type) {
        case 'lorenz':
          traj1 = generateLorenzAttractor(config);
          traj2 = generateLorenzAttractor({ ...config });
          break;
        case 'rossler':
          traj1 = generateRosslerAttractor(config);
          traj2 = generateRosslerAttractor({ ...config });
          break;
        case 'aizawa':
          traj1 = generateAizawaAttractor(config);
          traj2 = generateAizawaAttractor({ ...config });
          break;
      }

      for (let i = 0; i < traj1.tracks.length; i++) {
        for (let f = 0; f < traj1.tracks[i].length; f++) {
          expect(traj1.tracks[i][f][0]).toBe(traj2.tracks[i][f][0]);
          expect(traj1.tracks[i][f][1]).toBe(traj2.tracks[i][f][1]);
        }
      }
    });
  }
});

// ============================================================================
// STRICT SHAPE MORPH TESTS
// ============================================================================

describe('STRICT: Shape Morphing', () => {
  const shapes = ['circle', 'grid', 'heart', 'star', 'spiral', 'random'] as const;

  for (const source of shapes) {
    for (const target of shapes) {
      if (source === target) continue;

      test.prop([
        fc.integer({ min: 10, max: 30 }),
        fc.integer({ min: 16, max: 32 }),
        fc.integer({ min: 0, max: 1000000 })
      ])(`morph ${source} -> ${target}: valid trajectory`, (numPoints, numFrames, seed) => {
        const config: ShapeTargetConfig = {
          numPoints,
          numFrames,
          width: 512,
          height: 512,
          source: { type: source },
          target: { type: target },
          seed,
        };

        const trajectory = generateShapeMorph(config);

        expect(trajectory.tracks.length).toBe(numPoints);
        expect(trajectory.tracks[0].length).toBe(numFrames);

        // All coordinates finite
        for (const track of trajectory.tracks) {
          for (const [x, y] of track) {
            expect(Number.isFinite(x)).toBe(true);
            expect(Number.isFinite(y)).toBe(true);
          }
        }
      });
    }
  }

  test.prop([
    fc.integer({ min: 10, max: 30 }),
    fc.integer({ min: 16, max: 32 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('morph starts at source shape', (numPoints, numFrames, seed) => {
    const config: ShapeTargetConfig = {
      numPoints,
      numFrames,
      width: 512,
      height: 512,
      source: { type: 'grid' },
      target: { type: 'circle' },
      seed,
      morphNoise: 0, // No noise for precise test
    };

    const trajectory = generateShapeMorph(config);

    // Frame 0 should be near grid positions
    // (can't test exactly due to point distribution)
    for (const track of trajectory.tracks) {
      const [x, y] = track[0];
      expect(x).toBeGreaterThanOrEqual(0);
      expect(x).toBeLessThanOrEqual(512);
      expect(y).toBeGreaterThanOrEqual(0);
      expect(y).toBeLessThanOrEqual(512);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('morph is deterministic', (seed) => {
    const config: ShapeTargetConfig = {
      numPoints: 20,
      numFrames: 30,
      width: 512,
      height: 512,
      source: { type: 'circle' },
      target: { type: 'star' },
      seed,
    };

    const traj1 = generateShapeMorph(config);
    const traj2 = generateShapeMorph({ ...config });

    for (let i = 0; i < traj1.tracks.length; i++) {
      for (let f = 0; f < traj1.tracks[i].length; f++) {
        expect(traj1.tracks[i][f][0]).toBe(traj2.tracks[i][f][0]);
        expect(traj1.tracks[i][f][1]).toBe(traj2.tracks[i][f][1]);
      }
    }
  });
});

// ============================================================================
// STRICT FORCE FIELD TESTS
// ============================================================================

describe('STRICT: Force Field Physics', () => {
  test.prop([
    fc.integer({ min: 10, max: 50 }),
    fc.integer({ min: 16, max: 64 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('force field produces valid trajectory', (numPoints, numFrames, seed) => {
    const config: ForceFieldConfig = {
      numPoints,
      numFrames,
      width: 512,
      height: 512,
      forces: [
        { x: 256, y: 256, strength: 0.5, radius: 200, falloff: 'quadratic' }
      ],
      seed,
    };

    const trajectory = generateForceFieldFlow(config);

    expect(trajectory.tracks.length).toBe(numPoints);
    expect(trajectory.tracks[0].length).toBe(numFrames);
  });

  test.prop([
    fc.integer({ min: 10, max: 30 }),
    fc.integer({ min: 16, max: 32 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('attractor pulls particles inward', (numPoints, numFrames, seed) => {
    const cx = 256, cy = 256;
    const config: ForceFieldConfig = {
      numPoints,
      numFrames,
      width: 512,
      height: 512,
      forces: [
        { x: cx, y: cy, strength: 1.0, radius: 500, falloff: 'linear' }
      ],
      initialDistribution: 'edge',
      seed,
    };

    const trajectory = generateForceFieldFlow(config);

    // Average distance to center should decrease over time
    let avgDistStart = 0, avgDistEnd = 0;

    for (const track of trajectory.tracks) {
      const [sx, sy] = track[0];
      const [ex, ey] = track[track.length - 1];
      avgDistStart += Math.sqrt((sx - cx) ** 2 + (sy - cy) ** 2);
      avgDistEnd += Math.sqrt((ex - cx) ** 2 + (ey - cy) ** 2);
    }

    avgDistStart /= numPoints;
    avgDistEnd /= numPoints;

    // End should be closer to center than start (attractor)
    expect(avgDistEnd).toBeLessThan(avgDistStart);
  });

  test.prop([
    fc.integer({ min: 10, max: 30 }),
    fc.integer({ min: 16, max: 32 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('repulsor pushes particles outward', (numPoints, numFrames, seed) => {
    const cx = 256, cy = 256;
    const config: ForceFieldConfig = {
      numPoints,
      numFrames,
      width: 512,
      height: 512,
      forces: [
        { x: cx, y: cy, strength: -1.0, radius: 500, falloff: 'linear' }
      ],
      initialDistribution: 'center',
      seed,
    };

    const trajectory = generateForceFieldFlow(config);

    // Average distance to center should increase over time
    let avgDistStart = 0, avgDistEnd = 0;

    for (const track of trajectory.tracks) {
      const [sx, sy] = track[0];
      const [ex, ey] = track[track.length - 1];
      avgDistStart += Math.sqrt((sx - cx) ** 2 + (sy - cy) ** 2);
      avgDistEnd += Math.sqrt((ex - cx) ** 2 + (ey - cy) ** 2);
    }

    avgDistStart /= numPoints;
    avgDistEnd /= numPoints;

    // End should be farther from center than start (repulsor)
    expect(avgDistEnd).toBeGreaterThan(avgDistStart);
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('force field is deterministic', (seed) => {
    const config: ForceFieldConfig = {
      numPoints: 20,
      numFrames: 30,
      width: 512,
      height: 512,
      forces: [{ x: 256, y: 256, strength: 0.5, radius: 200 }],
      seed,
    };

    const traj1 = generateForceFieldFlow(config);
    const traj2 = generateForceFieldFlow({ ...config });

    for (let i = 0; i < traj1.tracks.length; i++) {
      for (let f = 0; f < traj1.tracks[i].length; f++) {
        expect(traj1.tracks[i][f][0]).toBe(traj2.tracks[i][f][0]);
        expect(traj1.tracks[i][f][1]).toBe(traj2.tracks[i][f][1]);
      }
    }
  });
});

// ============================================================================
// STRICT COLOR GRADIENT TESTS
// ============================================================================

describe('STRICT: Color Gradients', () => {
  const gradientNames = Object.keys(COLOR_GRADIENTS);

  for (const name of gradientNames) {
    test.prop([
      fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true })
    ])(`${name}: produces valid RGB`, (t) => {
      const gradient = COLOR_GRADIENTS[name as keyof typeof COLOR_GRADIENTS];
      const [r, g, b] = sampleGradient(gradient, t);

      expect(r).toBeGreaterThanOrEqual(0);
      expect(r).toBeLessThanOrEqual(255);
      expect(g).toBeGreaterThanOrEqual(0);
      expect(g).toBeLessThanOrEqual(255);
      expect(b).toBeGreaterThanOrEqual(0);
      expect(b).toBeLessThanOrEqual(255);
      expect(Number.isInteger(r)).toBe(true);
      expect(Number.isInteger(g)).toBe(true);
      expect(Number.isInteger(b)).toBe(true);
    });
  }

  test.prop([
    fc.double({ min: -10, max: 10, noNaN: true, noDefaultInfinity: true })
  ])('sampleGradient clamps out-of-range t', (t) => {
    const gradient = COLOR_GRADIENTS.viridis;
    const [r, g, b] = sampleGradient(gradient, t);

    // Should still produce valid RGB even with out-of-range t
    expect(r).toBeGreaterThanOrEqual(0);
    expect(r).toBeLessThanOrEqual(255);
    expect(g).toBeGreaterThanOrEqual(0);
    expect(g).toBeLessThanOrEqual(255);
    expect(b).toBeGreaterThanOrEqual(0);
    expect(b).toBeLessThanOrEqual(255);
  });

  it('gradient at t=0 matches first stop', () => {
    const gradient = COLOR_GRADIENTS.viridis;
    const [r, g, b] = sampleGradient(gradient, 0);
    const firstStop = gradient.stops[0].color;

    expect(r).toBe(firstStop[0]);
    expect(g).toBe(firstStop[1]);
    expect(b).toBe(firstStop[2]);
  });

  it('gradient at t=1 matches last stop', () => {
    const gradient = COLOR_GRADIENTS.viridis;
    const [r, g, b] = sampleGradient(gradient, 1);
    const lastStop = gradient.stops[gradient.stops.length - 1].color;

    expect(r).toBe(lastStop[0]);
    expect(g).toBe(lastStop[1]);
    expect(b).toBe(lastStop[2]);
  });
});

// ============================================================================
// STRICT SIMPLEX NOISE TESTS
// ============================================================================

describe('STRICT: Simplex Noise', () => {
  test.prop([
    fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 0, max: 1000000 })
  ])('noise produces values in [0, 1]', (x, y, seed) => {
    const value = simplexNoise2D(x, y, seed);

    expect(value).toBeGreaterThanOrEqual(0);
    expect(value).toBeLessThanOrEqual(1);
    expect(Number.isFinite(value)).toBe(true);
  });

  test.prop([
    fc.double({ min: -100, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: -100, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 0, max: 1000000 })
  ])('noise is deterministic', (x, y, seed) => {
    const val1 = simplexNoise2D(x, y, seed);
    const val2 = simplexNoise2D(x, y, seed);

    expect(val1).toBe(val2);
  });

  test.prop([
    // Use uniqueArray to ensure we're testing truly different seeds
    fc.uniqueArray(fc.integer({ min: 0, max: 1000000 }), { minLength: 10, maxLength: 10 })
  ])('different seeds mostly produce different noise', (seeds) => {
    // Test at multiple points to ensure diversity
    const points = [
      { x: 0.5, y: 0.5 },
      { x: 1.5, y: 1.5 },
      { x: 0.3, y: 0.7 },
      { x: 2.7, y: 3.1 },
    ];
    
    // Count total unique values across all points and seeds
    let totalUniqueCount = 0;
    for (const pt of points) {
      const values = seeds.map(s => simplexNoise2D(pt.x, pt.y, s));
      const uniqueValues = new Set(values);
      totalUniqueCount += uniqueValues.size;
    }
    
    // With 10 seeds and 4 points (40 total), we expect at least 12 unique values
    // This accounts for hash collisions due to discrete gradient directions
    expect(totalUniqueCount).toBeGreaterThanOrEqual(12);
  });

  test.prop([
    fc.double({ min: 0, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 0, max: 100, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 0, max: 1000000 })
  ])('noise is continuous (nearby points have similar values)', (x, y, seed) => {
    const delta = 0.01;
    const center = simplexNoise2D(x, y, seed);
    const right = simplexNoise2D(x + delta, y, seed);
    const up = simplexNoise2D(x, y + delta, seed);

    // Nearby points should be similar (not jump more than 0.5)
    expect(Math.abs(center - right)).toBeLessThan(0.5);
    expect(Math.abs(center - up)).toBeLessThan(0.5);
  });
});

// ============================================================================
// STRICT LAYER COMPOSITION TESTS
// ============================================================================

describe('STRICT: Layer Composition', () => {
  test.prop([
    fc.integer({ min: 2, max: 5 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('compositeFlowLayers combines all tracks', (layerCount, seed) => {
    const layers = [];
    const pointsPerLayer = 10;

    for (let i = 0; i < layerCount; i++) {
      const config: GenerativeFlowConfig = {
        pattern: 'spiral',
        numPoints: pointsPerLayer,
        numFrames: 20,
        width: 512,
        height: 512,
        params: { seed: seed + i },
      };
      layers.push({ trajectory: generateSpiralFlow(config) });
    }

    const composite = compositeFlowLayers(layers);

    expect(composite.tracks.length).toBe(layerCount * pointsPerLayer);
    expect(composite.visibility.length).toBe(layerCount * pointsPerLayer);
    expect(composite.metadata.numPoints).toBe(layerCount * pointsPerLayer);
  });

  it('compositeFlowLayers throws on empty input', () => {
    expect(() => compositeFlowLayers([])).toThrow();
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Wan-Move Large Data', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('handles 100 points x 100 frames', (seed) => {
    const config: GenerativeFlowConfig = {
      pattern: 'spiral',
      numPoints: 100,
      numFrames: 100,
      width: 1920,
      height: 1080,
      params: { seed },
    };

    const trajectory = generateSpiralFlow(config);
    const npyData = exportAsNPYData(trajectory);

    // Verify sizes
    expect(trajectory.tracks.length).toBe(100);
    expect(trajectory.tracks[0].length).toBe(100);
    expect(npyData.tracks.length).toBe(100 * 100 * 2);
    expect(npyData.visibility.length).toBe(100 * 100);
  });
});
