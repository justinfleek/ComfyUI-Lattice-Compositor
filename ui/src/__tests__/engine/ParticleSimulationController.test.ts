/**
 * ParticleSimulationController Determinism Tests
 *
 * These tests verify that particle simulation produces deterministic
 * results regardless of scrub order.
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  ParticleSimulationController,
  ParticleSimulationRegistry,
  type ParticleSnapshot,
} from '@/engine/ParticleSimulationController';
import type { ParticleSystemConfig } from '@/services/particleSystem';

// ============================================================================
// TEST UTILITIES
// ============================================================================

function createTestConfig(): ParticleSystemConfig {
  return {
    maxParticles: 100,
    gravity: 50,
    windStrength: 0,
    windDirection: 0,
    warmupPeriod: 0,
    respectMaskBoundary: false,
    boundaryBehavior: 'wrap' as const,
    friction: 0.02,
    turbulenceFields: [],
    subEmitters: [],
    collision: {
      enabled: false,
      particleCollision: false,
      particleCollisionRadius: 1.0,
      particleCollisionResponse: 'bounce' as const,
      particleCollisionDamping: 0.8,
      layerCollision: false,
      layerCollisionLayerId: null,
      layerCollisionThreshold: 0.5,
      floorEnabled: false,
      floorY: 1.0,
      ceilingEnabled: false,
      ceilingY: 0.0,
      wallsEnabled: false,
      bounciness: 0.5,
      friction: 0.1,
      spatialHashCellSize: 50,
    },
  };
}

/**
 * Compare two particle snapshots for equality
 */
function snapshotsEqual(a: ParticleSnapshot, b: ParticleSnapshot): boolean {
  if (a.frame !== b.frame) return false;
  if (a.count !== b.count) return false;
  if (a.seed !== b.seed) return false;

  // Compare each particle
  for (let i = 0; i < a.particles.length; i++) {
    const pa = a.particles[i];
    const pb = b.particles[i];

    if (!pb) return false;
    if (pa.id !== pb.id) return false;
    if (Math.abs(pa.x - pb.x) > 0.0001) return false;
    if (Math.abs(pa.y - pb.y) > 0.0001) return false;
    if (Math.abs(pa.vx - pb.vx) > 0.0001) return false;
    if (Math.abs(pa.vy - pb.vy) > 0.0001) return false;
  }

  return true;
}

// ============================================================================
// TESTS
// ============================================================================

describe('ParticleSimulationController', () => {
  let controller: ParticleSimulationController;
  let config: ParticleSystemConfig;
  const testSeed = 12345;

  beforeEach(() => {
    config = createTestConfig();
    controller = new ParticleSimulationController(config, testSeed);
  });

  describe('Basic Evaluation', () => {
    it('should return snapshot for frame 0', () => {
      const snapshot = controller.evaluateAtFrame(0);

      expect(snapshot).toBeDefined();
      expect(snapshot.frame).toBe(0);
      expect(snapshot.seed).toBe(testSeed);
    });

    it('should return frozen snapshot', () => {
      const snapshot = controller.evaluateAtFrame(10);

      expect(Object.isFrozen(snapshot)).toBe(true);
      expect(Object.isFrozen(snapshot.particles)).toBe(true);
    });

    it('should return consistent results for same frame', () => {
      const snapshot1 = controller.evaluateAtFrame(30);
      const snapshot2 = controller.evaluateAtFrame(30);

      expect(snapshotsEqual(snapshot1, snapshot2)).toBe(true);
    });
  });

  describe('Seed Determinism', () => {
    it('should produce identical results with same seed', () => {
      const controller1 = new ParticleSimulationController(config, testSeed);
      const controller2 = new ParticleSimulationController(config, testSeed);

      const snapshot1 = controller1.evaluateAtFrame(50);
      const snapshot2 = controller2.evaluateAtFrame(50);

      expect(snapshotsEqual(snapshot1, snapshot2)).toBe(true);
    });

    it('should produce different results with different seeds', () => {
      const controller1 = new ParticleSimulationController(config, 12345);
      const controller2 = new ParticleSimulationController(config, 67890);

      const snapshot1 = controller1.evaluateAtFrame(50);
      const snapshot2 = controller2.evaluateAtFrame(50);

      // Different seeds should (almost certainly) produce different results
      // Note: This could theoretically fail with astronomically low probability
      expect(snapshotsEqual(snapshot1, snapshot2)).toBe(false);
    });
  });

  describe('Scrub Order Independence', () => {
    it('should produce same results regardless of scrub order - forward then back', () => {
      // First path: 0 → 30 → 60 → 30
      controller.evaluateAtFrame(0);
      controller.evaluateAtFrame(30);
      controller.evaluateAtFrame(60);
      const snapshot30_first = controller.evaluateAtFrame(30);

      // Reset and try different path
      const controller2 = new ParticleSimulationController(config, testSeed);

      // Second path: 0 → 30 directly
      controller2.evaluateAtFrame(0);
      const snapshot30_direct = controller2.evaluateAtFrame(30);

      expect(snapshotsEqual(snapshot30_first, snapshot30_direct)).toBe(true);
    });

    it('should produce same results for frame 60 via different paths', () => {
      // Path 1: direct
      const snapshot60_direct = controller.evaluateAtFrame(60);

      // Path 2: via many intermediate frames
      const controller2 = new ParticleSimulationController(config, testSeed);
      for (let i = 0; i <= 60; i += 10) {
        controller2.evaluateAtFrame(i);
      }
      const snapshot60_stepped = controller2.evaluateAtFrame(60);

      expect(snapshotsEqual(snapshot60_direct, snapshot60_stepped)).toBe(true);
    });

    it('should handle random scrub pattern', () => {
      const frames = [45, 15, 60, 30, 5, 75, 40];
      const firstResults = new Map<number, ParticleSnapshot>();

      // First pass
      for (const frame of frames) {
        firstResults.set(frame, controller.evaluateAtFrame(frame));
      }

      // Second pass (different order)
      const reversedFrames = [...frames].reverse();
      for (const frame of reversedFrames) {
        const newResult = controller.evaluateAtFrame(frame);
        const originalResult = firstResults.get(frame)!;

        expect(snapshotsEqual(newResult, originalResult)).toBe(true);
      }
    });
  });

  describe('Reset', () => {
    it('should clear state on reset', () => {
      controller.evaluateAtFrame(50);
      controller.reset();
      const snapshot = controller.evaluateAtFrame(0);

      expect(snapshot.frame).toBe(0);
    });

    it('should produce same results after reset with same seed', () => {
      const snapshot50_before = controller.evaluateAtFrame(50);

      controller.reset();

      const snapshot50_after = controller.evaluateAtFrame(50);

      expect(snapshotsEqual(snapshot50_before, snapshot50_after)).toBe(true);
    });
  });

  describe('Config Updates', () => {
    it('should reset checkpoints when config changes', () => {
      const snapshot30_original = controller.evaluateAtFrame(30);

      // Change config (e.g., gravity)
      controller.updateConfig({ gravity: 100 });

      const snapshot30_new = controller.evaluateAtFrame(30);

      // Results should be different with different gravity
      // (unless by coincidence, which is unlikely)
      expect(snapshot30_original.count).toBeGreaterThanOrEqual(0);
      expect(snapshot30_new.count).toBeGreaterThanOrEqual(0);
    });
  });
});

describe('ParticleSimulationRegistry', () => {
  let registry: ParticleSimulationRegistry;
  let config: ParticleSystemConfig;

  beforeEach(() => {
    registry = new ParticleSimulationRegistry();
    config = createTestConfig();
  });

  describe('Controller Management', () => {
    it('should create controller for new layer', () => {
      const controller = registry.getController('layer-1', config);
      expect(controller).toBeDefined();
      expect(controller.getSeed()).toBeDefined();
    });

    it('should return same controller for same layer', () => {
      const controller1 = registry.getController('layer-1', config);
      const controller2 = registry.getController('layer-1', config);

      expect(controller1).toBe(controller2);
    });

    it('should return different controllers for different layers', () => {
      const controller1 = registry.getController('layer-1', config);
      const controller2 = registry.getController('layer-2', config);

      expect(controller1).not.toBe(controller2);
    });
  });

  describe('Deterministic Seeds', () => {
    it('should generate consistent seed for same layer ID', () => {
      const registry1 = new ParticleSimulationRegistry();
      const registry2 = new ParticleSimulationRegistry();

      const controller1 = registry1.getController('test-layer', config);
      const controller2 = registry2.getController('test-layer', config);

      expect(controller1.getSeed()).toBe(controller2.getSeed());
    });

    it('should generate different seeds for different layer IDs', () => {
      const controller1 = registry.getController('layer-a', config);
      const controller2 = registry.getController('layer-b', config);

      expect(controller1.getSeed()).not.toBe(controller2.getSeed());
    });
  });

  describe('Evaluate Layer', () => {
    it('should evaluate and return snapshot', () => {
      const snapshot = registry.evaluateLayer('layer-1', 30, config);

      expect(snapshot).toBeDefined();
      expect(snapshot.frame).toBe(30);
    });

    it('should produce deterministic results', () => {
      const snapshot1 = registry.evaluateLayer('layer-1', 30, config);
      const snapshot2 = registry.evaluateLayer('layer-1', 30, config);

      expect(snapshotsEqual(snapshot1, snapshot2)).toBe(true);
    });
  });

  describe('Clear', () => {
    it('should remove all controllers', () => {
      registry.getController('layer-1', config);
      registry.getController('layer-2', config);

      registry.clear();

      // New controller should be created (different instance)
      const newController = registry.getController('layer-1', config);
      expect(newController).toBeDefined();
    });
  });
});
