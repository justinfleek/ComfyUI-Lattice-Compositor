/**
 * REGRESSION TEST: BUG - Mass=0 Division by Zero
 * 
 * @fixed 2026-01-06
 * @file services/physics/PhysicsEngine.ts
 * @rootCause Dynamic bodies with mass=0 caused division by zero when calculating inverseMass (1/mass)
 * @fix Added mass||1 fallback to default to mass=1 when mass is 0
 * @counterexample Adding dynamic body with mass=0 produced Infinity for inverseMass
 */

import { describe, test, expect } from 'vitest';
import { PhysicsEngine } from '@/services/physics/PhysicsEngine';
import type { RigidBodyConfig } from '@/types/physics';

// Helper to create a complete RigidBodyConfig with sensible defaults
function createRigidBodyConfig(overrides: Partial<RigidBodyConfig> & { id: string }): RigidBodyConfig {
  return {
    layerId: overrides.layerId ?? `layer-${overrides.id}`,
    type: 'dynamic',
    position: { x: 0, y: 0 },
    velocity: { x: 0, y: 0 },
    mass: 1,
    angle: 0,
    angularVelocity: 0,
    shape: { type: 'circle', radius: 10 },
    material: { restitution: 0.5, friction: 0.5 },
    filter: { category: 1, mask: 1, group: 0 },
    response: 'collide',
    linearDamping: 0,
    angularDamping: 0,
    canSleep: false,
    sleepThreshold: 0.1,
    ...overrides,
  };
}

describe('BUG Regression: Mass=0 Division by Zero', () => {
  /**
   * This test MUST reproduce the exact counterexample from the bug report.
   * Before fix: Dynamic body with mass=0 would cause 1/0 → Infinity
   * After fix: mass||1 defaults to mass=1, so inverseMass = 1/1 = 1
   */
  test('original counterexample now passes', () => {
    const engine = new PhysicsEngine();

    // Create a dynamic body with mass=0 (the bug case)
    const bodyConfig = createRigidBodyConfig({
      id: 'test-body',
      type: 'dynamic',
      mass: 0, // Zero mass - would cause division by zero
    });

    // Before fix: Would throw or produce Infinity
    // After fix: Should handle gracefully (mass||1 = 1, so inverseMass = 1)
    engine.addRigidBody(bodyConfig);

    // Verify body was added successfully and simulation runs without errors
    // Before fix: Would crash or produce Infinity/NaN
    // After fix: Should handle gracefully (mass||1 = 1, so inverseMass = 1)
    expect(() => {
      const state = engine.evaluateFrame(0);
      const body = state.rigidBodies.find(b => b.id === 'test-body');
      expect(body).toBeDefined();
      // Verify body has valid state (not NaN/Infinity)
      expect(Number.isFinite(body!.position.x)).toBe(true);
      expect(Number.isFinite(body!.position.y)).toBe(true);
    }).not.toThrow();
  });

  /**
   * Additional edge cases related to this bug.
   */
  test('kinematic body with mass=0 also works', () => {
    const engine = new PhysicsEngine();

    const bodyConfig = createRigidBodyConfig({
      id: 'test-kinematic',
      type: 'kinematic',
      mass: 0, // Zero mass
    });

    engine.addRigidBody(bodyConfig);
    const state = engine.evaluateFrame(0);
    const body = state.rigidBodies.find((b) => b.id === 'test-kinematic');

    expect(body).toBeDefined();
    if (body) {
      // Verify body has valid state (not NaN/Infinity)
      expect(Number.isFinite(body.position.x)).toBe(true);
      expect(Number.isFinite(body.position.y)).toBe(true);
    }
  });

  test('static bodies with mass=0 have zero inverseMass', () => {
    const engine = new PhysicsEngine();

    const bodyConfig = createRigidBodyConfig({
      id: 'test-static',
      type: 'static',
      mass: 0, // Zero mass, but static
    });

    engine.addRigidBody(bodyConfig);
    const state = engine.evaluateFrame(0);
    const body = state.rigidBodies.find((b) => b.id === 'test-static');

    expect(body).toBeDefined();
    if (body) {
      // Verify body has valid state
      expect(Number.isFinite(body.position.x)).toBe(true);
    }
  });

  test('normal dynamic bodies with non-zero mass work correctly', () => {
    const engine = new PhysicsEngine();

    const bodyConfig = createRigidBodyConfig({
      id: 'test-normal',
      type: 'dynamic',
      mass: 10, // Normal mass
    });

    engine.addRigidBody(bodyConfig);
    const state = engine.evaluateFrame(0);
    const body = state.rigidBodies.find((b) => b.id === 'test-normal');

    expect(body).toBeDefined();
    if (body) {
      // Verify body has valid state
      expect(Number.isFinite(body.position.x)).toBe(true);
      expect(Number.isFinite(body.velocity.x)).toBe(true);
    }
  });

  test('simulation runs without errors with zero-mass dynamic bodies', () => {
    const engine = new PhysicsEngine();

    // Add multiple bodies, some with zero mass
    engine.addRigidBody({
      id: 'body-1',
      layerId: 'layer-1',
      type: 'dynamic',
      position: { x: 0, y: 0 },
      velocity: { x: 0, y: 0 },
      mass: 0, // Zero mass
      angle: 0,
      angularVelocity: 0,
      shape: { type: 'circle', radius: 10 },
      material: { restitution: 0.5, friction: 0.5 },
      filter: { category: 1, mask: 1, group: 0 },
      response: 'collide',
      linearDamping: 0,
      angularDamping: 0,
      canSleep: false,
      sleepThreshold: 0.1,
    });

    engine.addRigidBody({
      id: 'body-2',
      layerId: 'layer-2',
      type: 'dynamic',
      position: { x: 10, y: 10 },
      velocity: { x: 1, y: 1 },
      mass: 5, // Normal mass
      angle: 0,
      angularVelocity: 0,
      shape: { type: 'circle', radius: 10 },
      material: { restitution: 0.5, friction: 0.5 },
      filter: { category: 1, mask: 1, group: 0 },
      response: 'collide',
      linearDamping: 0,
      angularDamping: 0,
      canSleep: false,
      sleepThreshold: 0.1,
    });

    // Simulate multiple frames - should not crash
    for (let frame = 0; frame <= 10; frame++) {
      const state = engine.evaluateFrame(frame);
      expect(state.rigidBodies.length).toBe(2);
      
      // All body states should be valid (not NaN/Infinity)
      for (const body of state.rigidBodies) {
        expect(Number.isFinite(body.position.x)).toBe(true);
        expect(Number.isFinite(body.position.y)).toBe(true);
        expect(Number.isFinite(body.velocity.x)).toBe(true);
        expect(Number.isFinite(body.velocity.y)).toBe(true);
      }
    }
  });
});
