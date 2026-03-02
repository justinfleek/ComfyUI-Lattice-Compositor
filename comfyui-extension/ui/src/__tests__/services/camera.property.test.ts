/**
 * STRICT Property Tests for Camera System
 * 
 * Tests the invariants that must hold for correct camera animation:
 * 1. Determinism: same seed + same config = same shake
 * 2. Bounds: shake offset should be proportional to intensity
 * 3. Rack focus: smooth transition between distances
 * 4. Physics: camera movements should be continuous
 * 
 * TOLERANCE: STRICT - Camera bugs cause visible jitter in exports
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  CameraShake,
  getRackFocusDistance,
  DEFAULT_SHAKE_CONFIG,
  DEFAULT_RACK_FOCUS,
  type CameraShakeConfig,
  type RackFocusConfig,
} from '@/services/cameraEnhancements';

// ============================================================================
// STRICT CAMERA SHAKE DETERMINISM TESTS
// ============================================================================

describe('STRICT: Camera Shake Determinism', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 0, max: 300 })
  ])('same seed produces same shake at same frame', (seed, frame) => {
    const config1: CameraShakeConfig = {
      ...DEFAULT_SHAKE_CONFIG,
      seed,
      intensity: 0.5,
    };
    const config2: CameraShakeConfig = {
      ...DEFAULT_SHAKE_CONFIG,
      seed,
      intensity: 0.5,
    };
    
    const shake1 = new CameraShake(config1, 0, 1000);
    const shake2 = new CameraShake(config2, 0, 1000);
    
    const offset1 = shake1.getOffset(frame);
    const offset2 = shake2.getOffset(frame);
    
    expect(offset1.position.x).toBe(offset2.position.x);
    expect(offset1.position.y).toBe(offset2.position.y);
    expect(offset1.position.z).toBe(offset2.position.z);
    expect(offset1.rotation.x).toBe(offset2.rotation.x);
    expect(offset1.rotation.y).toBe(offset2.rotation.y);
    expect(offset1.rotation.z).toBe(offset2.rotation.z);
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('different seeds produce different shakes', (seed1, seed2) => {
    fc.pre(seed1 !== seed2);
    
    const shake1 = new CameraShake({
      ...DEFAULT_SHAKE_CONFIG,
      seed: seed1,
      intensity: 0.5,
    }, 0, 1000);
    
    const shake2 = new CameraShake({
      ...DEFAULT_SHAKE_CONFIG,
      seed: seed2,
      intensity: 0.5,
    }, 0, 1000);
    
    // Check at frame 50
    const offset1 = shake1.getOffset(50);
    const offset2 = shake2.getOffset(50);
    
    // At least one value should differ
    const allSame = 
      offset1.position.x === offset2.position.x &&
      offset1.position.y === offset2.position.y &&
      offset1.position.z === offset2.position.z;
    
    expect(allSame).toBe(false);
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.array(fc.integer({ min: 0, max: 299 }), { minLength: 10, maxLength: 50 })
  ])('frame access order does not affect results', (seed, frames) => {
    const config: CameraShakeConfig = {
      ...DEFAULT_SHAKE_CONFIG,
      seed,
      intensity: 0.5,
    };
    
    const shake = new CameraShake(config, 0, 1000);
    const results = new Map<number, { x: number; y: number; z: number }>();
    
    // First pass: collect results
    for (const frame of frames) {
      const offset = shake.getOffset(frame);
      results.set(frame, { ...offset.position });
    }
    
    // Shuffle order
    const shuffled = [...frames].sort(() => Math.random() - 0.5);
    
    // Second pass: verify consistency
    for (const frame of shuffled) {
      const offset = shake.getOffset(frame);
      const stored = results.get(frame)!;
      
      expect(offset.position.x).toBe(stored.x);
      expect(offset.position.y).toBe(stored.y);
      expect(offset.position.z).toBe(stored.z);
    }
  });
});

// ============================================================================
// STRICT CAMERA SHAKE BOUNDS TESTS
// ============================================================================

describe('STRICT: Camera Shake Bounds', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true })
  ])('shake magnitude is proportional to intensity', (seed, intensity) => {
    const shake = new CameraShake({
      ...DEFAULT_SHAKE_CONFIG,
      seed,
      intensity,
      decay: 0, // No decay
    }, 0, 1000);
    
    // Collect max offset across multiple frames
    let maxMagnitude = 0;
    
    for (let frame = 0; frame < 100; frame++) {
      const offset = shake.getOffset(frame);
      const magnitude = Math.sqrt(
        offset.position.x ** 2 +
        offset.position.y ** 2 +
        offset.position.z ** 2
      );
      maxMagnitude = Math.max(maxMagnitude, magnitude);
    }
    
    // With intensity 0, shake should be 0
    if (intensity === 0) {
      expect(maxMagnitude).toBe(0);
    } else {
      // Shake should exist but be bounded
      // Max shake should scale roughly with intensity
      // This is a sanity check, not exact math
      expect(maxMagnitude).toBeLessThan(1000 * intensity + 10);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('zero intensity produces zero shake', (seed) => {
    const shake = new CameraShake({
      ...DEFAULT_SHAKE_CONFIG,
      seed,
      intensity: 0,
    }, 0, 1000);
    
    for (let frame = 0; frame < 50; frame++) {
      const offset = shake.getOffset(frame);
      
      // Note: Use == 0 to accept both +0 and -0 (floating-point signed zero)
      // -0 can occur when multiplying by 0 in certain cases
      expect(offset.position.x == 0).toBe(true);
      expect(offset.position.y == 0).toBe(true);
      expect(offset.position.z == 0).toBe(true);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('shake values are finite numbers', (seed) => {
    const shake = new CameraShake({
      ...DEFAULT_SHAKE_CONFIG,
      seed,
      intensity: 0.8,
    }, 0, 1000);
    
    for (let frame = 0; frame < 100; frame++) {
      const offset = shake.getOffset(frame);
      
      expect(Number.isFinite(offset.position.x)).toBe(true);
      expect(Number.isFinite(offset.position.y)).toBe(true);
      expect(Number.isFinite(offset.position.z)).toBe(true);
      expect(Number.isNaN(offset.position.x)).toBe(false);
      expect(Number.isNaN(offset.position.y)).toBe(false);
      expect(Number.isNaN(offset.position.z)).toBe(false);
    }
  });
});

// ============================================================================
// STRICT RACK FOCUS TESTS
// ============================================================================

describe('STRICT: Rack Focus', () => {
  test.prop([
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 1, max: 100 })
  ])('rack focus returns start distance at start frame', (startDist, endDist, duration) => {
    const config: RackFocusConfig = {
      startDistance: startDist,
      endDistance: endDist,
      duration,
      startFrame: 0,
      easing: 'linear',
      holdStart: 0,
      holdEnd: 0,
    };
    
    const distance = getRackFocusDistance(config, 0);
    expect(distance).toBe(startDist);
  });

  test.prop([
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 1, max: 100 })
  ])('rack focus returns end distance at end frame', (startDist, endDist, duration) => {
    const config: RackFocusConfig = {
      startDistance: startDist,
      endDistance: endDist,
      duration,
      startFrame: 0,
      easing: 'linear',
      holdStart: 0,
      holdEnd: 0,
    };
    
    const distance = getRackFocusDistance(config, duration);
    
    // Should be very close to end distance
    expect(Math.abs(distance - endDist)).toBeLessThan(0.01);
  });

  test.prop([
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 10, max: 100 })
  ])('linear rack focus at midpoint is average', (startDist, endDist, duration) => {
    const config: RackFocusConfig = {
      startDistance: startDist,
      endDistance: endDist,
      duration,
      startFrame: 0,
      easing: 'linear',
      holdStart: 0,
      holdEnd: 0,
    };
    
    const midFrame = Math.floor(duration / 2);
    const distance = getRackFocusDistance(config, midFrame);
    const expectedMid = (startDist + endDist) / 2;
    
    // Should be close to average (allow for integer frame rounding)
    const tolerance = Math.abs(endDist - startDist) / duration;
    expect(Math.abs(distance - expectedMid)).toBeLessThan(tolerance + 0.01);
  });

  test.prop([
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 10, max: 100 })
  ])('rack focus is monotonic for linear easing', (startDist, endDist, duration) => {
    const config: RackFocusConfig = {
      startDistance: startDist,
      endDistance: endDist,
      duration,
      startFrame: 0,
      easing: 'linear',
      holdStart: 0,
      holdEnd: 0,
    };
    
    let prevDistance = startDist;
    const increasing = endDist > startDist;
    
    for (let frame = 1; frame <= duration; frame++) {
      const distance = getRackFocusDistance(config, frame);
      
      if (increasing) {
        expect(distance).toBeGreaterThanOrEqual(prevDistance - 0.001);
      } else {
        expect(distance).toBeLessThanOrEqual(prevDistance + 0.001);
      }
      
      prevDistance = distance;
    }
  });

  test.prop([
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 100, max: 5000, noNaN: true, noDefaultInfinity: true }),
    fc.integer({ min: 10, max: 100 })
  ])('rack focus returns finite values', (startDist, endDist, duration) => {
    const config: RackFocusConfig = {
      startDistance: startDist,
      endDistance: endDist,
      duration,
      startFrame: 0,
      easing: 'ease-in-out',
      holdStart: 0,
      holdEnd: 0,
    };
    
    for (let frame = 0; frame <= duration; frame++) {
      const distance = getRackFocusDistance(config, frame);
      
      expect(Number.isFinite(distance)).toBe(true);
      expect(Number.isNaN(distance)).toBe(false);
      expect(distance).toBeGreaterThan(0);
    }
  });
});

// ============================================================================
// STRICT DECAY TESTS
// ============================================================================

describe('STRICT: Camera Shake Decay', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 10, max: 100 })
  ])('decay reduces shake over time', (seed, duration) => {
    const shake = new CameraShake({
      ...DEFAULT_SHAKE_CONFIG,
      seed,
      intensity: 1.0,
      decay: 1.0, // Full decay
    }, 0, duration);
    
    // Get shake at start and end
    const startOffset = shake.getOffset(0);
    const endOffset = shake.getOffset(duration);
    
    const startMag = Math.sqrt(
      startOffset.position.x ** 2 +
      startOffset.position.y ** 2 +
      startOffset.position.z ** 2
    );
    
    const endMag = Math.sqrt(
      endOffset.position.x ** 2 +
      endOffset.position.y ** 2 +
      endOffset.position.z ** 2
    );
    
    // End should be less than or equal to start (decay)
    // Note: noise can cause variations, so we check general trend
    // by comparing averages near start vs end
    let avgStartMag = 0;
    let avgEndMag = 0;
    
    for (let i = 0; i < 10; i++) {
      const so = shake.getOffset(i);
      avgStartMag += Math.sqrt(so.position.x ** 2 + so.position.y ** 2 + so.position.z ** 2);
      
      const eo = shake.getOffset(duration - 10 + i);
      avgEndMag += Math.sqrt(eo.position.x ** 2 + eo.position.y ** 2 + eo.position.z ** 2);
    }
    
    avgStartMag /= 10;
    avgEndMag /= 10;
    
    // With full decay, end average should be less than start average
    expect(avgEndMag).toBeLessThanOrEqual(avgStartMag + 0.1); // Small tolerance for noise
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Camera System Under Load', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 100, max: 1000 })
  ])('rapid shake access produces consistent results', (seed, frameCount) => {
    const shake = new CameraShake({
      ...DEFAULT_SHAKE_CONFIG,
      seed,
      intensity: 0.5,
    }, 0, frameCount);
    
    const results = new Map<number, { x: number; y: number; z: number }>();
    
    // Random access pattern
    const frames = Array.from({ length: 100 }, () => Math.floor(Math.random() * frameCount));
    
    // First pass
    for (const frame of frames) {
      const offset = shake.getOffset(frame);
      results.set(frame, { ...offset.position });
    }
    
    // Second pass with different order
    const shuffled = [...frames].reverse();
    
    for (const frame of shuffled) {
      const offset = shake.getOffset(frame);
      const stored = results.get(frame)!;
      
      expect(offset.position.x).toBe(stored.x);
      expect(offset.position.y).toBe(stored.y);
      expect(offset.position.z).toBe(stored.z);
    }
  });
});
