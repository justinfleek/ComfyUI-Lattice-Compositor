/**
 * Edge case tests to verify potential bugs in animation.ts
 */

import { describe, test, expect } from 'vitest';
import { createTestKeyframe as createKeyframe } from '../setup';
import { createAnimatableProperty } from '@/types/animation';
import { interpolateProperty } from '@/services/interpolation';

describe('animation.ts edge cases - BUG FIXES VERIFIED', () => {
  describe('NaN frame handling - FIXED', () => {
    test('createKeyframe with NaN frame throws error', () => {
      // BUG FIX: Now throws instead of silently creating invalid keyframe
      expect(() => createKeyframe(NaN, 100)).toThrow('Invalid keyframe frame');
    });

    test('valid keyframes interpolate correctly', () => {
      const prop = createAnimatableProperty('test', 0);
      prop.animated = true;
      prop.keyframes = [
        createKeyframe(0, 0),
        createKeyframe(30, 50),
      ];

      // At frame 15, should get linear interpolation
      const result = interpolateProperty(prop, 15, 30);
      
      // Linear interpolation: 0 + 0.5 * (50 - 0) = 25
      expect(result).toBeCloseTo(25, 5);
    });
  });

  describe('Infinity frame handling - FIXED', () => {
    test('createKeyframe with Infinity frame throws error', () => {
      expect(() => createKeyframe(Infinity, 100)).toThrow('Invalid keyframe frame');
    });

    test('createKeyframe with -Infinity frame throws error', () => {
      expect(() => createKeyframe(-Infinity, 100)).toThrow('Invalid keyframe frame');
    });
  });

  describe('overlapping bezier handles', () => {
    test('keyframes 2 frames apart have overlapping handles', () => {
      const kf1 = createKeyframe(0, 0);
      const kf2 = createKeyframe(2, 100);
      
      // kf1.outHandle.frame = 5 (extends to frame 5)
      // kf2.inHandle.frame = -5 (extends to frame -3)
      // These overlap! The segment is only 2 frames but handles span 10 frames
      
      expect(kf1.outHandle.frame).toBe(5);
      expect(kf2.inHandle.frame).toBe(-5);
      
      // Is this handled correctly by bezier interpolation?
      // The handles are normalized by duration in cubicBezierEasing
    });
  });

  describe('negative frame handling', () => {
    test('createKeyframe with negative frame', () => {
      const kf = createKeyframe(-10, 100);
      expect(kf.frame).toBe(-10);
      // Negative frames might be valid for pre-roll animations
      // But should they be allowed by default?
    });
  });

  describe('ID collision potential', () => {
    test('rapid creation - potential collision', () => {
      // In a tight loop, Date.now() might be the same
      // Math.random() provides uniqueness, but let's verify
      const ids = new Set<string>();
      const collisions: string[] = [];
      
      for (let i = 0; i < 10000; i++) {
        const kf = createKeyframe(i, i);
        if (ids.has(kf.id)) {
          collisions.push(kf.id);
        }
        ids.add(kf.id);
      }
      
      // Should have no collisions
      expect(collisions.length).toBe(0);
      expect(ids.size).toBe(10000);
    });
  });
});
