/**
 * REGRESSION TEST: BUG - Malformed Hex Color NaN
 * 
 * @fixed 2026-01-05
 * @file services/interpolation.ts
 * @rootCause Malformed hex colors (e.g., #xyz) caused NaN when parsing hex components
 * @fix Added normalizeHexColor() validation that returns #000000 for invalid formats
 * @counterexample Interpolating between '#xyz' and '#ffffff' produced NaN
 */

import { describe, test, expect } from 'vitest';
import { interpolateProperty } from '@/services/interpolation';
import type { AnimatableProperty } from '@/types/project';

describe('BUG Regression: Malformed Hex Color NaN', () => {
  /**
   * This test MUST reproduce the exact counterexample from the bug report.
   * Before fix: '#xyz' would cause NaN when parsing hex components
   * After fix: '#xyz' is normalized to '#000000' (black)
   */
  test('original counterexample now passes', () => {
    const prop: AnimatableProperty<string> = {
      id: 'test',
      name: 'test',
      type: 'string',
      value: '#000000',
      animated: true,
      keyframes: [
        {
          id: 'kf1',
          frame: 0,
          value: '#xyz', // Malformed hex - should be normalized to #000000
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
        {
          id: 'kf2',
          frame: 100,
          value: '#ffffff',
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
      ],
    };

    // Before fix: This would produce NaN
    // After fix: '#xyz' is normalized to '#000000', so interpolation works correctly
    const result = interpolateProperty(prop, 50, 30);

    // Result should be a valid hex color string (not NaN)
    expect(typeof result).toBe('string');
    expect(result).toMatch(/^#[0-9a-f]{6}$/i);
    
    // Since '#xyz' is normalized to '#000000', interpolating between black and white
    // at t=0.5 should produce gray (#808080)
    expect(result.toLowerCase()).toBe('#808080');
  });

  /**
   * Additional edge cases related to this bug.
   */
  test('other malformed hex formats are handled', () => {
    const malformedHexes = [
      '#xyz',
      '#invalid',
      '#12', // Too short
      '#12345', // Wrong length
      '#1234567', // Wrong length
      '#123456789', // Too long
      'not-a-hex', // No # prefix
      '', // Empty string
    ];

    for (const malformed of malformedHexes) {
      const prop: AnimatableProperty<string> = {
        id: 'test',
        name: 'test',
        type: 'string',
        value: '#000000',
        animated: true,
        keyframes: [
          {
            id: 'kf1',
            frame: 0,
            value: malformed,
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
          {
            id: 'kf2',
            frame: 100,
            value: '#ffffff',
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
        ],
      };

      const result = interpolateProperty(prop, 50, 30);

      // Should never produce NaN or invalid strings
      expect(typeof result).toBe('string');
      expect(result).toMatch(/^#[0-9a-f]{6}$/i);
      expect(result).not.toBe('NaN');
      expect(result).not.toContain('NaN');
    }
  });

  test('malformed hex at end keyframe is handled', () => {
    const prop: AnimatableProperty<string> = {
      id: 'test',
      name: 'test',
      type: 'string',
      value: '#ffffff',
      animated: true,
      keyframes: [
        {
          id: 'kf1',
          frame: 0,
          value: '#ffffff',
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
        {
          id: 'kf2',
          frame: 100,
          value: '#xyz', // Malformed at end
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
      ],
    };

    const result = interpolateProperty(prop, 50, 30);
    expect(typeof result).toBe('string');
    expect(result).toMatch(/^#[0-9a-f]{6}$/i);
  });
});
