/**
 * REGRESSION TEST: BUG - RGBA Hex Color Alpha Lost
 * 
 * @fixed 2026-01-05
 * @file services/interpolation.ts
 * @rootCause 8-char hex colors (#rrggbbaa) were not handled, alpha channel was lost
 * @fix Added 8-char hex alpha interpolation support
 * @counterexample Interpolating between '#00000000' (transparent) and '#ffffffff' (opaque) lost alpha
 */

import { describe, test, expect } from 'vitest';
import { interpolateProperty } from '@/services/interpolation';
import type { AnimatableProperty } from '@/types/project';

describe('BUG Regression: RGBA Hex Color Alpha Lost', () => {
  /**
   * This test MUST reproduce the exact counterexample from the bug report.
   * Before fix: 8-char hex colors (#rrggbbaa) were not recognized, alpha was lost
   * After fix: 8-char hex colors are properly parsed and alpha is interpolated
   */
  test('original counterexample now passes', () => {
    const prop: AnimatableProperty<string> = {
      id: 'test',
      name: 'test',
      type: 'color',
      value: '#00000000',
      animated: true,
      keyframes: [
        {
          id: 'kf1',
          frame: 0,
          value: '#00000000', // Transparent black
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
        {
          id: 'kf2',
          frame: 100,
          value: '#ffffffff', // Opaque white
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
      ],
    };

    // Before fix: Alpha channel would be lost, result would be 6-char hex
    // After fix: Alpha is interpolated, result should be 8-char hex
    const result = interpolateProperty(prop, 50, 30);

    // Result should be a valid 8-char hex color string (with alpha)
    expect(typeof result).toBe('string');
    expect(result).toMatch(/^#[0-9a-f]{8}$/i);
    
    // Interpolating between transparent black and opaque white at t=0.5
    // should produce semi-transparent gray (#80808080)
    expect(result.toLowerCase()).toBe('#80808080');
  });

  /**
   * Additional edge cases related to this bug.
   */
  test('alpha interpolation works correctly', () => {
    const prop: AnimatableProperty<string> = {
      id: 'test',
      name: 'test',
      type: 'color',
      value: '#ff000000',
      animated: true,
      keyframes: [
        {
          id: 'kf1',
          frame: 0,
          value: '#ff000000', // Transparent red
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
        {
          id: 'kf2',
          frame: 100,
          value: '#00ff00ff', // Opaque green
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
      ],
    };

    const result = interpolateProperty(prop, 50, 30);
    expect(typeof result).toBe('string');
    expect(result).toMatch(/^#[0-9a-f]{8}$/i);

    // RGB should interpolate: red (255,0,0) + green (0,255,0) at t=0.5:
    // R: (255 + 0) / 2 = 127.5 ≈ 128 = 0x80
    // G: (0 + 255) / 2 = 127.5 ≈ 128 = 0x80
    // B: (0 + 0) / 2 = 0 = 0x00
    // Alpha should interpolate: 0 + 255 = 127.5 ≈ 128 = 0x80
    expect(result.toLowerCase()).toMatch(/^#80800080$/);
  });

  test('mixed 6-char and 8-char hex works', () => {
    const prop: AnimatableProperty<string> = {
      id: 'test',
      name: 'test',
      type: 'color',
      value: '#000000',
      animated: true,
      keyframes: [
        {
          id: 'kf1',
          frame: 0,
          value: '#000000', // 6-char hex (no alpha, treated as alpha=255)
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
        {
          id: 'kf2',
          frame: 100,
          value: '#ffffff00', // 8-char hex (alpha=0)
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
      ],
    };

    const result = interpolateProperty(prop, 50, 30);
    expect(typeof result).toBe('string');
    // When mixing 6-char and 8-char, result should be 8-char (includes alpha)
    expect(result).toMatch(/^#[0-9a-f]{8}$/i);
  });

  test('short RGBA hex (#rgba) works', () => {
    const prop: AnimatableProperty<string> = {
      id: 'test',
      name: 'test',
      type: 'color',
      value: '#0000',
      animated: true,
      keyframes: [
        {
          id: 'kf1',
          frame: 0,
          value: '#0000', // Short RGBA - should expand to #00000000
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
        {
          id: 'kf2',
          frame: 100,
          value: '#ffff', // Short RGBA - should expand to #ffffffff
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth',
        },
      ],
    };

    const result = interpolateProperty(prop, 50, 30);
    expect(typeof result).toBe('string');
    expect(result).toMatch(/^#[0-9a-f]{8}$/i);
    expect(result.toLowerCase()).toBe('#80808080');
  });
});
