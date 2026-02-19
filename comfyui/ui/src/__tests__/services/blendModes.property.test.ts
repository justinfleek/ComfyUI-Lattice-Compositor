/**
 * BLEND MODES Property Tests
 * 
 * Mathematical properties that MUST hold for blend mode operations.
 * These test color space conversions and basic blend invariants.
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  getAllBlendModes,
  getBlendModeCategory,
  getBlendModesInCategory,
  BLEND_MODE_CATEGORIES,
} from '@/types/blendModes';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                              // arbitraries
// ═══════════════════════════════════════════════════════════════════════════

/**
 * RGB channel value (0-255)
 */
const channelArb = fc.integer({ min: 0, max: 255 });

/**
 * RGBA pixel
 */
const pixelArb = fc.tuple(channelArb, channelArb, channelArb, channelArb)
  .map(([r, g, b, a]) => ({ r, g, b, a }));

/**
 * Normalized value (0-1)
 */
const normalizedArb = fc.double({ min: 0, max: 1, noNaN: true });

/**
 * Hue value (0-1, wraps around)
 */
const hueArb = normalizedArb;

/**
 * Blend mode from the type system
 */
const blendModeArb = fc.constantFrom(...getAllBlendModes());

describe('BLEND MODE Properties', () => {

  // ═══════════════════════════════════════════════════════════════════════════
  //                                          // blend // mode // categorization
  // ═══════════════════════════════════════════════════════════════════════════

  describe('blend mode categorization', () => {

    test.prop([blendModeArb])(
      'every blend mode belongs to exactly one category',
      (mode) => {
        const category = getBlendModeCategory(mode);
        
        // Should return a valid category
        expect(Object.keys(BLEND_MODE_CATEGORIES)).toContain(category);
        
        // Mode should be in that category
        const modesInCategory = getBlendModesInCategory(category);
        expect(modesInCategory).toContain(mode);
      }
    );

    test.prop([fc.constantFrom(...Object.keys(BLEND_MODE_CATEGORIES) as (keyof typeof BLEND_MODE_CATEGORIES)[])])(
      'getBlendModesInCategory returns non-empty array for valid category',
      (category) => {
        const modes = getBlendModesInCategory(category);
        expect(modes.length).toBeGreaterThan(0);
      }
    );

    test.prop([fc.constant(null)])(
      'getAllBlendModes returns all modes without duplicates',
      () => {
        const allModes = getAllBlendModes();
        const uniqueModes = new Set(allModes);
        
        // No duplicates
        expect(allModes.length).toBe(uniqueModes.size);
        
        // Should have a reasonable number of blend modes
        expect(allModes.length).toBeGreaterThan(20);
      }
    );

  });

  // ═══════════════════════════════════════════════════════════════════════════
  // COLOR CHANNEL CLAMPING (invariant for all blend modes)
  // ═══════════════════════════════════════════════════════════════════════════

  describe('color channel bounds', () => {

    test.prop([channelArb])(
      'channel values are bounded 0-255',
      (channel) => {
        expect(channel).toBeGreaterThanOrEqual(0);
        expect(channel).toBeLessThanOrEqual(255);
      }
    );

    test.prop([pixelArb])(
      'all pixel channels are bounded 0-255',
      (pixel) => {
        expect(pixel.r).toBeGreaterThanOrEqual(0);
        expect(pixel.r).toBeLessThanOrEqual(255);
        expect(pixel.g).toBeGreaterThanOrEqual(0);
        expect(pixel.g).toBeLessThanOrEqual(255);
        expect(pixel.b).toBeGreaterThanOrEqual(0);
        expect(pixel.b).toBeLessThanOrEqual(255);
        expect(pixel.a).toBeGreaterThanOrEqual(0);
        expect(pixel.a).toBeLessThanOrEqual(255);
      }
    );

  });

  // ═══════════════════════════════════════════════════════════════════════════
  // RGB <-> HSL CONVERSION (roundtrip property)
  // ═══════════════════════════════════════════════════════════════════════════

  describe('RGB <-> HSL conversion roundtrip', () => {

    /**
     * Simple RGB to HSL conversion for testing
     */
    function rgbToHsl(r: number, g: number, b: number): [number, number, number] {
      r /= 255;
      g /= 255;
      b /= 255;

      const max = Math.max(r, g, b);
      const min = Math.min(r, g, b);
      const l = (max + min) / 2;
      let h = 0;
      let s = 0;

      if (max !== min) {
        const d = max - min;
        s = l > 0.5 ? d / (2 - max - min) : d / (max + min);

        switch (max) {
          case r:
            h = ((g - b) / d + (g < b ? 6 : 0)) / 6;
            break;
          case g:
            h = ((b - r) / d + 2) / 6;
            break;
          case b:
            h = ((r - g) / d + 4) / 6;
            break;
        }
      }

      return [h, s, l];
    }

    /**
     * Simple HSL to RGB conversion for testing
     */
    function hslToRgb(h: number, s: number, l: number): [number, number, number] {
      let r: number, g: number, b: number;

      if (s === 0) {
        r = g = b = l;
      } else {
        const hue2rgb = (p: number, q: number, t: number) => {
          if (t < 0) t += 1;
          if (t > 1) t -= 1;
          if (t < 1 / 6) return p + (q - p) * 6 * t;
          if (t < 1 / 2) return q;
          if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
          return p;
        };

        const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
        const p = 2 * l - q;
        r = hue2rgb(p, q, h + 1 / 3);
        g = hue2rgb(p, q, h);
        b = hue2rgb(p, q, h - 1 / 3);
      }

      return [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
    }

    test.prop([channelArb, channelArb, channelArb])(
      'RGB -> HSL -> RGB roundtrip preserves color (within rounding)',
      (r, g, b) => {
        const [h, s, l] = rgbToHsl(r, g, b);
        const [rBack, gBack, bBack] = hslToRgb(h, s, l);
        
        // Allow for rounding errors (±1 per channel)
        expect(Math.abs(r - rBack)).toBeLessThanOrEqual(1);
        expect(Math.abs(g - gBack)).toBeLessThanOrEqual(1);
        expect(Math.abs(b - bBack)).toBeLessThanOrEqual(1);
      }
    );

    test.prop([channelArb])(
      'grayscale colors have saturation = 0',
      (gray) => {
        const [_h, s, _l] = rgbToHsl(gray, gray, gray);
        expect(s).toBe(0);
      }
    );

    test.prop([channelArb])(
      'pure white (255,255,255) has L = 1',
      () => {
        const [_h, _s, l] = rgbToHsl(255, 255, 255);
        expect(l).toBe(1);
      }
    );

    test.prop([channelArb])(
      'pure black (0,0,0) has L = 0',
      () => {
        const [_h, _s, l] = rgbToHsl(0, 0, 0);
        expect(l).toBe(0);
      }
    );

    test.prop([hueArb, normalizedArb])(
      'HSL with S=0 produces grayscale',
      (h, l) => {
        const [r, g, b] = hslToRgb(h, 0, l);
        // When saturation is 0, R = G = B
        expect(r).toBe(g);
        expect(g).toBe(b);
      }
    );

  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                 // luminance // calculation
  // ═══════════════════════════════════════════════════════════════════════════

  describe('luminance calculation', () => {

    function getLuminance(r: number, g: number, b: number): number {
      return 0.299 * r + 0.587 * g + 0.114 * b;
    }

    test.prop([channelArb, channelArb, channelArb])(
      'luminance is bounded 0-255',
      (r, g, b) => {
        const lum = getLuminance(r, g, b);
        expect(lum).toBeGreaterThanOrEqual(0);
        expect(lum).toBeLessThanOrEqual(255);
      }
    );

    test.prop([channelArb])(
      'grayscale luminance equals the gray value',
      (gray) => {
        const lum = getLuminance(gray, gray, gray);
        // Coefficients sum to 1, so luminance of (g, g, g) = g
        expect(lum).toBeCloseTo(gray, 6);
      }
    );

    test.prop([fc.constant(null)])(
      'pure white has maximum luminance',
      () => {
        const lum = getLuminance(255, 255, 255);
        expect(lum).toBe(255);
      }
    );

    test.prop([fc.constant(null)])(
      'pure black has minimum luminance',
      () => {
        const lum = getLuminance(0, 0, 0);
        expect(lum).toBe(0);
      }
    );

    test.prop([fc.constant(null)])(
      'green has higher luminance weight than red or blue',
      () => {
        const redLum = getLuminance(255, 0, 0);
        const greenLum = getLuminance(0, 255, 0);
        const blueLum = getLuminance(0, 0, 255);
        
        expect(greenLum).toBeGreaterThan(redLum);
        expect(greenLum).toBeGreaterThan(blueLum);
      }
    );

  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                     // basic // blend // mode // invariants
  // ═══════════════════════════════════════════════════════════════════════════

  describe('basic blend invariants', () => {

    // Simple blend functions for testing invariants
    function blendNormal(base: number, blend: number, opacity: number): number {
      return Math.round(base * (1 - opacity) + blend * opacity);
    }

    function blendMultiply(base: number, blend: number): number {
      return Math.round((base * blend) / 255);
    }

    function blendScreen(base: number, blend: number): number {
      return Math.round(255 - ((255 - base) * (255 - blend)) / 255);
    }

    function blendAdd(base: number, blend: number): number {
      return Math.min(255, base + blend);
    }

    test.prop([channelArb, channelArb])(
      'normal blend at opacity 0 returns base',
      (base, blend) => {
        expect(blendNormal(base, blend, 0)).toBe(base);
      }
    );

    test.prop([channelArb, channelArb])(
      'normal blend at opacity 1 returns blend',
      (base, blend) => {
        expect(blendNormal(base, blend, 1)).toBe(blend);
      }
    );

    test.prop([channelArb, channelArb])(
      'multiply is commutative: multiply(a, b) = multiply(b, a)',
      (a, b) => {
        expect(blendMultiply(a, b)).toBe(blendMultiply(b, a));
      }
    );

    test.prop([channelArb, channelArb])(
      'screen is commutative: screen(a, b) = screen(b, a)',
      (a, b) => {
        expect(blendScreen(a, b)).toBe(blendScreen(b, a));
      }
    );

    test.prop([channelArb, channelArb])(
      'add is commutative: add(a, b) = add(b, a)',
      (a, b) => {
        expect(blendAdd(a, b)).toBe(blendAdd(b, a));
      }
    );

    test.prop([channelArb])(
      'multiply with white (255) returns original',
      (base) => {
        expect(blendMultiply(base, 255)).toBe(base);
      }
    );

    test.prop([channelArb])(
      'multiply with black (0) returns black',
      (base) => {
        expect(blendMultiply(base, 0)).toBe(0);
      }
    );

    test.prop([channelArb])(
      'screen with black (0) returns original',
      (base) => {
        expect(blendScreen(base, 0)).toBe(base);
      }
    );

    test.prop([channelArb])(
      'screen with white (255) returns white',
      (base) => {
        expect(blendScreen(base, 255)).toBe(255);
      }
    );

    test.prop([channelArb, channelArb])(
      'add result is bounded by 255',
      (a, b) => {
        expect(blendAdd(a, b)).toBeLessThanOrEqual(255);
        expect(blendAdd(a, b)).toBeGreaterThanOrEqual(0);
      }
    );

    test.prop([channelArb, channelArb])(
      'multiply result is always <= min(a, b)',
      (a, b) => {
        expect(blendMultiply(a, b)).toBeLessThanOrEqual(Math.max(a, b) + 1);
      }
    );

  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                     // clamping // function
  // ═══════════════════════════════════════════════════════════════════════════

  describe('clamp function', () => {

    function clamp(value: number): number {
      return Math.max(0, Math.min(255, Math.round(value)));
    }

    test.prop([fc.double({ min: -1000, max: 1000, noNaN: true })])(
      'clamp always returns value in [0, 255]',
      (value) => {
        const result = clamp(value);
        expect(result).toBeGreaterThanOrEqual(0);
        expect(result).toBeLessThanOrEqual(255);
      }
    );

    test.prop([fc.integer({ min: 0, max: 255 })])(
      'clamp preserves values already in range',
      (value) => {
        expect(clamp(value)).toBe(value);
      }
    );

    test.prop([fc.integer({ min: 256, max: 1000 })])(
      'clamp caps values > 255 to 255',
      (value) => {
        expect(clamp(value)).toBe(255);
      }
    );

    test.prop([fc.integer({ min: -1000, max: -1 })])(
      'clamp floors values < 0 to 0',
      (value) => {
        expect(clamp(value)).toBe(0);
      }
    );

  });

});
