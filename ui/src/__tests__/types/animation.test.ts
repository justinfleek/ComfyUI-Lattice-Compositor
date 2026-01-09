/**
 * AUDIT: animation.ts - Core animation type definitions and factory functions
 * Lines: 172
 * Exports: 12 (10 types/interfaces, 2 functions)
 * Functions to test: createAnimatableProperty, createKeyframe
 * 
 * This file defines the foundational types for ALL animations in the system.
 * EVERY animated property uses AnimatableProperty<T>.
 * EVERY keyframe uses Keyframe<T>.
 */

import { describe, test, expect } from 'vitest';
import {
  createAnimatableProperty,
  createKeyframe,
  type AnimatableProperty,
  type Keyframe,
  type PropertyExpression,
  type BezierHandle,
  type ControlMode,
  type BaseInterpolationType,
  type EasingType,
  type InterpolationType,
  type PropertyValue,
  type ClipboardKeyframe,
} from '@/types/animation';

// ============================================================
// createAnimatableProperty TESTS
// ============================================================

describe('createAnimatableProperty', () => {
  // BASIC FUNCTIONALITY
  describe('basic functionality', () => {
    test('creates property with required fields', () => {
      const prop = createAnimatableProperty('testProp', 42);
      
      expect(prop.name).toBe('testProp');
      expect(prop.value).toBe(42);
      expect(prop.type).toBe('number'); // default
      expect(prop.animated).toBe(false);
      expect(prop.keyframes).toEqual([]);
      expect(prop.group).toBeUndefined();
    });

    test('creates property with all parameters', () => {
      const prop = createAnimatableProperty('position', { x: 10, y: 20 }, 'position', 'Transform');
      
      expect(prop.name).toBe('position');
      expect(prop.value).toEqual({ x: 10, y: 20 });
      expect(prop.type).toBe('position');
      expect(prop.group).toBe('Transform');
    });

    test('id starts with prop_ prefix', () => {
      const prop = createAnimatableProperty('test', 0);
      expect(prop.id.startsWith('prop_')).toBe(true);
    });

    test('id contains property name', () => {
      const prop = createAnimatableProperty('myProperty', 0);
      expect(prop.id).toContain('myProperty');
    });
  });

  // ALL SUPPORTED TYPES
  describe('type parameter variations', () => {
    test('type: number (default)', () => {
      const prop = createAnimatableProperty('opacity', 100);
      expect(prop.type).toBe('number');
    });

    test('type: number (explicit)', () => {
      const prop = createAnimatableProperty('rotation', 45, 'number');
      expect(prop.type).toBe('number');
    });

    test('type: position', () => {
      const prop = createAnimatableProperty('pos', { x: 0, y: 0 }, 'position');
      expect(prop.type).toBe('position');
    });

    test('type: color', () => {
      const prop = createAnimatableProperty('fill', '#ff0000', 'color');
      expect(prop.type).toBe('color');
    });

    test('type: enum', () => {
      const prop = createAnimatableProperty('blendMode', 'normal', 'enum');
      expect(prop.type).toBe('enum');
    });

    test('type: vector3', () => {
      const prop = createAnimatableProperty('orientation', { x: 0, y: 0, z: 0 }, 'vector3');
      expect(prop.type).toBe('vector3');
    });
  });

  // VALUE TYPES
  describe('value type variations', () => {
    test('number value', () => {
      const prop = createAnimatableProperty<number>('opacity', 50);
      expect(typeof prop.value).toBe('number');
      expect(prop.value).toBe(50);
    });

    test('string value (hex color)', () => {
      const prop = createAnimatableProperty<string>('color', '#ff00ff', 'color');
      expect(typeof prop.value).toBe('string');
      expect(prop.value).toBe('#ff00ff');
    });

    test('Vec2 value', () => {
      const prop = createAnimatableProperty('scale', { x: 100, y: 100 }, 'position');
      expect(prop.value).toEqual({ x: 100, y: 100 });
    });

    test('Vec3 value', () => {
      const prop = createAnimatableProperty('position3d', { x: 0, y: 0, z: 0 }, 'vector3');
      expect(prop.value).toEqual({ x: 0, y: 0, z: 0 });
    });

    test('RGBA value', () => {
      const prop = createAnimatableProperty('color', { r: 255, g: 0, b: 0, a: 1 }, 'color');
      expect(prop.value).toEqual({ r: 255, g: 0, b: 0, a: 1 });
    });
  });

  // EDGE CASES - BOUNDARY VALUES
  describe('boundary values', () => {
    test('value: 0', () => {
      const prop = createAnimatableProperty('zero', 0);
      expect(prop.value).toBe(0);
    });

    test('value: 1', () => {
      const prop = createAnimatableProperty('one', 1);
      expect(prop.value).toBe(1);
    });

    test('value: -1', () => {
      const prop = createAnimatableProperty('negOne', -1);
      expect(prop.value).toBe(-1);
    });

    test('value: -0 (preserves -0, which === 0 in JS)', () => {
      const prop = createAnimatableProperty('negZero', -0);
      // -0 === 0 in standard JS equality, but Object.is distinguishes them
      // This is NOT a bug - the value is preserved correctly
      expect(prop.value === 0).toBe(true); // Standard equality
      expect(Object.is(prop.value, -0)).toBe(true); // Value is preserved as -0
    });

    test('value: large positive', () => {
      const prop = createAnimatableProperty('large', 1e10);
      expect(prop.value).toBe(1e10);
    });

    test('value: large negative', () => {
      const prop = createAnimatableProperty('largeNeg', -1e10);
      expect(prop.value).toBe(-1e10);
    });

    test('value: very small positive', () => {
      const prop = createAnimatableProperty('tiny', 1e-10);
      expect(prop.value).toBeCloseTo(1e-10, 15);
    });

    test('value: MAX_SAFE_INTEGER', () => {
      const prop = createAnimatableProperty('max', Number.MAX_SAFE_INTEGER);
      expect(prop.value).toBe(Number.MAX_SAFE_INTEGER);
    });

    test('value: MIN_SAFE_INTEGER', () => {
      const prop = createAnimatableProperty('min', Number.MIN_SAFE_INTEGER);
      expect(prop.value).toBe(Number.MIN_SAFE_INTEGER);
    });
  });

  // EDGE CASES - SPECIAL FLOATS
  describe('special float values', () => {
    test('value: NaN (preserves NaN)', () => {
      const prop = createAnimatableProperty('nan', NaN);
      expect(Number.isNaN(prop.value)).toBe(true);
    });

    test('value: Infinity', () => {
      const prop = createAnimatableProperty('inf', Infinity);
      expect(prop.value).toBe(Infinity);
    });

    test('value: -Infinity', () => {
      const prop = createAnimatableProperty('negInf', -Infinity);
      expect(prop.value).toBe(-Infinity);
    });
  });

  // EDGE CASES - EMPTY/NULL VALUES
  describe('empty and special string values', () => {
    test('name: empty string', () => {
      const prop = createAnimatableProperty('', 0);
      expect(prop.name).toBe('');
      expect(prop.id).toContain('prop_');
    });

    test('name: whitespace only', () => {
      const prop = createAnimatableProperty('   ', 0);
      expect(prop.name).toBe('   ');
    });

    test('name: special characters', () => {
      const prop = createAnimatableProperty('test-prop_123.value', 0);
      expect(prop.name).toBe('test-prop_123.value');
    });

    test('name: unicode characters', () => {
      const prop = createAnimatableProperty('位置', { x: 0, y: 0 }, 'position');
      expect(prop.name).toBe('位置');
    });

    test('value: empty string', () => {
      const prop = createAnimatableProperty<string>('empty', '', 'enum');
      expect(prop.value).toBe('');
    });

    test('value: null (stores null)', () => {
      const prop = createAnimatableProperty('nullable', null as any);
      expect(prop.value).toBeNull();
    });

    test('value: undefined (stores undefined)', () => {
      const prop = createAnimatableProperty('undef', undefined as any);
      expect(prop.value).toBeUndefined();
    });

    test('value: empty object', () => {
      const prop = createAnimatableProperty('emptyObj', {});
      expect(prop.value).toEqual({});
    });

    test('value: empty array', () => {
      const prop = createAnimatableProperty('emptyArr', []);
      expect(prop.value).toEqual([]);
    });
  });

  // ID UNIQUENESS
  describe('ID generation', () => {
    test('creates unique IDs for same inputs', () => {
      const ids = new Set<string>();
      for (let i = 0; i < 100; i++) {
        const prop = createAnimatableProperty('test', 0);
        ids.add(prop.id);
      }
      // Should have 100 unique IDs
      expect(ids.size).toBe(100);
    });

    test('ID format: prop_name_timestamp_random', () => {
      const prop = createAnimatableProperty('myProp', 0);
      // ID should match pattern: prop_name_timestamp_random
      expect(prop.id).toMatch(/^prop_myProp_\d+_[a-z0-9]+$/);
    });
  });

  // RETURN TYPE CONTRACT
  describe('return type contract', () => {
    test('returns object with all required fields', () => {
      const prop = createAnimatableProperty('test', 42);
      
      // All required fields from AnimatableProperty<T>
      expect(prop).toHaveProperty('id');
      expect(prop).toHaveProperty('name');
      expect(prop).toHaveProperty('type');
      expect(prop).toHaveProperty('value');
      expect(prop).toHaveProperty('animated');
      expect(prop).toHaveProperty('keyframes');
    });

    test('keyframes is always an empty array initially', () => {
      const prop = createAnimatableProperty('test', 0);
      expect(Array.isArray(prop.keyframes)).toBe(true);
      expect(prop.keyframes.length).toBe(0);
    });

    test('animated is always false initially', () => {
      const prop = createAnimatableProperty('test', 0);
      expect(prop.animated).toBe(false);
    });

    test('expression is undefined by default', () => {
      const prop = createAnimatableProperty('test', 0);
      expect(prop.expression).toBeUndefined();
    });
  });

  // GROUP PARAMETER
  describe('group parameter', () => {
    test('undefined group when not provided', () => {
      const prop = createAnimatableProperty('test', 0);
      expect(prop.group).toBeUndefined();
    });

    test('group: Transform', () => {
      const prop = createAnimatableProperty('position', { x: 0, y: 0 }, 'position', 'Transform');
      expect(prop.group).toBe('Transform');
    });

    test('group: Text', () => {
      const prop = createAnimatableProperty('fontSize', 24, 'number', 'Text');
      expect(prop.group).toBe('Text');
    });

    test('group: More Options', () => {
      const prop = createAnimatableProperty('motionBlur', 0, 'number', 'More Options');
      expect(prop.group).toBe('More Options');
    });

    test('group: empty string', () => {
      const prop = createAnimatableProperty('test', 0, 'number', '');
      expect(prop.group).toBe('');
    });
  });
});

// ============================================================
// createKeyframe TESTS
// ============================================================

describe('createKeyframe', () => {
  // BASIC FUNCTIONALITY
  describe('basic functionality', () => {
    test('creates keyframe with required fields', () => {
      const kf = createKeyframe(0, 100);
      
      expect(kf.frame).toBe(0);
      expect(kf.value).toBe(100);
      expect(kf.interpolation).toBe('linear'); // default
    });

    test('creates keyframe with all parameters', () => {
      const kf = createKeyframe(30, 50, 'bezier');
      
      expect(kf.frame).toBe(30);
      expect(kf.value).toBe(50);
      expect(kf.interpolation).toBe('bezier');
    });

    test('id starts with kf_ prefix', () => {
      const kf = createKeyframe(0, 0);
      expect(kf.id.startsWith('kf_')).toBe(true);
    });

    test('id contains frame number', () => {
      const kf = createKeyframe(42, 0);
      expect(kf.id).toContain('42');
    });
  });

  // INTERPOLATION TYPES
  describe('interpolation types', () => {
    // Base types
    test('interpolation: linear (default)', () => {
      const kf = createKeyframe(0, 0);
      expect(kf.interpolation).toBe('linear');
    });

    test('interpolation: linear (explicit)', () => {
      const kf = createKeyframe(0, 0, 'linear');
      expect(kf.interpolation).toBe('linear');
    });

    test('interpolation: bezier', () => {
      const kf = createKeyframe(0, 0, 'bezier');
      expect(kf.interpolation).toBe('bezier');
    });

    test('interpolation: hold', () => {
      const kf = createKeyframe(0, 0, 'hold');
      expect(kf.interpolation).toBe('hold');
    });

    // Easing functions (all 30)
    const easingTypes: EasingType[] = [
      'easeInSine', 'easeOutSine', 'easeInOutSine',
      'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
      'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
      'easeInQuart', 'easeOutQuart', 'easeInOutQuart',
      'easeInQuint', 'easeOutQuint', 'easeInOutQuint',
      'easeInExpo', 'easeOutExpo', 'easeInOutExpo',
      'easeInCirc', 'easeOutCirc', 'easeInOutCirc',
      'easeInBack', 'easeOutBack', 'easeInOutBack',
      'easeInElastic', 'easeOutElastic', 'easeInOutElastic',
      'easeInBounce', 'easeOutBounce', 'easeInOutBounce',
    ];

    test.each(easingTypes)('interpolation: %s', (easing) => {
      const kf = createKeyframe(0, 0, easing);
      expect(kf.interpolation).toBe(easing);
    });
  });

  // DEFAULT BEZIER HANDLES
  describe('default bezier handles', () => {
    test('inHandle has correct defaults', () => {
      const kf = createKeyframe(0, 0);
      expect(kf.inHandle).toEqual({
        frame: -5,
        value: 0,
        enabled: true,
      });
    });

    test('outHandle has correct defaults', () => {
      const kf = createKeyframe(0, 0);
      expect(kf.outHandle).toEqual({
        frame: 5,
        value: 0,
        enabled: true,
      });
    });

    test('controlMode defaults to smooth', () => {
      const kf = createKeyframe(0, 0);
      expect(kf.controlMode).toBe('smooth');
    });
  });

  // FRAME VALUES (BOUNDARY)
  describe('frame boundary values', () => {
    test('frame: 0 (first frame)', () => {
      const kf = createKeyframe(0, 100);
      expect(kf.frame).toBe(0);
    });

    test('frame: 1', () => {
      const kf = createKeyframe(1, 100);
      expect(kf.frame).toBe(1);
    });

    test('frame: -1 (negative)', () => {
      const kf = createKeyframe(-1, 100);
      expect(kf.frame).toBe(-1);
    });

    test('frame: 80 (standard composition end)', () => {
      const kf = createKeyframe(80, 100);
      expect(kf.frame).toBe(80);
    });

    test('frame: 10000 (very long composition)', () => {
      const kf = createKeyframe(10000, 100);
      expect(kf.frame).toBe(10000);
    });

    test('frame: 0.5 (fractional frame)', () => {
      const kf = createKeyframe(0.5, 100);
      expect(kf.frame).toBe(0.5);
    });

    test('frame: 29.97 (NTSC timecode)', () => {
      const kf = createKeyframe(29.97, 100);
      expect(kf.frame).toBeCloseTo(29.97, 5);
    });
  });

  // VALUE TYPES
  describe('value type variations', () => {
    test('number value', () => {
      const kf = createKeyframe<number>(0, 42);
      expect(kf.value).toBe(42);
    });

    test('string value (hex color)', () => {
      const kf = createKeyframe<string>(0, '#ff0000');
      expect(kf.value).toBe('#ff0000');
    });

    test('Vec2 value', () => {
      const kf = createKeyframe(0, { x: 100, y: 200 });
      expect(kf.value).toEqual({ x: 100, y: 200 });
    });

    test('Vec3 value', () => {
      const kf = createKeyframe(0, { x: 0, y: 0, z: 100 });
      expect(kf.value).toEqual({ x: 0, y: 0, z: 100 });
    });

    test('RGBA value', () => {
      const kf = createKeyframe(0, { r: 255, g: 128, b: 0, a: 0.5 });
      expect(kf.value).toEqual({ r: 255, g: 128, b: 0, a: 0.5 });
    });
  });

  // SPECIAL FLOAT VALUES - VALIDATION
  describe('special float values - validation', () => {
    test('frame: NaN throws error (prevents silent interpolation failure)', () => {
      expect(() => createKeyframe(NaN, 0)).toThrow('Invalid keyframe frame');
    });

    test('frame: Infinity throws error', () => {
      expect(() => createKeyframe(Infinity, 0)).toThrow('Invalid keyframe frame');
    });

    test('frame: -Infinity throws error', () => {
      expect(() => createKeyframe(-Infinity, 0)).toThrow('Invalid keyframe frame');
    });

    test('value: NaN', () => {
      const kf = createKeyframe<number>(0, NaN);
      expect(Number.isNaN(kf.value)).toBe(true);
    });

    test('value: Infinity', () => {
      const kf = createKeyframe<number>(0, Infinity);
      expect(kf.value).toBe(Infinity);
    });

    test('value: -0 (preserves -0, which === 0 in JS)', () => {
      const kf = createKeyframe(0, -0);
      // -0 === 0 in standard JS equality, but Object.is distinguishes them
      // This is NOT a bug - the value is preserved correctly
      expect(kf.value === 0).toBe(true); // Standard equality
      expect(Object.is(kf.value, -0)).toBe(true); // Value is preserved as -0
    });
  });

  // ID UNIQUENESS
  describe('ID generation', () => {
    test('creates unique IDs for same inputs', () => {
      const ids = new Set<string>();
      for (let i = 0; i < 100; i++) {
        const kf = createKeyframe(0, 0);
        ids.add(kf.id);
      }
      expect(ids.size).toBe(100);
    });

    test('ID format: kf_frame_timestamp_random', () => {
      const kf = createKeyframe(42, 0);
      expect(kf.id).toMatch(/^kf_42_\d+_[a-z0-9]+$/);
    });
  });

  // RETURN TYPE CONTRACT
  describe('return type contract', () => {
    test('returns object with all required fields', () => {
      const kf = createKeyframe(0, 0);
      
      expect(kf).toHaveProperty('id');
      expect(kf).toHaveProperty('frame');
      expect(kf).toHaveProperty('value');
      expect(kf).toHaveProperty('interpolation');
      expect(kf).toHaveProperty('inHandle');
      expect(kf).toHaveProperty('outHandle');
      expect(kf).toHaveProperty('controlMode');
    });

    test('does NOT have spatial tangents by default', () => {
      const kf = createKeyframe(0, 0);
      expect(kf.spatialInTangent).toBeUndefined();
      expect(kf.spatialOutTangent).toBeUndefined();
    });
  });

  // EMPTY/NULL VALUES
  describe('empty and null values', () => {
    test('value: null', () => {
      const kf = createKeyframe(0, null as any);
      expect(kf.value).toBeNull();
    });

    test('value: undefined', () => {
      const kf = createKeyframe(0, undefined as any);
      expect(kf.value).toBeUndefined();
    });

    test('value: empty object', () => {
      const kf = createKeyframe(0, {});
      expect(kf.value).toEqual({});
    });

    test('value: empty string', () => {
      const kf = createKeyframe<string>(0, '');
      expect(kf.value).toBe('');
    });
  });
});

// ============================================================
// TYPE DEFINITIONS VALIDATION
// ============================================================

describe('Type definitions (compile-time validation)', () => {
  // These tests verify the types exist and can be used
  // They won't catch runtime bugs but ensure interface compliance

  test('AnimatableProperty interface structure', () => {
    const prop: AnimatableProperty<number> = {
      id: 'test',
      name: 'test',
      type: 'number',
      value: 0,
      animated: false,
      keyframes: [],
    };
    expect(prop.id).toBe('test');
  });

  test('PropertyExpression interface structure', () => {
    const expr: PropertyExpression = {
      enabled: true,
      type: 'preset',
      name: 'jitter',
      params: { amplitude: 10, frequency: 1 },
    };
    expect(expr.enabled).toBe(true);
    expect(expr.type).toBe('preset');
  });

  test('Keyframe interface structure', () => {
    const kf: Keyframe<number> = {
      id: 'kf1',
      frame: 0,
      value: 100,
      interpolation: 'linear',
      inHandle: { frame: -5, value: 0, enabled: true },
      outHandle: { frame: 5, value: 0, enabled: true },
      controlMode: 'smooth',
    };
    expect(kf.frame).toBe(0);
  });

  test('BezierHandle interface structure', () => {
    const handle: BezierHandle = {
      frame: -5,
      value: 10,
      enabled: true,
    };
    expect(handle.frame).toBe(-5);
    expect(handle.enabled).toBe(true);
  });

  test('ControlMode type values', () => {
    const modes: ControlMode[] = ['symmetric', 'smooth', 'corner'];
    expect(modes.length).toBe(3);
  });

  test('BaseInterpolationType values', () => {
    const types: BaseInterpolationType[] = ['linear', 'bezier', 'hold'];
    expect(types.length).toBe(3);
  });

  test('PropertyValue can be number', () => {
    const val: PropertyValue = 42;
    expect(val).toBe(42);
  });

  test('PropertyValue can be string', () => {
    const val: PropertyValue = '#ff0000';
    expect(val).toBe('#ff0000');
  });

  test('PropertyValue can be Vec2', () => {
    const val: PropertyValue = { x: 10, y: 20 };
    expect(val).toEqual({ x: 10, y: 20 });
  });

  test('PropertyValue can be Vec3', () => {
    const val: PropertyValue = { x: 0, y: 0, z: 100 };
    expect(val).toEqual({ x: 0, y: 0, z: 100 });
  });

  test('PropertyValue can be RGBA', () => {
    const val: PropertyValue = { r: 255, g: 0, b: 0, a: 1 };
    expect(val).toEqual({ r: 255, g: 0, b: 0, a: 1 });
  });

  test('ClipboardKeyframe structure', () => {
    const clip: ClipboardKeyframe = {
      layerId: 'layer_1',
      propertyPath: 'transform.position',
      keyframes: [],
    };
    expect(clip.layerId).toBe('layer_1');
    expect(clip.propertyPath).toBe('transform.position');
  });
});
