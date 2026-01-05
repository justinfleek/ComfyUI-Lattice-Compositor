/**
 * Custom Arbitraries for Lattice Compositor Property Tests
 * 
 * These generate valid random inputs for property-based testing.
 * Each arbitrary is designed to produce values that match the
 * actual data structures used in the compositor.
 */

import * as fc from 'fast-check';
import type { 
  Keyframe, 
  AnimatableProperty, 
  BezierHandle, 
  InterpolationType,
  PropertyExpression,
  ControlMode
} from '@/types/animation';
import type { Vec2, Vec3, LayerTransform } from '@/types/transform';

// ============================================================================
// BASIC VALUE ARBITRARIES
// ============================================================================

/**
 * Frame number (0-1000 typical range, supports up to 10000)
 */
export const frameArb = fc.integer({ min: 0, max: 10000 });

/**
 * Frame number for typical AI video (0-81 frames, 16fps, ~5 seconds)
 */
export const wanFrameArb = fc.integer({ min: 0, max: 81 });

/**
 * Normalized value (0-1)
 */
export const normalizedArb = fc.double({ min: 0, max: 1, noNaN: true });

/**
 * Percentage (0-100)
 */
export const percentArb = fc.double({ min: 0, max: 100, noNaN: true });

/**
 * Opacity value (0-100, commonly used)
 */
export const opacityArb = fc.double({ min: 0, max: 100, noNaN: true });

/**
 * Rotation in degrees (-360 to 360)
 */
export const rotationArb = fc.double({ min: -360, max: 360, noNaN: true });

/**
 * Scale value (0.01 to 10, typical range)
 */
export const scaleArb = fc.double({ min: 0.01, max: 10, noNaN: true });

/**
 * Position value (typically -10000 to 10000)
 */
export const positionValueArb = fc.double({ min: -10000, max: 10000, noNaN: true });

/**
 * Small position value for testing (more manageable range)
 */
export const smallPositionArb = fc.double({ min: -1000, max: 1000, noNaN: true });

// ============================================================================
// VECTOR ARBITRARIES
// ============================================================================

/**
 * 2D Vector
 */
export const vec2Arb: fc.Arbitrary<Vec2> = fc.record({
  x: positionValueArb,
  y: positionValueArb,
});

/**
 * 3D Vector
 */
export const vec3Arb: fc.Arbitrary<Vec3> = fc.record({
  x: positionValueArb,
  y: positionValueArb,
  z: positionValueArb,
});

/**
 * Small 2D Vector (for testing)
 */
export const smallVec2Arb: fc.Arbitrary<Vec2> = fc.record({
  x: smallPositionArb,
  y: smallPositionArb,
});

// ============================================================================
// COLOR ARBITRARIES
// ============================================================================

/**
 * Hex color string (#RRGGBB)
 */
export const hexColorArb = fc.tuple(
  fc.integer({ min: 0, max: 255 }),
  fc.integer({ min: 0, max: 255 }),
  fc.integer({ min: 0, max: 255 })
).map(([r, g, b]) => 
  `#${r.toString(16).padStart(2, '0')}${g.toString(16).padStart(2, '0')}${b.toString(16).padStart(2, '0')}`
);

/**
 * RGBA color object
 */
export const rgbaArb = fc.record({
  r: fc.integer({ min: 0, max: 255 }),
  g: fc.integer({ min: 0, max: 255 }),
  b: fc.integer({ min: 0, max: 255 }),
  a: fc.double({ min: 0, max: 1, noNaN: true }),
});

// ============================================================================
// BEZIER HANDLE ARBITRARIES
// ============================================================================

/**
 * Bezier handle for keyframe curves
 */
export const bezierHandleArb: fc.Arbitrary<BezierHandle> = fc.record({
  frame: fc.double({ min: -50, max: 50, noNaN: true }),
  value: fc.double({ min: -100, max: 100, noNaN: true }),
  enabled: fc.boolean(),
});

/**
 * Bezier handle that's always enabled (more common case)
 */
export const enabledBezierHandleArb: fc.Arbitrary<BezierHandle> = fc.record({
  frame: fc.double({ min: -50, max: 50, noNaN: true }),
  value: fc.double({ min: -100, max: 100, noNaN: true }),
  enabled: fc.constant(true),
});

// ============================================================================
// INTERPOLATION TYPE ARBITRARIES
// ============================================================================

/**
 * Base interpolation types
 */
export const baseInterpolationArb = fc.constantFrom<InterpolationType>(
  'linear', 'bezier', 'hold'
);

/**
 * Easing interpolation types
 */
export const easingInterpolationArb = fc.constantFrom<InterpolationType>(
  'easeInSine', 'easeOutSine', 'easeInOutSine',
  'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
  'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
  'easeInQuart', 'easeOutQuart', 'easeInOutQuart',
  'easeInQuint', 'easeOutQuint', 'easeInOutQuint',
  'easeInExpo', 'easeOutExpo', 'easeInOutExpo',
  'easeInCirc', 'easeOutCirc', 'easeInOutCirc',
  'easeInBack', 'easeOutBack', 'easeInOutBack',
  'easeInElastic', 'easeOutElastic', 'easeInOutElastic',
  'easeInBounce', 'easeOutBounce', 'easeInOutBounce'
);

/**
 * Any interpolation type
 */
export const interpolationTypeArb = fc.oneof(
  baseInterpolationArb,
  easingInterpolationArb
);

/**
 * Control mode for bezier handles
 */
export const controlModeArb = fc.constantFrom<ControlMode>(
  'symmetric', 'smooth', 'corner'
);

// ============================================================================
// KEYFRAME ARBITRARIES
// ============================================================================

/**
 * Generate a unique ID
 */
const idArb = fc.string({ minLength: 8, maxLength: 12, unit: 'grapheme' })
  .map(s => `kf_${s.replace(/[^a-zA-Z0-9]/g, 'x')}`);

/**
 * Numeric keyframe
 */
export const numericKeyframeArb: fc.Arbitrary<Keyframe<number>> = fc.record({
  id: idArb,
  frame: frameArb,
  value: fc.double({ min: -1000, max: 1000, noNaN: true }),
  interpolation: interpolationTypeArb,
  inHandle: bezierHandleArb,
  outHandle: bezierHandleArb,
  controlMode: controlModeArb,
});

/**
 * Position keyframe (2D)
 */
export const positionKeyframeArb: fc.Arbitrary<Keyframe<Vec2>> = fc.record({
  id: idArb,
  frame: frameArb,
  value: smallVec2Arb,
  interpolation: interpolationTypeArb,
  inHandle: bezierHandleArb,
  outHandle: bezierHandleArb,
  controlMode: controlModeArb,
});

/**
 * Generate a sorted array of keyframes (required for interpolation)
 * Ensures frames are unique and sorted ascending
 */
export function sortedKeyframesArb<T>(
  valueArb: fc.Arbitrary<T>,
  minLength: number = 2,
  maxLength: number = 10
): fc.Arbitrary<Keyframe<T>[]> {
  return fc.array(
    fc.record({
      id: idArb,
      frame: frameArb,
      value: valueArb,
      interpolation: interpolationTypeArb,
      inHandle: bezierHandleArb,
      outHandle: bezierHandleArb,
      controlMode: controlModeArb,
    }),
    { minLength, maxLength }
  ).map(keyframes => {
    // Sort by frame and ensure unique frames
    const sorted = [...keyframes].sort((a, b) => a.frame - b.frame);
    const unique: Keyframe<T>[] = [];
    let lastFrame = -1;
    
    for (const kf of sorted) {
      if (kf.frame > lastFrame) {
        unique.push(kf);
        lastFrame = kf.frame;
      }
    }
    
    // Ensure at least minLength keyframes
    while (unique.length < minLength) {
      const newFrame = (unique[unique.length - 1]?.frame ?? 0) + 10;
      unique.push({
        ...keyframes[0],
        id: `kf_pad_${unique.length}`,
        frame: newFrame,
      });
    }
    
    return unique;
  });
}

/**
 * Sorted numeric keyframes (most common case)
 */
export const sortedNumericKeyframesArb = sortedKeyframesArb(
  fc.double({ min: -1000, max: 1000, noNaN: true }),
  2,
  10
);

/**
 * Sorted position keyframes
 */
export const sortedPositionKeyframesArb = sortedKeyframesArb(
  smallVec2Arb,
  2,
  10
);

// ============================================================================
// ANIMATABLE PROPERTY ARBITRARIES
// ============================================================================

/**
 * Property ID generator
 */
const propertyIdArb = fc.string({ minLength: 8, maxLength: 12, unit: 'grapheme' })
  .map(s => `prop_${s.replace(/[^a-zA-Z0-9]/g, 'x')}`);

/**
 * Animated numeric property with keyframes
 */
export const animatedNumericPropertyArb: fc.Arbitrary<AnimatableProperty<number>> = fc.record({
  id: propertyIdArb,
  name: fc.constantFrom('opacity', 'rotation', 'scale', 'blur'),
  type: fc.constant('number' as const),
  value: fc.double({ min: 0, max: 100, noNaN: true }),
  animated: fc.constant(true),
  keyframes: sortedNumericKeyframesArb,
  expression: fc.constant(undefined),
});

/**
 * Static numeric property (no keyframes)
 */
export const staticNumericPropertyArb: fc.Arbitrary<AnimatableProperty<number>> = fc.record({
  id: propertyIdArb,
  name: fc.constantFrom('opacity', 'rotation', 'scale', 'blur'),
  type: fc.constant('number' as const),
  value: fc.double({ min: 0, max: 100, noNaN: true }),
  animated: fc.constant(false),
  keyframes: fc.constant([]),
  expression: fc.constant(undefined),
});

/**
 * Animated position property
 */
export const animatedPositionPropertyArb: fc.Arbitrary<AnimatableProperty<Vec2>> = fc.record({
  id: propertyIdArb,
  name: fc.constant('position'),
  type: fc.constant('position' as const),
  value: smallVec2Arb,
  animated: fc.constant(true),
  keyframes: sortedPositionKeyframesArb,
  expression: fc.constant(undefined),
});

// ============================================================================
// EXPRESSION ARBITRARIES
// ============================================================================

/**
 * Wiggle expression parameters
 */
export const wiggleParamsArb = fc.record({
  frequency: fc.double({ min: 0.1, max: 10, noNaN: true }),
  amplitude: fc.double({ min: 1, max: 100, noNaN: true }),
  octaves: fc.integer({ min: 1, max: 4 }),
  ampMult: fc.double({ min: 0.1, max: 1, noNaN: true }),
  seed: fc.integer({ min: 0, max: 1000000 }),
});

/**
 * Property expression (preset type)
 */
export const presetExpressionArb: fc.Arbitrary<PropertyExpression> = fc.record({
  enabled: fc.boolean(),
  type: fc.constant('preset' as const),
  name: fc.constantFrom('jitter', 'repeatAfter', 'repeatBefore', 'inertia'),
  params: fc.record({
    frequency: fc.double({ min: 0.1, max: 10, noNaN: true }),
    amplitude: fc.double({ min: 1, max: 100, noNaN: true }),
  }),
});

// ============================================================================
// TRANSFORM ARBITRARIES
// ============================================================================

/**
 * Layer transform
 */
export const layerTransformArb: fc.Arbitrary<LayerTransform> = fc.record({
  position: fc.record({
    x: smallPositionArb,
    y: smallPositionArb,
    z: fc.constant(0),
  }),
  scale: fc.record({
    x: scaleArb.map(s => s * 100), // Scale is in percentage
    y: scaleArb.map(s => s * 100),
    z: fc.constant(100),
  }),
  rotation: fc.record({
    x: fc.constant(0),
    y: fc.constant(0),
    z: rotationArb,
  }),
  origin: smallVec2Arb,
});

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/**
 * Generate a frame that falls between two keyframes
 * Useful for testing interpolation
 */
export function frameBetweenKeyframesArb(keyframes: Keyframe<unknown>[]): fc.Arbitrary<number> {
  if (keyframes.length < 2) {
    return fc.constant(0);
  }
  
  const firstFrame = keyframes[0].frame;
  const lastFrame = keyframes[keyframes.length - 1].frame;
  
  return fc.double({ 
    min: firstFrame, 
    max: lastFrame, 
    noNaN: true 
  });
}

/**
 * Generate a frame with associated keyframes where frame is guaranteed
 * to be within the keyframe range
 */
export const frameWithKeyframesArb = sortedNumericKeyframesArb.chain(keyframes => {
  const firstFrame = keyframes[0].frame;
  const lastFrame = keyframes[keyframes.length - 1].frame;
  
  return fc.double({ min: firstFrame, max: lastFrame, noNaN: true }).map(frame => ({
    frame,
    keyframes
  }));
});
