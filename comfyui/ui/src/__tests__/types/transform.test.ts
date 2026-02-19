/**
 * AUDIT: transform.ts - Layer transform types and helper functions
 * Lines: 550
 * Exports: 15 (8 types/interfaces, 7 functions)
 * Functions to test: createDefaultTransform, normalizeLayerTransform,
 *   createFollowPathConstraint, separatePositionDimensions, linkPositionDimensions,
 *   separateScaleDimensions, linkScaleDimensions
 * 
 * IMPORTANT: Several functions MUTATE their input!
 */

import { describe, test, expect, beforeEach } from 'vitest';
import {
  createDefaultTransform,
  normalizeLayerTransform,
  createFollowPathConstraint,
  separatePositionDimensions,
  linkPositionDimensions,
  separateScaleDimensions,
  linkScaleDimensions,
  type LayerTransform,
  type Vec2,
  type Vec3,
  type MotionBlurType,
  type LayerMotionBlurSettings,
  type LayerMaterialOptions,
  type AutoOrientMode,
  type FollowPathConstraint,
} from '@/types/transform';
import { createAnimatableProperty, createKeyframe, type AnimatableProperty } from '@/types/animation';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // helper
// ════════════════════════════════════════════════════════════════════════════

function createTransformWithKeyframes(): LayerTransform {
  const transform = createDefaultTransform();
  
  // Add keyframes to position
  transform.position.animated = true;
  transform.position.keyframes = [
    createKeyframe(0, { x: 0, y: 0, z: 0 }),
    createKeyframe(30, { x: 100, y: 50, z: 25 }),
    createKeyframe(60, { x: 200, y: 100, z: 50 }),
  ];
  
  // Add keyframes to scale
  transform.scale.animated = true;
  transform.scale.keyframes = [
    createKeyframe(0, { x: 100, y: 100, z: 100 }),
    createKeyframe(30, { x: 150, y: 150, z: 100 }),
  ];
  
  return transform;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                      // test
// ════════════════════════════════════════════════════════════════════════════

describe('createDefaultTransform', () => {
  test('returns LayerTransform with all required properties', () => {
    const transform = createDefaultTransform();
    
    expect(transform).toHaveProperty('position');
    expect(transform).toHaveProperty('origin');
    expect(transform).toHaveProperty('anchorPoint'); // deprecated but present
    expect(transform).toHaveProperty('scale');
    expect(transform).toHaveProperty('rotation');
    expect(transform).toHaveProperty('orientation');
    expect(transform).toHaveProperty('rotationX');
    expect(transform).toHaveProperty('rotationY');
    expect(transform).toHaveProperty('rotationZ');
  });

  test('position defaults to (0, 0, 0)', () => {
    const transform = createDefaultTransform();
    expect(transform.position.value).toEqual({ x: 0, y: 0, z: 0 });
  });

  test('origin defaults to (0, 0, 0)', () => {
    const transform = createDefaultTransform();
    expect(transform.origin.value).toEqual({ x: 0, y: 0, z: 0 });
  });

  test('anchorPoint is same reference as origin (backwards compat)', () => {
    const transform = createDefaultTransform();
    expect(transform.anchorPoint).toBe(transform.origin);
  });

  test('scale defaults to (100, 100, 100)', () => {
    const transform = createDefaultTransform();
    expect(transform.scale.value).toEqual({ x: 100, y: 100, z: 100 });
  });

  test('rotation defaults to 0', () => {
    const transform = createDefaultTransform();
    expect(transform.rotation.value).toBe(0);
  });

  test('orientation defaults to (0, 0, 0)', () => {
    const transform = createDefaultTransform();
    expect(transform.orientation?.value).toEqual({ x: 0, y: 0, z: 0 });
  });

  test('rotationX/Y/Z default to 0', () => {
    const transform = createDefaultTransform();
    expect(transform.rotationX?.value).toBe(0);
    expect(transform.rotationY?.value).toBe(0);
    expect(transform.rotationZ?.value).toBe(0);
  });

  test('all properties start as not animated', () => {
    const transform = createDefaultTransform();
    expect(transform.position.animated).toBe(false);
    expect(transform.origin.animated).toBe(false);
    expect(transform.scale.animated).toBe(false);
    expect(transform.rotation.animated).toBe(false);
  });

  test('all properties have empty keyframes', () => {
    const transform = createDefaultTransform();
    expect(transform.position.keyframes).toEqual([]);
    expect(transform.origin.keyframes).toEqual([]);
    expect(transform.scale.keyframes).toEqual([]);
    expect(transform.rotation.keyframes).toEqual([]);
  });

  test('each call returns unique transform (not shared reference)', () => {
    const t1 = createDefaultTransform();
    const t2 = createDefaultTransform();
    
    expect(t1).not.toBe(t2);
    expect(t1.position).not.toBe(t2.position);
  });

  test('properties have correct types', () => {
    const transform = createDefaultTransform();
    expect(transform.position.type).toBe('vector3');
    expect(transform.origin.type).toBe('vector3');
    expect(transform.scale.type).toBe('vector3');
    expect(transform.rotation.type).toBe('number');
    expect(transform.orientation?.type).toBe('vector3');
    expect(transform.rotationX?.type).toBe('number');
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                      // test
// ════════════════════════════════════════════════════════════════════════════

describe('normalizeLayerTransform', () => {
  test('MUTATES input: copies anchorPoint to origin if origin missing', () => {
    const baseTransform = createDefaultTransform();
    // Create transform without origin for testing fallback behavior
    const { origin, ...transformWithoutOrigin } = baseTransform;
    const transform: Omit<LayerTransform, 'origin'> & { anchorPoint?: AnimatableProperty<{ x: number; y: number; z?: number }> } = {
      ...transformWithoutOrigin,
      anchorPoint: baseTransform.anchorPoint,
    };
    
    const anchorPointValue = transform.anchorPoint;
    normalizeLayerTransform(transform as LayerTransform);
    
    expect((transform as LayerTransform).origin).toBe(anchorPointValue);
  });

  test('MUTATES input: copies origin to anchorPoint if anchorPoint missing', () => {
    const baseTransform = createDefaultTransform();
    // Create transform without anchorPoint for testing fallback behavior
    const { anchorPoint, ...transformWithoutAnchorPoint } = baseTransform;
    const transform: Omit<LayerTransform, 'anchorPoint'> = {
      ...transformWithoutAnchorPoint,
    };
    
    const originValue = transform.origin;
    normalizeLayerTransform(transform);
    
    expect(transform.anchorPoint).toBe(originValue);
  });

  test('returns the same transform object (not a copy)', () => {
    const transform = createDefaultTransform();
    const result = normalizeLayerTransform(transform);
    
    expect(result).toBe(transform);
  });

  test('does nothing if both origin and anchorPoint exist', () => {
    const transform = createDefaultTransform();
    const originalOrigin = transform.origin;
    const originalAnchorPoint = transform.anchorPoint;
    
    normalizeLayerTransform(transform);
    
    expect(transform.origin).toBe(originalOrigin);
    expect(transform.anchorPoint).toBe(originalAnchorPoint);
  });

  test('handles transform with neither origin nor anchorPoint', () => {
    const baseTransform = createDefaultTransform();
    // Create transform without both origin and anchorPoint for testing edge case
    const { origin, anchorPoint, ...transformWithoutBoth } = baseTransform;
    const transform: Omit<LayerTransform, 'origin' | 'anchorPoint'> = {
      ...transformWithoutBoth,
    };
    
    // Should not throw
    const result = normalizeLayerTransform(transform as LayerTransform);
    expect(result).toBe(transform);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                      // test
// ════════════════════════════════════════════════════════════════════════════

describe('createFollowPathConstraint', () => {
  test('creates constraint with specified pathLayerId', () => {
    const constraint = createFollowPathConstraint('layer_123');
    expect(constraint.pathLayerId).toBe('layer_123');
  });

  test('enabled is true by default', () => {
    const constraint = createFollowPathConstraint('layer_123');
    expect(constraint.enabled).toBe(true);
  });

  test('progress starts at 0', () => {
    const constraint = createFollowPathConstraint('layer_123');
    expect(constraint.progress.value).toBe(0);
  });

  test('offset starts at 0', () => {
    const constraint = createFollowPathConstraint('layer_123');
    expect(constraint.offset.value).toBe(0);
  });

  test('tangentOffset starts at 0', () => {
    const constraint = createFollowPathConstraint('layer_123');
    expect(constraint.tangentOffset).toBe(0);
  });

  test('autoOrient is true by default', () => {
    const constraint = createFollowPathConstraint('layer_123');
    expect(constraint.autoOrient).toBe(true);
  });

  test('rotationOffset starts at 0', () => {
    const constraint = createFollowPathConstraint('layer_123');
    expect(constraint.rotationOffset.value).toBe(0);
  });

  test('banking starts at 0', () => {
    const constraint = createFollowPathConstraint('layer_123');
    expect(constraint.banking.value).toBe(0);
  });

  test('loopMode defaults to clamp', () => {
    const constraint = createFollowPathConstraint('layer_123');
    expect(constraint.loopMode).toBe('clamp');
  });

  test('handles empty string pathLayerId', () => {
    const constraint = createFollowPathConstraint('');
    expect(constraint.pathLayerId).toBe('');
  });

  test('handles special characters in pathLayerId', () => {
    const constraint = createFollowPathConstraint('layer-with-special_chars.123');
    expect(constraint.pathLayerId).toBe('layer-with-special_chars.123');
  });

  test('animatable properties have correct structure', () => {
    const constraint = createFollowPathConstraint('layer_123');
    
    expect(constraint.progress).toHaveProperty('id');
    expect(constraint.progress).toHaveProperty('name');
    expect(constraint.progress).toHaveProperty('type');
    expect(constraint.progress).toHaveProperty('value');
    expect(constraint.progress).toHaveProperty('animated');
    expect(constraint.progress).toHaveProperty('keyframes');
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                      // test
// ════════════════════════════════════════════════════════════════════════════

describe('separatePositionDimensions', () => {
  test('MUTATES input: creates positionX, positionY, positionZ', () => {
    const transform = createDefaultTransform();
    transform.position.value = { x: 10, y: 20, z: 30 };
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX).toBeDefined();
    expect(transform.positionY).toBeDefined();
    expect(transform.positionZ).toBeDefined();
  });

  test('positionX/Y/Z have correct values from position', () => {
    const transform = createDefaultTransform();
    transform.position.value = { x: 10, y: 20, z: 30 };
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX?.value).toBe(10);
    expect(transform.positionY?.value).toBe(20);
    expect(transform.positionZ?.value).toBe(30);
  });

  test('handles position without z component', () => {
    const transform = createDefaultTransform();
    // Vec2 is valid for position (z is optional)
    transform.position.value = { x: 10, y: 20 };
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX?.value).toBe(10);
    expect(transform.positionY?.value).toBe(20);
    expect(transform.positionZ?.value).toBe(0); // default
  });

  test('copies keyframes to separate properties', () => {
    const transform = createTransformWithKeyframes();
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX?.keyframes.length).toBe(3);
    expect(transform.positionY?.keyframes.length).toBe(3);
    expect(transform.positionZ?.keyframes.length).toBe(3);
  });

  test('keyframe values are split correctly', () => {
    const transform = createTransformWithKeyframes();
    
    separatePositionDimensions(transform);
    
    // First keyframe was { x: 0, y: 0, z: 0 }
    expect(transform.positionX?.keyframes[0].value).toBe(0);
    expect(transform.positionY?.keyframes[0].value).toBe(0);
    expect(transform.positionZ?.keyframes[0].value).toBe(0);
    
    // Second keyframe was { x: 100, y: 50, z: 25 }
    expect(transform.positionX?.keyframes[1].value).toBe(100);
    expect(transform.positionY?.keyframes[1].value).toBe(50);
    expect(transform.positionZ?.keyframes[1].value).toBe(25);
  });

  test('sets separateDimensions.position to true', () => {
    const transform = createDefaultTransform();
    
    separatePositionDimensions(transform);
    
    expect(transform.separateDimensions?.position).toBe(true);
  });

  test('initializes separateDimensions if undefined', () => {
    const transform = createDefaultTransform();
    delete transform.separateDimensions;
    
    separatePositionDimensions(transform);
    
    expect(transform.separateDimensions).toEqual({ position: true, scale: false });
  });

  test('sets animated flag on separate properties if original was animated', () => {
    const transform = createTransformWithKeyframes();
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX?.animated).toBe(true);
    expect(transform.positionY?.animated).toBe(true);
    expect(transform.positionZ?.animated).toBe(true);
  });

  test('does not set animated flag if original was not animated', () => {
    const transform = createDefaultTransform();
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX?.animated).toBe(false);
    expect(transform.positionY?.animated).toBe(false);
    expect(transform.positionZ?.animated).toBe(false);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                      // test
// ════════════════════════════════════════════════════════════════════════════

describe('linkPositionDimensions', () => {
  test('does nothing if positionX is undefined', () => {
    const transform = createDefaultTransform();
    
    // Should not throw
    linkPositionDimensions(transform);
    
    expect(transform.positionX).toBeUndefined();
  });

  test('does nothing if positionY is undefined', () => {
    const transform = createDefaultTransform();
    transform.positionX = createAnimatableProperty('Position X', 10, 'number');
    
    // Should not throw
    linkPositionDimensions(transform);
  });

  test('MUTATES input: updates position.value from X/Y/Z', () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    
    transform.positionX!.value = 100;
    transform.positionY!.value = 200;
    transform.positionZ!.value = 300;
    
    linkPositionDimensions(transform);
    
    expect(transform.position.value).toEqual({ x: 100, y: 200, z: 300 });
  });

  test('MUTATES input: deletes positionX/Y/Z', () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    
    linkPositionDimensions(transform);
    
    expect(transform.positionX).toBeUndefined();
    expect(transform.positionY).toBeUndefined();
    expect(transform.positionZ).toBeUndefined();
  });

  test('merges keyframes from X/Y/Z', () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    
    // Add keyframes to separate properties
    transform.positionX!.animated = true;
    transform.positionX!.keyframes = [createKeyframe(0, 0), createKeyframe(30, 100)];
    transform.positionY!.animated = true;
    transform.positionY!.keyframes = [createKeyframe(0, 0), createKeyframe(30, 50)];
    transform.positionZ!.animated = true;
    transform.positionZ!.keyframes = [createKeyframe(0, 0), createKeyframe(30, 25)];
    
    linkPositionDimensions(transform);
    
    expect(transform.position.keyframes.length).toBe(2);
    expect(transform.position.keyframes[0].value).toEqual({ x: 0, y: 0, z: 0 });
    expect(transform.position.keyframes[1].value).toEqual({ x: 100, y: 50, z: 25 });
  });

  test('handles keyframes at different frames (interpolates missing)', () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    
    // X has keyframe at 0 and 30
    transform.positionX!.animated = true;
    transform.positionX!.value = 0;
    transform.positionX!.keyframes = [createKeyframe(0, 0), createKeyframe(30, 100)];
    
    // Y only has keyframe at 0
    transform.positionY!.animated = true;
    transform.positionY!.value = 50;
    transform.positionY!.keyframes = [createKeyframe(0, 50)];
    
    // Z has no keyframes
    transform.positionZ!.animated = false;
    transform.positionZ!.value = 10;
    transform.positionZ!.keyframes = [];
    
    linkPositionDimensions(transform);
    
    // Should have keyframes at 0 and 30
    expect(transform.position.keyframes.length).toBe(2);
    // At frame 0: x=0, y=50, z=10
    expect(transform.position.keyframes[0].value).toEqual({ x: 0, y: 50, z: 10 });
    // At frame 30: x=100, y=50 (from value since no kf at 30), z=10
    expect(transform.position.keyframes[1].value.x).toBe(100);
  });

  test('sets separateDimensions.position to false', () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    
    linkPositionDimensions(transform);
    
    expect(transform.separateDimensions?.position).toBe(false);
  });

  test('roundtrip: separate then link preserves values', () => {
    const transform = createDefaultTransform();
    transform.position.value = { x: 123, y: 456, z: 789 };
    
    separatePositionDimensions(transform);
    linkPositionDimensions(transform);
    
    expect(transform.position.value).toEqual({ x: 123, y: 456, z: 789 });
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                      // test
// ════════════════════════════════════════════════════════════════════════════

describe('separateScaleDimensions', () => {
  test('MUTATES input: creates scaleX, scaleY, scaleZ', () => {
    const transform = createDefaultTransform();
    
    separateScaleDimensions(transform);
    
    expect(transform.scaleX).toBeDefined();
    expect(transform.scaleY).toBeDefined();
    expect(transform.scaleZ).toBeDefined();
  });

  test('scaleX/Y/Z have correct values from scale', () => {
    const transform = createDefaultTransform();
    transform.scale.value = { x: 150, y: 200, z: 50 };
    
    separateScaleDimensions(transform);
    
    expect(transform.scaleX?.value).toBe(150);
    expect(transform.scaleY?.value).toBe(200);
    expect(transform.scaleZ?.value).toBe(50);
  });

  test('handles scale without z component (defaults to 100)', () => {
    const transform = createDefaultTransform();
    // Vec2 is valid for scale (z is optional)
    transform.scale.value = { x: 150, y: 200 };
    
    separateScaleDimensions(transform);
    
    expect(transform.scaleX?.value).toBe(150);
    expect(transform.scaleY?.value).toBe(200);
    expect(transform.scaleZ?.value).toBe(100); // default
  });

  test('copies keyframes to separate properties', () => {
    const transform = createTransformWithKeyframes();
    
    separateScaleDimensions(transform);
    
    expect(transform.scaleX?.keyframes.length).toBe(2);
    expect(transform.scaleY?.keyframes.length).toBe(2);
    expect(transform.scaleZ?.keyframes.length).toBe(2);
  });

  test('sets separateDimensions.scale to true', () => {
    const transform = createDefaultTransform();
    
    separateScaleDimensions(transform);
    
    expect(transform.separateDimensions?.scale).toBe(true);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                      // test
// ════════════════════════════════════════════════════════════════════════════

describe('linkScaleDimensions', () => {
  test('does nothing if scaleX is undefined', () => {
    const transform = createDefaultTransform();
    
    linkScaleDimensions(transform);
    
    expect(transform.scaleX).toBeUndefined();
  });

  test('MUTATES input: updates scale.value from X/Y/Z', () => {
    const transform = createDefaultTransform();
    separateScaleDimensions(transform);
    
    transform.scaleX!.value = 200;
    transform.scaleY!.value = 300;
    transform.scaleZ!.value = 150;
    
    linkScaleDimensions(transform);
    
    expect(transform.scale.value).toEqual({ x: 200, y: 300, z: 150 });
  });

  test('MUTATES input: deletes scaleX/Y/Z', () => {
    const transform = createDefaultTransform();
    separateScaleDimensions(transform);
    
    linkScaleDimensions(transform);
    
    expect(transform.scaleX).toBeUndefined();
    expect(transform.scaleY).toBeUndefined();
    expect(transform.scaleZ).toBeUndefined();
  });

  test('sets separateDimensions.scale to false', () => {
    const transform = createDefaultTransform();
    separateScaleDimensions(transform);
    
    linkScaleDimensions(transform);
    
    expect(transform.separateDimensions?.scale).toBe(false);
  });

  test('roundtrip: separate then link preserves values', () => {
    const transform = createDefaultTransform();
    transform.scale.value = { x: 123, y: 456, z: 789 };
    
    separateScaleDimensions(transform);
    linkScaleDimensions(transform);
    
    expect(transform.scale.value).toEqual({ x: 123, y: 456, z: 789 });
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                      // test
// ════════════════════════════════════════════════════════════════════════════

describe('Type definitions', () => {
  test('Vec2 interface structure', () => {
    const v: Vec2 = { x: 10, y: 20 };
    expect(v.x).toBe(10);
    expect(v.y).toBe(20);
  });

  test('Vec3 interface structure', () => {
    const v: Vec3 = { x: 10, y: 20, z: 30 };
    expect(v.x).toBe(10);
    expect(v.y).toBe(20);
    expect(v.z).toBe(30);
  });

  test('MotionBlurType values', () => {
    const types: MotionBlurType[] = ['standard', 'pixel', 'directional', 'radial', 'vector', 'adaptive'];
    expect(types.length).toBe(6);
  });

  test('LayerMotionBlurSettings structure', () => {
    const settings: LayerMotionBlurSettings = {
      type: 'standard',
      shutterAngle: 180,
      shutterPhase: 0,
      samplesPerFrame: 16,
    };
    expect(settings.type).toBe('standard');
    expect(settings.shutterAngle).toBe(180);
  });

  test('LayerMaterialOptions structure', () => {
    const options: LayerMaterialOptions = {
      castsShadows: 'on',
      lightTransmission: 0,
      acceptsShadows: true,
      acceptsLights: true,
      ambient: 100,
      diffuse: 100,
      specularIntensity: 50,
      specularShininess: 50,
      metal: 0,
    };
    expect(options.castsShadows).toBe('on');
  });

  test('AutoOrientMode values', () => {
    const modes: AutoOrientMode[] = ['off', 'toCamera', 'alongPath', 'toPointOfInterest'];
    expect(modes.length).toBe(4);
  });

  test('FollowPathConstraint structure', () => {
    const constraint: FollowPathConstraint = {
      enabled: true,
      pathLayerId: 'path_1',
      progress: createAnimatableProperty('Progress', 0, 'number'),
      offset: createAnimatableProperty('Offset', 0, 'number'),
      tangentOffset: 0,
      autoOrient: true,
      rotationOffset: createAnimatableProperty('Rotation Offset', 0, 'number'),
      banking: createAnimatableProperty('Banking', 0, 'number'),
      loopMode: 'clamp',
    };
    expect(constraint.loopMode).toBe('clamp');
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                             // edge // cases
// ════════════════════════════════════════════════════════════════════════════

describe('Edge cases', () => {
  test('separatePositionDimensions with negative values', () => {
    const transform = createDefaultTransform();
    transform.position.value = { x: -100, y: -50, z: -25 };
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX?.value).toBe(-100);
    expect(transform.positionY?.value).toBe(-50);
    expect(transform.positionZ?.value).toBe(-25);
  });

  test('separatePositionDimensions with very large values', () => {
    const transform = createDefaultTransform();
    transform.position.value = { x: 1e10, y: 1e10, z: 1e10 };
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX?.value).toBe(1e10);
    expect(transform.positionY?.value).toBe(1e10);
    expect(transform.positionZ?.value).toBe(1e10);
  });

  test('separatePositionDimensions with zero values', () => {
    const transform = createDefaultTransform();
    transform.position.value = { x: 0, y: 0, z: 0 };
    
    separatePositionDimensions(transform);
    
    expect(transform.positionX?.value).toBe(0);
    expect(transform.positionY?.value).toBe(0);
    expect(transform.positionZ?.value).toBe(0);
  });

  test('linkPositionDimensions handles empty keyframes array', () => {
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    
    // Clear all keyframes
    transform.positionX!.keyframes = [];
    transform.positionY!.keyframes = [];
    transform.positionZ!.keyframes = [];
    
    linkPositionDimensions(transform);
    
    expect(transform.position.keyframes.length).toBe(0);
    expect(transform.position.animated).toBe(false);
  });

  test('multiple separate/link roundtrips preserve data', () => {
    const transform = createDefaultTransform();
    transform.position.value = { x: 42, y: 84, z: 126 };
    
    // First roundtrip
    separatePositionDimensions(transform);
    linkPositionDimensions(transform);
    
    // Second roundtrip
    separatePositionDimensions(transform);
    linkPositionDimensions(transform);
    
    // Third roundtrip
    separatePositionDimensions(transform);
    linkPositionDimensions(transform);
    
    expect(transform.position.value).toEqual({ x: 42, y: 84, z: 126 });
  });

  test('separate position and scale independently', () => {
    const transform = createDefaultTransform();
    transform.position.value = { x: 100, y: 200, z: 300 };
    transform.scale.value = { x: 50, y: 75, z: 100 };
    
    separatePositionDimensions(transform);
    separateScaleDimensions(transform);
    
    expect(transform.separateDimensions?.position).toBe(true);
    expect(transform.separateDimensions?.scale).toBe(true);
    
    // Link only position
    linkPositionDimensions(transform);
    
    expect(transform.separateDimensions?.position).toBe(false);
    expect(transform.separateDimensions?.scale).toBe(true);
    expect(transform.scaleX).toBeDefined();
  });

  test('linkPositionDimensions interpolates Y value when keyframe missing mid-animation', () => {
    // This tests the internal getInterpolatedValue helper
    const transform = createDefaultTransform();
    separatePositionDimensions(transform);
    
    // X has keyframes at 0, 15, 30
    transform.positionX!.animated = true;
    transform.positionX!.keyframes = [
      createKeyframe(0, 0),
      createKeyframe(15, 50),
      createKeyframe(30, 100),
    ];
    
    // Y has keyframes at 0 and 30 only (missing at 15)
    transform.positionY!.animated = true;
    transform.positionY!.keyframes = [
      createKeyframe(0, 0),
      createKeyframe(30, 200),
    ];
    
    // Z has no keyframes
    transform.positionZ!.value = 0;
    transform.positionZ!.keyframes = [];
    
    linkPositionDimensions(transform);
    
    // Should have keyframes at 0, 15, 30
    expect(transform.position.keyframes.length).toBe(3);
    
    // At frame 15, Y should be interpolated: 0 + (200-0) * (15/30) = 100
    const midKeyframe = transform.position.keyframes.find(kf => kf.frame === 15);
    expect(midKeyframe).toBeDefined();
    expect(midKeyframe!.value.x).toBe(50);
    expect(midKeyframe!.value.y).toBe(100); // Interpolated!
    expect(midKeyframe!.value.z).toBe(0);
  });

  test('linkScaleDimensions interpolates when keyframes at different frames', () => {
    const transform = createDefaultTransform();
    separateScaleDimensions(transform);
    
    // X: keyframes at 0 and 60
    transform.scaleX!.animated = true;
    transform.scaleX!.keyframes = [
      createKeyframe(0, 100),
      createKeyframe(60, 200),
    ];
    
    // Y: keyframe at 30 only
    transform.scaleY!.animated = true;
    transform.scaleY!.keyframes = [
      createKeyframe(30, 150),
    ];
    
    transform.scaleZ!.value = 100;
    transform.scaleZ!.keyframes = [];
    
    linkScaleDimensions(transform);
    
    // Should have keyframes at 0, 30, 60
    expect(transform.scale.keyframes.length).toBe(3);
    
    // At frame 30, X should be interpolated: 100 + (200-100) * (30/60) = 150
    const midKeyframe = transform.scale.keyframes.find(kf => kf.frame === 30);
    expect(midKeyframe).toBeDefined();
    expect(midKeyframe!.value.x).toBe(150); // Interpolated!
    expect(midKeyframe!.value.y).toBe(150);
  });
});
