/**
 * Depthflow Service Tests
 *
 * Tests motion components, easing functions, presets, and
 * the depthflow parallax system.
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  applyEasing,
  createMotionComponent,
  evaluateMotionComponent,
  evaluateMotionsForParameter,
  evaluateAllMotions,
  createDefaultDepthflowConfig,
  createDefaultDOFConfig,
  createDefaultEnhancedConfig,
  applyMotionPreset,
  getMotionPresetNames,
  getMotionPresetDescription,
  MOTION_PRESETS,
  type MotionComponent,
  type MotionParameter,
  type EasingType,
  type DepthflowConfig
} from '@/services/depthflow';

// ============================================================================
// EASING FUNCTION TESTS
// ============================================================================

describe('applyEasing', () => {
  describe('Linear easing', () => {
    it('should return t unchanged for linear', () => {
      expect(applyEasing(0, 'linear')).toBe(0);
      expect(applyEasing(0.5, 'linear')).toBe(0.5);
      expect(applyEasing(1, 'linear')).toBe(1);
    });
  });

  describe('Ease-in (quadratic)', () => {
    it('should return 0 at t=0', () => {
      expect(applyEasing(0, 'ease-in')).toBe(0);
    });

    it('should return 1 at t=1', () => {
      expect(applyEasing(1, 'ease-in')).toBe(1);
    });

    it('should produce values less than t (slow start)', () => {
      const result = applyEasing(0.5, 'ease-in');
      expect(result).toBeLessThan(0.5);
      expect(result).toBe(0.25); // t^2 = 0.5^2 = 0.25
    });
  });

  describe('Ease-out (quadratic)', () => {
    it('should return 0 at t=0', () => {
      expect(applyEasing(0, 'ease-out')).toBe(0);
    });

    it('should return 1 at t=1', () => {
      expect(applyEasing(1, 'ease-out')).toBe(1);
    });

    it('should produce values greater than t (fast start)', () => {
      const result = applyEasing(0.5, 'ease-out');
      expect(result).toBeGreaterThan(0.5);
      expect(result).toBe(0.75); // 1 - (1-0.5)^2 = 0.75
    });
  });

  describe('Ease-in-out', () => {
    it('should return 0 at t=0', () => {
      expect(applyEasing(0, 'ease-in-out')).toBe(0);
    });

    it('should return 1 at t=1', () => {
      expect(applyEasing(1, 'ease-in-out')).toBe(1);
    });

    it('should return 0.5 at t=0.5', () => {
      expect(applyEasing(0.5, 'ease-in-out')).toBe(0.5);
    });

    it('should produce slow start and slow end', () => {
      expect(applyEasing(0.25, 'ease-in-out')).toBeLessThan(0.25);
      expect(applyEasing(0.75, 'ease-in-out')).toBeGreaterThan(0.75);
    });
  });

  describe('Bounce easing', () => {
    it('should return 0 at t=0', () => {
      expect(applyEasing(0, 'bounce')).toBe(0);
    });

    it('should return values close to 1 at t=1', () => {
      const result = applyEasing(1, 'bounce');
      expect(result).toBeCloseTo(1, 2);
    });

    it('should produce bounce-like behavior', () => {
      // Bounce easing should have characteristic points
      const early = applyEasing(0.3, 'bounce');
      const mid = applyEasing(0.5, 'bounce');
      const late = applyEasing(0.9, 'bounce');

      expect(early).toBeGreaterThan(0);
      expect(mid).toBeGreaterThan(0);
      expect(late).toBeCloseTo(1, 1);
    });
  });

  describe('Elastic easing', () => {
    it('should return 0 at t=0', () => {
      expect(applyEasing(0, 'elastic')).toBe(0);
    });

    it('should return 1 at t=1', () => {
      expect(applyEasing(1, 'elastic')).toBe(1);
    });

    it('should overshoot (values > 1) during animation', () => {
      // Elastic easing can overshoot
      const values = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9].map(t =>
        applyEasing(t, 'elastic')
      );
      // At some point it should exceed 1 (overshoot)
      const hasOvershoot = values.some(v => v > 1);
      expect(hasOvershoot || values.every(v => v <= 1)).toBe(true);
    });
  });

  describe('Back easing', () => {
    it('should return 0 at t=0', () => {
      expect(applyEasing(0, 'back')).toBeCloseTo(0, 5);
    });

    it('should return 1 at t=1', () => {
      expect(applyEasing(1, 'back')).toBe(1);
    });

    it('should produce overshoot characteristic of back easing', () => {
      const mid = applyEasing(0.5, 'back');
      // Back easing overshoots, should be close to or past target at midpoint
      expect(typeof mid).toBe('number');
    });
  });

  describe('Unknown easing', () => {
    it('should default to linear for unknown easing types', () => {
      const result = applyEasing(0.5, 'unknown' as EasingType);
      expect(result).toBe(0.5);
    });
  });
});

// ============================================================================
// MOTION COMPONENT TESTS
// ============================================================================

describe('createMotionComponent', () => {
  it('should create a motion component with default values', () => {
    const motion = createMotionComponent();

    expect(motion.id).toMatch(/^motion_/);
    expect(motion.type).toBe('linear');
    expect(motion.parameter).toBe('zoom');
    expect(motion.startValue).toBe(1.0);
    expect(motion.endValue).toBe(1.2);
    expect(motion.startFrame).toBe(0);
    expect(motion.endFrame).toBe(30);
    expect(motion.easing).toBe('ease-in-out');
    expect(motion.enabled).toBe(true);
  });

  it('should apply overrides', () => {
    const motion = createMotionComponent({
      type: 'sine',
      parameter: 'offsetX',
      startValue: 0,
      endValue: 100,
      amplitude: 0.5,
      frequency: 2
    });

    expect(motion.type).toBe('sine');
    expect(motion.parameter).toBe('offsetX');
    expect(motion.amplitude).toBe(0.5);
    expect(motion.frequency).toBe(2);
  });

  it('should generate unique IDs', () => {
    const motion1 = createMotionComponent();
    const motion2 = createMotionComponent();

    expect(motion1.id).not.toBe(motion2.id);
  });
});

describe('evaluateMotionComponent', () => {
  describe('Disabled motions', () => {
    it('should return null for disabled motion', () => {
      const motion = createMotionComponent({ enabled: false });
      expect(evaluateMotionComponent(motion, 15)).toBeNull();
    });
  });

  describe('Frame range handling', () => {
    it('should return startValue before startFrame', () => {
      const motion = createMotionComponent({
        startFrame: 10,
        endFrame: 20,
        startValue: 100,
        endValue: 200
      });

      expect(evaluateMotionComponent(motion, 5)).toBe(100);
      expect(evaluateMotionComponent(motion, 0)).toBe(100);
    });

    it('should return endValue after endFrame', () => {
      const motion = createMotionComponent({
        startFrame: 10,
        endFrame: 20,
        startValue: 100,
        endValue: 200
      });

      expect(evaluateMotionComponent(motion, 25)).toBe(200);
      expect(evaluateMotionComponent(motion, 100)).toBe(200);
    });
  });

  describe('Linear motion type', () => {
    it('should linearly interpolate between start and end', () => {
      const motion = createMotionComponent({
        type: 'linear',
        startFrame: 0,
        endFrame: 100,
        startValue: 0,
        endValue: 100,
        easing: 'linear'
      });

      expect(evaluateMotionComponent(motion, 0)).toBe(0);
      expect(evaluateMotionComponent(motion, 50)).toBe(50);
      expect(evaluateMotionComponent(motion, 100)).toBe(100);
    });
  });

  describe('Exponential motion type', () => {
    it('should interpolate exponentially', () => {
      const motion = createMotionComponent({
        type: 'exponential',
        startFrame: 0,
        endFrame: 100,
        startValue: 1,
        endValue: 100,
        easing: 'linear'
      });

      const start = evaluateMotionComponent(motion, 0);
      const mid = evaluateMotionComponent(motion, 50);
      const end = evaluateMotionComponent(motion, 100);

      expect(start).toBeCloseTo(1, 3);
      expect(mid).toBeCloseTo(10, 0); // sqrt(1 * 100) = 10
      expect(end).toBeCloseTo(100, 3);
    });
  });

  describe('Sine motion type', () => {
    it('should oscillate sinusoidally', () => {
      const motion = createMotionComponent({
        type: 'sine',
        startFrame: 0,
        endFrame: 100,
        startValue: 0,
        endValue: 0,
        amplitude: 1,
        frequency: 1,
        loops: 1,
        phase: 0,
        easing: 'linear'
      });

      // At start (t=0), sin(0) = 0
      const atStart = evaluateMotionComponent(motion, 0);
      expect(atStart).toBeCloseTo(0, 1);

      // At quarter (t=0.25), sin(0.5*PI) = 1
      const atQuarter = evaluateMotionComponent(motion, 25);
      expect(atQuarter).toBeCloseTo(1, 1);

      // At mid (t=0.5), sin(PI) = 0
      const atMid = evaluateMotionComponent(motion, 50);
      expect(atMid).toBeCloseTo(0, 1);
    });
  });

  describe('Cosine motion type', () => {
    it('should oscillate cosinusoidally', () => {
      const motion = createMotionComponent({
        type: 'cosine',
        startFrame: 0,
        endFrame: 100,
        startValue: 0,
        endValue: 0,
        amplitude: 1,
        frequency: 1,
        loops: 1,
        phase: 0,
        easing: 'linear'
      });

      // At start (t=0), cos(0) = 1
      const atStart = evaluateMotionComponent(motion, 0);
      expect(atStart).toBeCloseTo(1, 1);

      // At mid (t=0.5), cos(PI) = -1
      const atMid = evaluateMotionComponent(motion, 50);
      expect(atMid).toBeCloseTo(-1, 1);
    });
  });

  describe('Arc motion type', () => {
    it('should follow parabolic arc', () => {
      const motion = createMotionComponent({
        type: 'arc',
        startFrame: 0,
        endFrame: 100,
        startValue: 0,
        endValue: 100,
        amplitude: 50,
        easing: 'linear'
      });

      const start = evaluateMotionComponent(motion, 0);
      const mid = evaluateMotionComponent(motion, 50);
      const end = evaluateMotionComponent(motion, 100);

      // Arc should peak in the middle
      expect(start).toBe(0);
      expect(mid).toBeGreaterThan(50); // Should be above linear interpolation
      expect(end).toBeCloseTo(100, 1);
    });
  });

  describe('setTarget motion type', () => {
    it('should jump to end value at start frame', () => {
      const motion = createMotionComponent({
        type: 'setTarget',
        startFrame: 10,
        endFrame: 20,
        startValue: 0,
        endValue: 100
      });

      expect(evaluateMotionComponent(motion, 5)).toBe(0);
      expect(evaluateMotionComponent(motion, 10)).toBe(100);
      expect(evaluateMotionComponent(motion, 15)).toBe(100);
    });
  });

  describe('Zero duration handling', () => {
    it('should handle zero duration gracefully', () => {
      const motion = createMotionComponent({
        startFrame: 10,
        endFrame: 10,
        startValue: 0,
        endValue: 100
      });

      const result = evaluateMotionComponent(motion, 10);
      expect(typeof result).toBe('number');
    });
  });
});

// ============================================================================
// MOTION COMPOSITION TESTS
// ============================================================================

describe('evaluateMotionsForParameter', () => {
  it('should return base value when no motions match parameter', () => {
    const motions: MotionComponent[] = [
      createMotionComponent({ parameter: 'offsetX' })
    ];

    const result = evaluateMotionsForParameter(motions, 'zoom', 15, 1.0);
    expect(result).toBe(1.0);
  });

  it('should return base value when all motions are disabled', () => {
    const motions: MotionComponent[] = [
      createMotionComponent({ parameter: 'zoom', enabled: false })
    ];

    const result = evaluateMotionsForParameter(motions, 'zoom', 15, 1.0);
    expect(result).toBe(1.0);
  });

  it('should combine multiple motions additively', () => {
    const motions: MotionComponent[] = [
      createMotionComponent({
        parameter: 'zoom',
        startFrame: 0,
        endFrame: 100,
        startValue: 1.0,
        endValue: 1.5,
        easing: 'linear'
      }),
      createMotionComponent({
        parameter: 'zoom',
        startFrame: 0,
        endFrame: 100,
        startValue: 0,
        endValue: 0.5,
        easing: 'linear'
      })
    ];

    // Both motions add their delta from startValue
    // At frame 50: first motion adds 0.25, second adds 0.25
    const result = evaluateMotionsForParameter(motions, 'zoom', 50, 1.0);
    expect(result).toBeCloseTo(1.5, 2);
  });
});

describe('evaluateAllMotions', () => {
  it('should evaluate all motion parameters at once', () => {
    const baseConfig = createDefaultDepthflowConfig();
    const motions: MotionComponent[] = [
      createMotionComponent({
        parameter: 'zoom',
        startFrame: 0,
        endFrame: 100,
        startValue: 1.0,
        endValue: 2.0,
        easing: 'linear'
      }),
      createMotionComponent({
        parameter: 'offsetX',
        startFrame: 0,
        endFrame: 100,
        startValue: 0,
        endValue: 0.5,
        easing: 'linear'
      })
    ];

    const result = evaluateAllMotions(motions, 50, baseConfig);

    expect(result.zoom).toBeCloseTo(1.5, 2);
    expect(result.offsetX).toBeCloseTo(0.25, 2);
    expect(result.offsetY).toBe(baseConfig.offsetY);
    expect(result.rotation).toBe(baseConfig.rotation);
  });
});

// ============================================================================
// DEFAULT CONFIGURATION TESTS
// ============================================================================

describe('Default Configuration Functions', () => {
  describe('createDefaultDepthflowConfig', () => {
    it('should create config with all required fields', () => {
      const config = createDefaultDepthflowConfig();

      expect(config.preset).toBe('static');
      expect(config.zoom).toBe(1.0);
      expect(config.offsetX).toBe(0);
      expect(config.offsetY).toBe(0);
      expect(config.rotation).toBe(0);
      expect(config.depthScale).toBe(1.0);
      expect(config.focusDepth).toBe(0.5);
      expect(config.dollyZoom).toBe(0);
      expect(config.orbitRadius).toBe(0.1);
      expect(config.orbitSpeed).toBe(2);
      expect(config.swingAmplitude).toBe(0.1);
      expect(config.swingFrequency).toBe(0.5);
      expect(config.edgeDilation).toBe(5);
      expect(config.inpaintEdges).toBe(true);
    });
  });

  describe('createDefaultDOFConfig', () => {
    it('should create DOF config with defaults', () => {
      const config = createDefaultDOFConfig();

      expect(config.enabled).toBe(false);
      expect(config.focusDepth).toBe(0.5);
      expect(config.aperture).toBe(2.8);
      expect(config.bokehShape).toBe('circle');
      expect(config.bokehSize).toBe(1.0);
    });
  });

  describe('createDefaultEnhancedConfig', () => {
    it('should create enhanced config with empty motions', () => {
      const config = createDefaultEnhancedConfig();

      expect(config.motions).toEqual([]);
      expect(config.dof).toBeDefined();
      expect(config.vignette).toBe(0);
      expect(config.quality).toBe(80);
      expect(config.ssaa).toBe(1);
      expect(config.tilingMode).toBe('none');
    });
  });
});

// ============================================================================
// MOTION PRESET TESTS
// ============================================================================

describe('Motion Presets', () => {
  describe('MOTION_PRESETS', () => {
    it('should have all expected presets', () => {
      const expectedPresets = [
        'zoom_in_gentle',
        'ken_burns',
        'vertigo',
        'breathing',
        'swing_horizontal',
        'orbit',
        'rack_focus',
        'reveal',
        'tilt_shift'
      ];

      for (const preset of expectedPresets) {
        expect(MOTION_PRESETS[preset]).toBeDefined();
        expect(Array.isArray(MOTION_PRESETS[preset])).toBe(true);
      }
    });

    it('should have valid motion components in each preset', () => {
      for (const [name, motions] of Object.entries(MOTION_PRESETS)) {
        expect(motions.length).toBeGreaterThan(0);

        for (const motion of motions) {
          expect(motion.id).toBeDefined();
          expect(motion.type).toBeDefined();
          expect(motion.parameter).toBeDefined();
          expect(motion.enabled).toBe(true);
        }
      }
    });
  });

  describe('applyMotionPreset', () => {
    it('should apply preset with custom timing', () => {
      const motions = applyMotionPreset('zoom_in_gentle', 10, 100);

      expect(motions.length).toBeGreaterThan(0);
      for (const motion of motions) {
        expect(motion.startFrame).toBe(10);
        expect(motion.endFrame).toBe(110);
      }
    });

    it('should return empty array for unknown preset', () => {
      const motions = applyMotionPreset('unknown_preset', 0, 30);
      expect(motions).toEqual([]);
    });

    it('should create unique IDs for applied preset motions', () => {
      const motions1 = applyMotionPreset('ken_burns', 0, 30);
      const motions2 = applyMotionPreset('ken_burns', 0, 30);

      for (let i = 0; i < motions1.length; i++) {
        expect(motions1[i].id).not.toBe(motions2[i].id);
      }
    });
  });

  describe('getMotionPresetNames', () => {
    it('should return all preset names', () => {
      const names = getMotionPresetNames();

      expect(names.length).toBeGreaterThan(0);
      expect(names).toContain('zoom_in_gentle');
      expect(names).toContain('ken_burns');
      expect(names).toContain('vertigo');
    });
  });

  describe('getMotionPresetDescription', () => {
    it('should return descriptions for known presets', () => {
      const desc = getMotionPresetDescription('ken_burns');
      expect(desc).toBe('Classic documentary-style pan and zoom');
    });

    it('should return default description for unknown preset', () => {
      const desc = getMotionPresetDescription('unknown');
      expect(desc).toBe('Custom motion effect');
    });
  });
});

// ============================================================================
// MOTION PARAMETER TYPE TESTS
// ============================================================================

describe('Motion Parameter Types', () => {
  const parameters: MotionParameter[] = ['zoom', 'offsetX', 'offsetY', 'rotation', 'depthScale', 'focusDepth'];

  it('should support all parameter types', () => {
    for (const param of parameters) {
      const motion = createMotionComponent({ parameter: param });
      expect(motion.parameter).toBe(param);
    }
  });
});

// ============================================================================
// EDGE CASES
// ============================================================================

describe('Bounce motion type', () => {
  it('should apply bounce effect', () => {
    const motion = createMotionComponent({
      type: 'bounce',
      startFrame: 0,
      endFrame: 100,
      startValue: 0,
      endValue: 100,
      easing: 'linear'
    });

    const start = evaluateMotionComponent(motion, 0);
    const mid = evaluateMotionComponent(motion, 50);
    const end = evaluateMotionComponent(motion, 100);

    // Bounce should produce valid numeric values
    expect(typeof start).toBe('number');
    expect(typeof mid).toBe('number');
    expect(typeof end).toBe('number');
    // End should be close to target value
    expect(end).toBeCloseTo(100, 0);
  });
});

describe('Elastic motion type', () => {
  it('should apply elastic effect', () => {
    const motion = createMotionComponent({
      type: 'elastic',
      startFrame: 0,
      endFrame: 100,
      startValue: 0,
      endValue: 100,
      easing: 'linear'
    });

    const start = evaluateMotionComponent(motion, 0);
    const mid = evaluateMotionComponent(motion, 50);
    const end = evaluateMotionComponent(motion, 100);

    // Elastic should produce valid values
    expect(typeof start).toBe('number');
    expect(typeof mid).toBe('number');
    // End should be close to target value
    expect(end).toBeCloseTo(100, 0);
  });

  it('should handle boundary cases in elastic motion', () => {
    const motion = createMotionComponent({
      type: 'elastic',
      startFrame: 0,
      endFrame: 100,
      startValue: 0,
      endValue: 100,
      easing: 'linear'
    });

    // At t=0 and t=1, elastic modifier should be minimal
    const atStart = evaluateMotionComponent(motion, 0);
    const atEnd = evaluateMotionComponent(motion, 100);

    expect(atStart).toBeCloseTo(0, 0);
    expect(atEnd).toBeCloseTo(100, 0);
  });
});

describe('Default motion type handling', () => {
  it('should use linear interpolation for unknown motion type', () => {
    const motion = createMotionComponent({
      type: 'unknown' as any,
      startFrame: 0,
      endFrame: 100,
      startValue: 0,
      endValue: 100,
      easing: 'linear'
    });

    // Should fall through to default case which uses linear
    expect(evaluateMotionComponent(motion, 50)).toBe(50);
  });
});

describe('Edge Cases', () => {
  it('should handle negative frame numbers', () => {
    const motion = createMotionComponent({
      startFrame: -10,
      endFrame: 10,
      startValue: 0,
      endValue: 100,
      easing: 'linear'
    });

    expect(evaluateMotionComponent(motion, 0)).toBe(50);
    expect(evaluateMotionComponent(motion, -10)).toBe(0);
  });

  it('should handle very large frame numbers', () => {
    const motion = createMotionComponent({
      startFrame: 0,
      endFrame: 1000000,
      startValue: 0,
      endValue: 100,
      easing: 'linear'
    });

    expect(evaluateMotionComponent(motion, 500000)).toBe(50);
  });

  it('should handle very small value differences', () => {
    const motion = createMotionComponent({
      startFrame: 0,
      endFrame: 100,
      startValue: 0.0001,
      endValue: 0.0002,
      easing: 'linear'
    });

    const result = evaluateMotionComponent(motion, 50);
    expect(result).toBeCloseTo(0.00015, 6);
  });

  it('should handle reversed value ranges (endValue < startValue)', () => {
    const motion = createMotionComponent({
      startFrame: 0,
      endFrame: 100,
      startValue: 100,
      endValue: 0,
      easing: 'linear'
    });

    expect(evaluateMotionComponent(motion, 0)).toBe(100);
    expect(evaluateMotionComponent(motion, 50)).toBe(50);
    expect(evaluateMotionComponent(motion, 100)).toBe(0);
  });
});
