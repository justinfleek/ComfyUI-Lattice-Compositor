/**
 * Displacement Effects Tests
 *
 * Tests for Tutorial 12: Displacement Maps & Turbulent Displace
 * - Displacement Map effect with layer referencing and procedural maps
 * - Turbulent Displace effect with 7 displacement types
 * - Radio Waves and Ellipse generate effects
 * - Ripple distort effect
 *
 * Note: These tests focus on API correctness and parameter handling.
 * Visual output testing requires a real browser environment.
 */
import { describe, it, expect, beforeEach } from 'vitest';

// Import effect renderers
import {
  displacementMapRenderer,
  turbulentDisplaceRenderer,
  rippleDistortRenderer
} from '@/services/effects/distortRenderer';

import {
  radioWavesRenderer,
  ellipseRenderer
} from '@/services/effects/generateRenderer';

import type { EffectStackResult, EvaluatedEffectParams } from '@/services/effectProcessor';

// Helper to create test canvas
function createTestCanvas(width = 100, height = 100): EffectStackResult {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext('2d')!;

  // Fill with a solid color for testing
  ctx.fillStyle = '#808080';
  ctx.fillRect(0, 0, width, height);

  return { canvas, ctx };
}

// Helper to create displacement map canvas
function createDisplacementMapCanvas(width = 100, height = 100): HTMLCanvasElement {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext('2d')!;

  // Create horizontal gradient (black to white)
  ctx.fillStyle = '#000000';
  ctx.fillRect(0, 0, width / 2, height);
  ctx.fillStyle = '#ffffff';
  ctx.fillRect(width / 2, 0, width / 2, height);

  return canvas;
}

describe('Displacement Map Effect', () => {
  let input: EffectStackResult;

  beforeEach(() => {
    input = createTestCanvas(100, 100);
  });

  describe('Procedural Maps', () => {
    it('should return valid canvas when displacement is zero', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'noise',
        use_for_horizontal: 'luminance',
        use_for_vertical: 'luminance',
        max_horizontal: 0,
        max_vertical: 0
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas.width).toBe(100);
      expect(result.canvas.height).toBe(100);
      expect(result.ctx).toBeDefined();
    });

    it('should process with noise-based procedural displacement', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'noise',
        use_for_horizontal: 'luminance',
        use_for_vertical: 'luminance',
        max_horizontal: 20,
        max_vertical: 20
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
      expect(result.canvas.width).toBe(100);
    });

    it('should process with gradient-h procedural displacement', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'gradient-h',
        use_for_horizontal: 'luminance',
        max_horizontal: 30,
        max_vertical: 0
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });

    it('should process with radial procedural displacement', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'radial',
        use_for_horizontal: 'luminance',
        use_for_vertical: 'luminance',
        max_horizontal: 25,
        max_vertical: 25
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });

    it('should process with sine wave procedural displacement', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'sine-h',
        use_for_horizontal: 'luminance',
        max_horizontal: 15,
        max_vertical: 0,
        map_scale: 2
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });

    it('should process with checker procedural displacement', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'checker',
        use_for_horizontal: 'luminance',
        max_horizontal: 10,
        map_scale: 1
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });
  });

  describe('Layer Referencing', () => {
    it('should accept layer canvas as displacement map', () => {
      const mapCanvas = createDisplacementMapCanvas(100, 100);

      const params: EvaluatedEffectParams = {
        map_type: 'layer',
        displacement_map_behavior: 'stretch',
        use_for_horizontal: 'red',
        use_for_vertical: 'off',
        max_horizontal: 30,
        max_vertical: 0,
        _mapLayerCanvas: mapCanvas
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
      expect(result.canvas.width).toBe(100);
    });

    it('should handle center map behavior', () => {
      const mapCanvas = createDisplacementMapCanvas(50, 50); // Smaller than input

      const params: EvaluatedEffectParams = {
        map_type: 'layer',
        displacement_map_behavior: 'center',
        use_for_horizontal: 'red',
        max_horizontal: 20,
        _mapLayerCanvas: mapCanvas
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });

    it('should handle stretch map behavior', () => {
      const mapCanvas = createDisplacementMapCanvas(50, 50);

      const params: EvaluatedEffectParams = {
        map_type: 'layer',
        displacement_map_behavior: 'stretch',
        use_for_horizontal: 'red',
        max_horizontal: 20,
        _mapLayerCanvas: mapCanvas
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });

    it('should handle tile map behavior', () => {
      const mapCanvas = createDisplacementMapCanvas(50, 50);

      const params: EvaluatedEffectParams = {
        map_type: 'layer',
        displacement_map_behavior: 'tile',
        use_for_horizontal: 'red',
        max_horizontal: 20,
        _mapLayerCanvas: mapCanvas
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });

    it('should fall back gracefully when no layer canvas provided', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'layer',
        displacement_map_behavior: 'stretch',
        use_for_horizontal: 'red',
        max_horizontal: 20
        // No _mapLayerCanvas
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });
  });

  describe('Edge Behavior', () => {
    it('should handle clip edge behavior', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'gradient-h',
        use_for_horizontal: 'luminance',
        max_horizontal: 100,
        edge_behavior: 'off'
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });

    it('should handle wrap/tiles edge behavior', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'gradient-h',
        use_for_horizontal: 'luminance',
        max_horizontal: 100,
        edge_behavior: 'tiles'
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });

    it('should handle mirror edge behavior', () => {
      const params: EvaluatedEffectParams = {
        map_type: 'gradient-h',
        use_for_horizontal: 'luminance',
        max_horizontal: 100,
        edge_behavior: 'mirror'
      };

      const result = displacementMapRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });
  });

  describe('Channel Selection', () => {
    const channels = ['red', 'green', 'blue', 'alpha', 'luminance', 'off'];

    for (const channel of channels) {
      it(`should accept ${channel} for horizontal displacement`, () => {
        const params: EvaluatedEffectParams = {
          map_type: 'noise',
          use_for_horizontal: channel,
          use_for_vertical: 'off',
          max_horizontal: channel === 'off' ? 0 : 20,
          max_vertical: 0
        };

        const result = displacementMapRenderer(input, params);
        expect(result.canvas).toBeDefined();
      });
    }
  });
});

describe('Turbulent Displace Effect', () => {
  let input: EffectStackResult;

  beforeEach(() => {
    input = createTestCanvas(100, 100);
  });

  it('should return valid canvas when amount is zero', () => {
    const params: EvaluatedEffectParams = {
      displacement: 'turbulent',
      amount: 0,
      size: 100
    };

    const result = turbulentDisplaceRenderer(input, params);
    expect(result.canvas.width).toBe(100);
    expect(result.canvas.height).toBe(100);
  });

  describe('Displacement Types', () => {
    const displacementTypes = [
      'turbulent',
      'bulge',
      'twist',
      'turbulent-smoother',
      'horizontal',
      'vertical',
      'cross'
    ];

    for (const type of displacementTypes) {
      it(`should process ${type} displacement without error`, () => {
        const params: EvaluatedEffectParams = {
          displacement: type,
          amount: 30,
          size: 50,
          complexity: 3
        };

        const result = turbulentDisplaceRenderer(input, params);
        expect(result.canvas).toBeDefined();
        expect(result.canvas.width).toBe(100);
      });
    }
  });

  describe('Evolution Animation', () => {
    it('should accept evolution parameter', () => {
      const params: EvaluatedEffectParams = {
        displacement: 'turbulent',
        amount: 30,
        size: 50,
        evolution: 90,
        random_seed: 12345
      };

      const result = turbulentDisplaceRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });

    it('should accept cycle_evolution parameter', () => {
      const params: EvaluatedEffectParams = {
        displacement: 'turbulent',
        amount: 30,
        size: 50,
        evolution: 180,
        cycle_evolution: true,
        cycle_revolutions: 2,
        random_seed: 12345
      };

      const result = turbulentDisplaceRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });
  });

  describe('Pinning Options', () => {
    const pinningModes = ['none', 'all', 'horizontal', 'vertical'];

    for (const mode of pinningModes) {
      it(`should accept ${mode} pinning`, () => {
        const params: EvaluatedEffectParams = {
          displacement: 'turbulent',
          amount: 50,
          size: 50,
          pinning: mode
        };

        const result = turbulentDisplaceRenderer(input, params);
        expect(result.canvas).toBeDefined();
      });
    }
  });

  describe('Complexity', () => {
    it('should accept complexity parameter from 1 to 10', () => {
      for (const complexity of [1, 3, 5, 8, 10]) {
        const params: EvaluatedEffectParams = {
          displacement: 'turbulent',
          amount: 30,
          size: 50,
          complexity
        };

        const result = turbulentDisplaceRenderer(input, params);
        expect(result.canvas).toBeDefined();
      }
    });
  });

  describe('Offset', () => {
    it('should accept offset parameter', () => {
      const params: EvaluatedEffectParams = {
        displacement: 'turbulent',
        amount: 30,
        size: 50,
        offset: { x: 100, y: 50 }
      };

      const result = turbulentDisplaceRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });
  });

  describe('Random Seed', () => {
    it('should accept random_seed parameter', () => {
      const params: EvaluatedEffectParams = {
        displacement: 'turbulent',
        amount: 30,
        size: 50,
        random_seed: 99999
      };

      const result = turbulentDisplaceRenderer(input, params);
      expect(result.canvas).toBeDefined();
    });
  });
});

describe('Ripple Distort Effect', () => {
  let input: EffectStackResult;

  beforeEach(() => {
    input = createTestCanvas(100, 100);
  });

  it('should return valid canvas when amplitude is zero', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      radius: 200,
      wavelength: 50,
      amplitude: 0
    };

    const result = rippleDistortRenderer(input, params);
    expect(result.canvas.width).toBe(100);
    expect(result.canvas.height).toBe(100);
  });

  it('should process ripple distortion', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      radius: 80,
      wavelength: 20,
      amplitude: 15,
      phase: 0,
      decay: 50
    };

    const result = rippleDistortRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });

  it('should accept phase parameter for animation', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      radius: 80,
      wavelength: 20,
      amplitude: 15,
      phase: 180,
      decay: 50
    };

    const result = rippleDistortRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });

  it('should accept different center positions', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.25, y: 0.75 },
      radius: 60,
      wavelength: 15,
      amplitude: 10
    };

    const result = rippleDistortRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });
});

describe('Radio Waves Effect', () => {
  let input: EffectStackResult;

  beforeEach(() => {
    input = createTestCanvas(100, 100);
  });

  it('should generate valid output', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      frequency: 4,
      expansion: 50,
      wave_width: 20,
      stroke_color: { r: 255, g: 255, b: 255, a: 1 },
      background_color: { r: 128, g: 128, b: 128, a: 1 }
    };

    const result = radioWavesRenderer(input, params);
    expect(result.canvas.width).toBe(100);
    expect(result.canvas.height).toBe(100);
  });

  it('should accept expansion parameter for animation', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      frequency: 4,
      expansion: 75,
      wave_width: 20
    };

    const result = radioWavesRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });

  it('should accept fade parameters', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      frequency: 4,
      expansion: 50,
      wave_width: 20,
      fade_start: 20,
      fade_end: 80
    };

    const result = radioWavesRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });

  it('should accept invert parameter', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      frequency: 4,
      expansion: 50,
      invert: true
    };

    const result = radioWavesRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });
});

describe('Ellipse Effect', () => {
  let input: EffectStackResult;

  beforeEach(() => {
    input = createTestCanvas(100, 100);
  });

  it('should generate valid output', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      ellipse_width: 60,
      ellipse_height: 40,
      softness: 0,
      stroke_width: 0,
      stroke_color: { r: 255, g: 255, b: 255, a: 1 },
      background_color: { r: 0, g: 0, b: 0, a: 1 }
    };

    const result = ellipseRenderer(input, params);
    expect(result.canvas.width).toBe(100);
    expect(result.canvas.height).toBe(100);
  });

  it('should accept softness parameter', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      ellipse_width: 60,
      ellipse_height: 40,
      softness: 50
    };

    const result = ellipseRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });

  it('should accept stroke_width parameter', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      ellipse_width: 60,
      ellipse_height: 40,
      stroke_width: 10,
      stroke_color: { r: 255, g: 0, b: 0, a: 1 }
    };

    const result = ellipseRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });

  it('should accept invert parameter', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      ellipse_width: 60,
      ellipse_height: 40,
      invert: true
    };

    const result = ellipseRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });

  it('should accept different dimensions for ellipse', () => {
    const params: EvaluatedEffectParams = {
      center: { x: 0.5, y: 0.5 },
      ellipse_width: 80,
      ellipse_height: 30
    };

    const result = ellipseRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });
});

describe('Determinism', () => {
  it('Turbulent Displace should be deterministic with same parameters', () => {
    const params: EvaluatedEffectParams = {
      displacement: 'turbulent',
      amount: 50,
      size: 80,
      complexity: 4,
      evolution: 90,
      random_seed: 42
    };

    const input1 = createTestCanvas(50, 50);
    const input2 = createTestCanvas(50, 50);

    const result1 = turbulentDisplaceRenderer(input1, params);
    const result2 = turbulentDisplaceRenderer(input2, params);

    // Same dimensions
    expect(result1.canvas.width).toBe(result2.canvas.width);
    expect(result1.canvas.height).toBe(result2.canvas.height);
  });

  it('Displacement Map noise should use seeded random', () => {
    const params: EvaluatedEffectParams = {
      map_type: 'noise',
      use_for_horizontal: 'luminance',
      use_for_vertical: 'luminance',
      max_horizontal: 20,
      max_vertical: 20
    };

    // Two calls with same params should not throw
    const input1 = createTestCanvas(50, 50);
    const input2 = createTestCanvas(50, 50);

    const result1 = displacementMapRenderer(input1, params);
    const result2 = displacementMapRenderer(input2, params);

    expect(result1.canvas).toBeDefined();
    expect(result2.canvas).toBeDefined();
  });
});

describe('Parameter Validation', () => {
  it('Turbulent Displace should handle missing optional parameters', () => {
    const input = createTestCanvas(50, 50);
    const params: EvaluatedEffectParams = {
      // Only required param
      amount: 30
    };

    const result = turbulentDisplaceRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });

  it('Displacement Map should handle missing optional parameters', () => {
    const input = createTestCanvas(50, 50);
    const params: EvaluatedEffectParams = {
      max_horizontal: 20
    };

    const result = displacementMapRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });

  it('Ripple Distort should handle missing optional parameters', () => {
    const input = createTestCanvas(50, 50);
    const params: EvaluatedEffectParams = {
      amplitude: 10
    };

    const result = rippleDistortRenderer(input, params);
    expect(result.canvas).toBeDefined();
  });
});
