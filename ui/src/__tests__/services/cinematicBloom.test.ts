/**
 * Tests for Cinematic Bloom Effect
 */
import { describe, it, expect, beforeEach } from 'vitest';
import {
  cinematicBloomRenderer,
  glowRenderer,
  tonemapACES,
  tonemapReinhard,
  tonemapHable,
  generateInverseSquareKernel,
  generateGaussianKernel,
  generateLensDirt,
  applyChromaticAberration
} from '../../services/effects/cinematicBloom';

// Helper to create test canvas
function createTestCanvas(width: number, height: number, fillColor?: { r: number; g: number; b: number; a: number }): HTMLCanvasElement {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext('2d')!;

  if (fillColor) {
    ctx.fillStyle = `rgba(${fillColor.r}, ${fillColor.g}, ${fillColor.b}, ${fillColor.a})`;
    ctx.fillRect(0, 0, width, height);
  }

  return canvas;
}

// Helper to create EffectStackResult
function createEffectInput(width: number, height: number, fillColor?: { r: number; g: number; b: number; a: number }) {
  const canvas = createTestCanvas(width, height, fillColor);
  return {
    canvas,
    ctx: canvas.getContext('2d')!
  };
}

describe('Cinematic Bloom - Tonemapping', () => {
  describe('tonemapACES', () => {
    it('should return 0 for input 0', () => {
      expect(tonemapACES(0)).toBe(0);
    });

    it('should return value < 1 for input 1', () => {
      const result = tonemapACES(1);
      expect(result).toBeGreaterThan(0);
      expect(result).toBeLessThan(1);
    });

    it('should approach 1 for high values', () => {
      const result = tonemapACES(10);
      expect(result).toBeGreaterThan(0.9);
      expect(result).toBeLessThanOrEqual(1);
    });

    it('should be monotonically increasing', () => {
      const values = [0, 0.1, 0.5, 1, 2, 5, 10];
      for (let i = 1; i < values.length; i++) {
        expect(tonemapACES(values[i])).toBeGreaterThan(tonemapACES(values[i - 1]));
      }
    });
  });

  describe('tonemapReinhard', () => {
    it('should return 0 for input 0', () => {
      expect(tonemapReinhard(0)).toBe(0);
    });

    it('should return ~0.5 for input 1', () => {
      const result = tonemapReinhard(1);
      expect(result).toBeCloseTo(0.5, 1);
    });

    it('should be monotonically increasing', () => {
      const values = [0, 0.1, 0.5, 1, 2, 5, 10];
      for (let i = 1; i < values.length; i++) {
        expect(tonemapReinhard(values[i])).toBeGreaterThan(tonemapReinhard(values[i - 1]));
      }
    });
  });

  describe('tonemapHable', () => {
    it('should return value near 0 for input 0', () => {
      // Hable has a toe so it's not exactly 0
      expect(tonemapHable(0)).toBeLessThan(0.1);
    });

    it('should be monotonically increasing for positive values', () => {
      const values = [0.1, 0.5, 1, 2, 5, 10];
      for (let i = 1; i < values.length; i++) {
        expect(tonemapHable(values[i])).toBeGreaterThan(tonemapHable(values[i - 1]));
      }
    });
  });
});

describe('Cinematic Bloom - Kernel Generation', () => {
  describe('generateInverseSquareKernel', () => {
    it('should generate kernel with correct size', () => {
      const kernel = generateInverseSquareKernel(10);
      expect(kernel.length).toBe(21); // 10 * 2 + 1
    });

    it('should sum to approximately 1 (normalized)', () => {
      const kernel = generateInverseSquareKernel(20);
      const sum = kernel.reduce((a, b) => a + b, 0);
      expect(sum).toBeCloseTo(1, 5);
    });

    it('should have maximum at center', () => {
      const kernel = generateInverseSquareKernel(15);
      const center = Math.floor(kernel.length / 2);
      for (let i = 0; i < kernel.length; i++) {
        if (i !== center) {
          expect(kernel[center]).toBeGreaterThanOrEqual(kernel[i]);
        }
      }
    });

    it('should be symmetric', () => {
      const kernel = generateInverseSquareKernel(10);
      const n = kernel.length;
      for (let i = 0; i < Math.floor(n / 2); i++) {
        expect(kernel[i]).toBeCloseTo(kernel[n - 1 - i], 10);
      }
    });
  });

  describe('generateGaussianKernel', () => {
    it('should generate kernel with correct size', () => {
      const kernel = generateGaussianKernel(10);
      expect(kernel.length).toBe(21);
    });

    it('should sum to approximately 1', () => {
      const kernel = generateGaussianKernel(20);
      const sum = kernel.reduce((a, b) => a + b, 0);
      expect(sum).toBeCloseTo(1, 5);
    });

    it('should be symmetric', () => {
      const kernel = generateGaussianKernel(10);
      const n = kernel.length;
      for (let i = 0; i < Math.floor(n / 2); i++) {
        expect(kernel[i]).toBeCloseTo(kernel[n - 1 - i], 10);
      }
    });
  });

  describe('inverse-square vs gaussian comparison', () => {
    it('inverse-square should have longer tails than gaussian', () => {
      const radius = 20;
      const invSq = generateInverseSquareKernel(radius);
      const gauss = generateGaussianKernel(radius);

      // Check the edge values - inverse-square should have more weight at edges
      const edgeIdx = 0;
      const centerIdx = Math.floor(invSq.length / 2);

      // Normalize by center value to compare tail ratio
      const invSqTailRatio = invSq[edgeIdx] / invSq[centerIdx];
      const gaussTailRatio = gauss[edgeIdx] / gauss[centerIdx];

      expect(invSqTailRatio).toBeGreaterThan(gaussTailRatio);
    });
  });
});

describe('Cinematic Bloom - Lens Dirt', () => {
  describe('generateLensDirt', () => {
    it('should generate array of correct size', () => {
      const dirt = generateLensDirt(100, 100, 1);
      expect(dirt.length).toBe(100 * 100);
    });

    it('should have values between 0 and 1', () => {
      const dirt = generateLensDirt(50, 50, 1);
      for (const value of dirt) {
        expect(value).toBeGreaterThanOrEqual(0);
        expect(value).toBeLessThanOrEqual(1);
      }
    });

    it('should be deterministic with same seed', () => {
      const dirt1 = generateLensDirt(50, 50, 1, 12345);
      const dirt2 = generateLensDirt(50, 50, 1, 12345);

      for (let i = 0; i < dirt1.length; i++) {
        expect(dirt1[i]).toBe(dirt2[i]);
      }
    });

    it('should differ with different seeds', () => {
      const dirt1 = generateLensDirt(50, 50, 1, 12345);
      const dirt2 = generateLensDirt(50, 50, 1, 54321);

      let differences = 0;
      for (let i = 0; i < dirt1.length; i++) {
        if (dirt1[i] !== dirt2[i]) differences++;
      }

      expect(differences).toBeGreaterThan(dirt1.length * 0.5);
    });
  });
});

describe('Cinematic Bloom - Chromatic Aberration', () => {
  describe('applyChromaticAberration', () => {
    it('should return image of same dimensions', () => {
      const canvas = createTestCanvas(100, 100, { r: 255, g: 128, b: 64, a: 255 });
      const ctx = canvas.getContext('2d')!;
      const imageData = ctx.getImageData(0, 0, 100, 100);

      const result = applyChromaticAberration(imageData, 5);

      expect(result.width).toBe(100);
      expect(result.height).toBe(100);
    });

    it('should return original when amount is 0', () => {
      const canvas = createTestCanvas(50, 50, { r: 255, g: 128, b: 64, a: 255 });
      const ctx = canvas.getContext('2d')!;
      const imageData = ctx.getImageData(0, 0, 50, 50);

      const result = applyChromaticAberration(imageData, 0);

      // Should be same object reference when amount is 0
      expect(result).toBe(imageData);
    });

    it('should modify pixel data when amount > 0', () => {
      // Create a non-uniform image manually - chromatic aberration needs varying content
      const canvas = document.createElement('canvas');
      canvas.width = 50;
      canvas.height = 50;
      const ctx = canvas.getContext('2d')!;
      const imageData = ctx.createImageData(50, 50);

      // Create a pattern with varying colors - bright center, dark edges
      for (let y = 0; y < 50; y++) {
        for (let x = 0; x < 50; x++) {
          const idx = (y * 50 + x) * 4;
          // Create a radial pattern
          const dx = x - 25;
          const dy = y - 25;
          const dist = Math.sqrt(dx * dx + dy * dy);
          const intensity = Math.max(0, 255 - dist * 8);

          imageData.data[idx] = intensity;       // R - varies
          imageData.data[idx + 1] = 128;         // G - constant
          imageData.data[idx + 2] = 255 - intensity; // B - inverse of R
          imageData.data[idx + 3] = 255;         // A
        }
      }

      const originalData = new Uint8ClampedArray(imageData.data);

      const result = applyChromaticAberration(imageData, 10);

      // At least some pixels should be different (especially near edges where channel offsets diverge)
      let differences = 0;
      for (let i = 0; i < result.data.length; i++) {
        if (result.data[i] !== originalData[i]) differences++;
      }

      expect(differences).toBeGreaterThan(0);
    });
  });
});

describe('Cinematic Bloom - Main Renderer', () => {
  describe('cinematicBloomRenderer', () => {
    it('should return canvas of same dimensions', () => {
      const input = createEffectInput(100, 100, { r: 255, g: 255, b: 255, a: 255 });

      const result = cinematicBloomRenderer(input, {
        intensity: 1,
        threshold: 0.5,
        radius: 10
      });

      expect(result.canvas.width).toBe(100);
      expect(result.canvas.height).toBe(100);
    });

    it('should return input unchanged when intensity is 0', () => {
      const input = createEffectInput(50, 50, { r: 128, g: 128, b: 128, a: 255 });

      const result = cinematicBloomRenderer(input, {
        intensity: 0,
        threshold: 0.5,
        radius: 10
      });

      expect(result).toBe(input);
    });

    it('should return input unchanged when radius is 0', () => {
      const input = createEffectInput(50, 50, { r: 128, g: 128, b: 128, a: 255 });

      const result = cinematicBloomRenderer(input, {
        intensity: 1,
        threshold: 0.5,
        radius: 0
      });

      expect(result).toBe(input);
    });

    it('should handle all falloff modes without error', () => {
      const input = createEffectInput(50, 50, { r: 255, g: 255, b: 255, a: 255 });

      const modes = ['gaussian', 'inverse_square', 'exponential'];

      for (const mode of modes) {
        expect(() => {
          cinematicBloomRenderer(input, {
            intensity: 1,
            threshold: 0.5,
            radius: 10,
            falloff_mode: mode
          });
        }).not.toThrow();
      }
    });

    it('should handle all tonemap modes without error', () => {
      const input = createEffectInput(50, 50, { r: 255, g: 255, b: 255, a: 255 });

      const modes = ['none', 'aces', 'reinhard', 'hable'];

      for (const mode of modes) {
        expect(() => {
          cinematicBloomRenderer(input, {
            intensity: 1,
            threshold: 0.5,
            radius: 10,
            tonemap: mode
          });
        }).not.toThrow();
      }
    });

    it('should handle all blend modes without error', () => {
      const input = createEffectInput(50, 50, { r: 255, g: 255, b: 255, a: 255 });

      const modes = ['add', 'screen', 'overlay', 'soft_light'];

      for (const mode of modes) {
        expect(() => {
          cinematicBloomRenderer(input, {
            intensity: 1,
            threshold: 0.5,
            radius: 10,
            blend_mode: mode
          });
        }).not.toThrow();
      }
    });

    it('should apply lens dirt when enabled', () => {
      const input = createEffectInput(50, 50, { r: 255, g: 255, b: 255, a: 255 });

      expect(() => {
        cinematicBloomRenderer(input, {
          intensity: 1,
          threshold: 0.5,
          radius: 10,
          lens_dirt_enabled: true,
          lens_dirt_intensity: 0.5,
          lens_dirt_scale: 1
        });
      }).not.toThrow();
    });

    it('should apply chromatic aberration when set', () => {
      const input = createEffectInput(50, 50, { r: 255, g: 255, b: 255, a: 255 });

      expect(() => {
        cinematicBloomRenderer(input, {
          intensity: 1,
          threshold: 0.5,
          radius: 10,
          chromatic_aberration: 5
        });
      }).not.toThrow();
    });

    it('should handle per-channel radii', () => {
      const input = createEffectInput(50, 50, { r: 255, g: 255, b: 255, a: 255 });

      expect(() => {
        cinematicBloomRenderer(input, {
          intensity: 1,
          threshold: 0.5,
          radius: 20,
          radius_r: 1.5,
          radius_g: 1.0,
          radius_b: 0.8
        });
      }).not.toThrow();
    });
  });

  describe('glowRenderer (simple variant)', () => {
    it('should work with basic parameters', () => {
      const input = createEffectInput(50, 50, { r: 255, g: 255, b: 255, a: 255 });

      const result = glowRenderer(input, {
        glow_threshold: 50,
        glow_radius: 25,
        glow_intensity: 100
      });

      expect(result.canvas.width).toBe(50);
      expect(result.canvas.height).toBe(50);
    });

    it('should return input when intensity is 0', () => {
      const input = createEffectInput(50, 50, { r: 128, g: 128, b: 128, a: 255 });

      const result = glowRenderer(input, {
        glow_threshold: 50,
        glow_radius: 25,
        glow_intensity: 0
      });

      expect(result).toBe(input);
    });
  });
});

describe('Cinematic Bloom - Edge Cases', () => {
  it('should handle very small canvas', () => {
    const input = createEffectInput(1, 1, { r: 255, g: 255, b: 255, a: 255 });

    expect(() => {
      cinematicBloomRenderer(input, {
        intensity: 1,
        threshold: 0.5,
        radius: 10
      });
    }).not.toThrow();
  });

  it('should handle extreme parameter values', () => {
    const input = createEffectInput(50, 50, { r: 255, g: 255, b: 255, a: 255 });

    expect(() => {
      cinematicBloomRenderer(input, {
        intensity: 10,
        threshold: 0,
        radius: 200,
        exposure: 5,
        chromatic_aberration: 20,
        lens_dirt_enabled: true,
        lens_dirt_intensity: 1,
        lens_dirt_scale: 2
      });
    }).not.toThrow();
  });

  it('should handle black image (no bright areas)', () => {
    const input = createEffectInput(50, 50, { r: 0, g: 0, b: 0, a: 255 });

    const result = cinematicBloomRenderer(input, {
      intensity: 1,
      threshold: 0.5,
      radius: 10
    });

    // Should still produce valid output
    expect(result.canvas.width).toBe(50);
    expect(result.canvas.height).toBe(50);
  });

  it('should handle transparent image', () => {
    const input = createEffectInput(50, 50, { r: 255, g: 255, b: 255, a: 0 });

    expect(() => {
      cinematicBloomRenderer(input, {
        intensity: 1,
        threshold: 0.5,
        radius: 10
      });
    }).not.toThrow();
  });
});
