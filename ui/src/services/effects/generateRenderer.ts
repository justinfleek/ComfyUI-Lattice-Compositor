/**
 * Generate Effect Renderers
 *
 * Implements generative effects: Fill, Gradient Ramp, Fractal Noise
 * These effects create or modify content procedurally.
 */
import {
  registerEffectRenderer,
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams
} from '../effectProcessor';

// ============================================================================
// FILL EFFECT
// ============================================================================

/**
 * Fill effect renderer
 * Fills the layer with a solid color
 *
 * Parameters:
 * - fill_mask: 'all' | 'none'
 * - color: { r, g, b, a }
 * - invert: boolean
 * - horizontal_feather: pixels
 * - vertical_feather: pixels
 * - opacity: percentage (0-100)
 */
export function fillRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const color = params.color ?? { r: 255, g: 0, b: 0, a: 1 };
  const opacity = (params.opacity ?? 100) / 100;
  const invert = params.invert ?? false;

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  // Get original image data for alpha masking
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;

  // Normalize color
  const r = color.r ?? 255;
  const g = color.g ?? 0;
  const b = color.b ?? 0;
  const a = (color.a ?? 1) * 255 * opacity;

  for (let i = 0; i < src.length; i += 4) {
    const srcAlpha = src[i + 3] / 255;

    if (invert) {
      // Fill where original is transparent
      const fillAmount = 1 - srcAlpha;
      dst[i] = Math.round(r * fillAmount + src[i] * (1 - fillAmount));
      dst[i + 1] = Math.round(g * fillAmount + src[i + 1] * (1 - fillAmount));
      dst[i + 2] = Math.round(b * fillAmount + src[i + 2] * (1 - fillAmount));
      dst[i + 3] = Math.max(src[i + 3], Math.round(a * fillAmount));
    } else {
      // Fill where original is opaque
      dst[i] = Math.round(r * srcAlpha * opacity + src[i] * (1 - opacity));
      dst[i + 1] = Math.round(g * srcAlpha * opacity + src[i + 1] * (1 - opacity));
      dst[i + 2] = Math.round(b * srcAlpha * opacity + src[i + 2] * (1 - opacity));
      dst[i + 3] = src[i + 3];
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// GRADIENT RAMP EFFECT
// ============================================================================

/**
 * Gradient Ramp effect renderer
 * Generates a color gradient
 *
 * Parameters:
 * - start_of_ramp: { x, y } normalized (0-1)
 * - start_color: { r, g, b, a }
 * - end_of_ramp: { x, y } normalized (0-1)
 * - end_color: { r, g, b, a }
 * - ramp_shape: 'linear' | 'radial'
 * - ramp_scatter: 0-100
 * - blend_with_original: 0-100
 */
export function gradientRampRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const startPoint = params.start_of_ramp ?? { x: 0, y: 0.5 };
  const startColor = params.start_color ?? { r: 0, g: 0, b: 0, a: 1 };
  const endPoint = params.end_of_ramp ?? { x: 1, y: 0.5 };
  const endColor = params.end_color ?? { r: 255, g: 255, b: 255, a: 1 };
  const rampShape = params.ramp_shape ?? 'linear';
  const scatter = (params.ramp_scatter ?? 0) / 100;
  const blend = (params.blend_with_original ?? 0) / 100;

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  // Create gradient
  let gradient: CanvasGradient;

  if (rampShape === 'radial') {
    const cx = startPoint.x * width;
    const cy = startPoint.y * height;
    const dx = (endPoint.x - startPoint.x) * width;
    const dy = (endPoint.y - startPoint.y) * height;
    const radius = Math.sqrt(dx * dx + dy * dy);

    gradient = output.ctx.createRadialGradient(cx, cy, 0, cx, cy, radius);
  } else {
    gradient = output.ctx.createLinearGradient(
      startPoint.x * width,
      startPoint.y * height,
      endPoint.x * width,
      endPoint.y * height
    );
  }

  const startRgba = `rgba(${startColor.r}, ${startColor.g}, ${startColor.b}, ${startColor.a ?? 1})`;
  const endRgba = `rgba(${endColor.r}, ${endColor.g}, ${endColor.b}, ${endColor.a ?? 1})`;

  gradient.addColorStop(0, startRgba);
  gradient.addColorStop(1, endRgba);

  // Draw gradient
  output.ctx.fillStyle = gradient;
  output.ctx.fillRect(0, 0, width, height);

  // Apply scatter (noise dithering)
  if (scatter > 0) {
    const outputData = output.ctx.getImageData(0, 0, width, height);
    const dst = outputData.data;
    const scatterAmount = scatter * 25;

    for (let i = 0; i < dst.length; i += 4) {
      const noise = (Math.random() - 0.5) * scatterAmount;
      dst[i] = Math.max(0, Math.min(255, dst[i] + noise));
      dst[i + 1] = Math.max(0, Math.min(255, dst[i + 1] + noise));
      dst[i + 2] = Math.max(0, Math.min(255, dst[i + 2] + noise));
    }

    output.ctx.putImageData(outputData, 0, 0);
  }

  // Blend with original
  if (blend > 0) {
    output.ctx.globalAlpha = blend;
    output.ctx.drawImage(input.canvas, 0, 0);
    output.ctx.globalAlpha = 1;
  }

  return output;
}

// ============================================================================
// FRACTAL NOISE EFFECT
// ============================================================================

/**
 * Simple noise function for fractal noise
 */
function noise2D(x: number, y: number, seed: number): number {
  const n = Math.sin(x * 12.9898 + y * 78.233 + seed) * 43758.5453;
  return n - Math.floor(n);
}

/**
 * Smoothed noise with interpolation
 */
function smoothNoise(x: number, y: number, seed: number): number {
  const x0 = Math.floor(x);
  const y0 = Math.floor(y);
  const fx = x - x0;
  const fy = y - y0;

  const v00 = noise2D(x0, y0, seed);
  const v10 = noise2D(x0 + 1, y0, seed);
  const v01 = noise2D(x0, y0 + 1, seed);
  const v11 = noise2D(x0 + 1, y0 + 1, seed);

  // Smooth interpolation
  const sx = fx * fx * (3 - 2 * fx);
  const sy = fy * fy * (3 - 2 * fy);

  return (
    v00 * (1 - sx) * (1 - sy) +
    v10 * sx * (1 - sy) +
    v01 * (1 - sx) * sy +
    v11 * sx * sy
  );
}

/**
 * Fractal Noise effect renderer
 * Generates procedural noise patterns
 *
 * Parameters:
 * - fractal_type: 'basic' | 'turbulent-basic' | etc.
 * - noise_type: 'block' | 'linear' | 'soft-linear' | 'spline'
 * - invert: boolean
 * - contrast: 0-400
 * - brightness: -200 to 200
 * - scale: 10-10000
 * - complexity: 1-20 (octaves)
 * - evolution: angle (for animation)
 */
export function fractalNoiseRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const fractalType = params.fractal_type ?? 'basic';
  const invert = params.invert ?? false;
  const contrast = (params.contrast ?? 100) / 100;
  const brightness = (params.brightness ?? 0) / 100;
  const scale = params.scale ?? 100;
  const complexity = Math.max(1, Math.min(20, params.complexity ?? 6));
  const evolution = (params.evolution ?? 0) * Math.PI / 180;

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;

  const seed = evolution * 1000;
  const isTurbulent = fractalType.includes('turbulent');

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let value = 0;
      let amplitude = 1;
      let frequency = 1;
      let maxValue = 0;

      // Fractal sum (fBm)
      for (let octave = 0; octave < complexity; octave++) {
        const sampleX = (x / scale) * frequency;
        const sampleY = (y / scale) * frequency;

        let noiseValue = smoothNoise(sampleX, sampleY, seed + octave * 100);

        if (isTurbulent) {
          noiseValue = Math.abs(noiseValue * 2 - 1);
        }

        value += noiseValue * amplitude;
        maxValue += amplitude;

        amplitude *= 0.5;
        frequency *= 2;
      }

      // Normalize
      value /= maxValue;

      // Apply contrast and brightness
      value = (value - 0.5) * contrast + 0.5 + brightness;

      // Invert if needed
      if (invert) {
        value = 1 - value;
      }

      // Clamp
      value = Math.max(0, Math.min(1, value));

      const pixelValue = Math.round(value * 255);
      const idx = (y * width + x) * 4;
      dst[idx] = pixelValue;
      dst[idx + 1] = pixelValue;
      dst[idx + 2] = pixelValue;
      dst[idx + 3] = 255;
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// REGISTRATION
// ============================================================================

/**
 * Register all generate effect renderers
 */
export function registerGenerateEffects(): void {
  registerEffectRenderer('fill', fillRenderer);
  registerEffectRenderer('gradient-ramp', gradientRampRenderer);
  registerEffectRenderer('fractal-noise', fractalNoiseRenderer);
}

export default {
  fillRenderer,
  gradientRampRenderer,
  fractalNoiseRenderer,
  registerGenerateEffects
};
