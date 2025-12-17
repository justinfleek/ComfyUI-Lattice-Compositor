/**
 * Distort Effect Renderers
 *
 * Implements distortion effects: Transform, Warp, Displacement Map
 * These effects manipulate pixel positions rather than colors.
 */
import {
  registerEffectRenderer,
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams
} from '../effectProcessor';

// ============================================================================
// TRANSFORM EFFECT
// ============================================================================

/**
 * Transform effect renderer
 * Applies anchor point, position, scale, skew, rotation, and opacity
 *
 * Parameters:
 * - anchor_point: { x, y } normalized (0-1)
 * - position: { x, y } normalized (0-1)
 * - scale_width: percentage
 * - scale_height: percentage
 * - skew: degrees (-85 to 85)
 * - skew_axis: degrees
 * - rotation: degrees
 * - opacity: percentage (0-100)
 */
export function transformRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const anchorPoint = params.anchor_point ?? { x: 0.5, y: 0.5 };
  const position = params.position ?? { x: 0.5, y: 0.5 };
  const scaleWidth = (params.scale_width ?? 100) / 100;
  const scaleHeight = (params.scale_height ?? 100) / 100;
  const skew = (params.skew ?? 0) * Math.PI / 180;
  const skewAxis = (params.skew_axis ?? 0) * Math.PI / 180;
  const rotation = (params.rotation ?? 0) * Math.PI / 180;
  const opacity = (params.opacity ?? 100) / 100;

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  // Calculate pixel positions
  const anchorX = anchorPoint.x * width;
  const anchorY = anchorPoint.y * height;
  const posX = position.x * width;
  const posY = position.y * height;

  // Apply transform
  output.ctx.globalAlpha = opacity;
  output.ctx.translate(posX, posY);
  output.ctx.rotate(rotation);

  // Apply skew
  if (skew !== 0) {
    const skewX = Math.tan(skew) * Math.cos(skewAxis);
    const skewY = Math.tan(skew) * Math.sin(skewAxis);
    output.ctx.transform(1, skewY, skewX, 1, 0, 0);
  }

  output.ctx.scale(scaleWidth, scaleHeight);
  output.ctx.translate(-anchorX, -anchorY);

  output.ctx.drawImage(input.canvas, 0, 0);
  output.ctx.setTransform(1, 0, 0, 1, 0, 0);
  output.ctx.globalAlpha = 1;

  return output;
}

// ============================================================================
// WARP EFFECT
// ============================================================================

/**
 * Warp effect renderer
 * Applies various warp distortions
 *
 * Parameters:
 * - warp_style: 'arc' | 'bulge' | 'wave' | 'fisheye' | 'twist' | etc.
 * - bend: -100 to 100
 * - horizontal_distortion: -100 to 100
 * - vertical_distortion: -100 to 100
 */
export function warpRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const warpStyle = params.warp_style ?? 'arc';
  const bend = (params.bend ?? 0) / 100;
  const hDistort = (params.horizontal_distortion ?? 0) / 100;
  const vDistort = (params.vertical_distortion ?? 0) / 100;

  // No warp needed
  if (bend === 0 && hDistort === 0 && vDistort === 0) {
    return input;
  }

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;

  const centerX = width / 2;
  const centerY = height / 2;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      // Normalize coordinates to -1 to 1
      const nx = (x - centerX) / centerX;
      const ny = (y - centerY) / centerY;

      let srcX = x;
      let srcY = y;

      // Apply warp based on style
      switch (warpStyle) {
        case 'arc': {
          const arcBend = bend * ny * ny;
          srcX = x + arcBend * centerX * nx;
          break;
        }
        case 'bulge': {
          const r = Math.sqrt(nx * nx + ny * ny);
          if (r < 1) {
            const factor = 1 + bend * (1 - r * r);
            srcX = centerX + (x - centerX) / factor;
            srcY = centerY + (y - centerY) / factor;
          }
          break;
        }
        case 'wave': {
          srcX = x + Math.sin(ny * Math.PI * 2) * bend * width * 0.1;
          srcY = y + Math.sin(nx * Math.PI * 2) * bend * height * 0.1;
          break;
        }
        case 'fisheye': {
          const r = Math.sqrt(nx * nx + ny * ny);
          if (r > 0 && r < 1) {
            const theta = Math.atan2(ny, nx);
            const newR = Math.pow(r, 1 + bend);
            srcX = centerX + newR * Math.cos(theta) * centerX;
            srcY = centerY + newR * Math.sin(theta) * centerY;
          }
          break;
        }
        case 'twist': {
          const r = Math.sqrt(nx * nx + ny * ny);
          const angle = bend * Math.PI * (1 - r);
          const cos = Math.cos(angle);
          const sin = Math.sin(angle);
          srcX = centerX + (nx * cos - ny * sin) * centerX;
          srcY = centerY + (nx * sin + ny * cos) * centerY;
          break;
        }
        default:
          // Pass through for unimplemented styles
          break;
      }

      // Apply horizontal and vertical distortion
      srcX += hDistort * centerX * (1 - ny * ny);
      srcY += vDistort * centerY * (1 - nx * nx);

      // Clamp to bounds
      srcX = Math.max(0, Math.min(width - 1, srcX));
      srcY = Math.max(0, Math.min(height - 1, srcY));

      // Bilinear interpolation
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, width - 1);
      const y1 = Math.min(y0 + 1, height - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;

      const idx00 = (y0 * width + x0) * 4;
      const idx01 = (y0 * width + x1) * 4;
      const idx10 = (y1 * width + x0) * 4;
      const idx11 = (y1 * width + x1) * 4;
      const outIdx = (y * width + x) * 4;

      for (let c = 0; c < 4; c++) {
        const v00 = src[idx00 + c];
        const v01 = src[idx01 + c];
        const v10 = src[idx10 + c];
        const v11 = src[idx11 + c];

        dst[outIdx + c] = Math.round(
          v00 * (1 - fx) * (1 - fy) +
          v01 * fx * (1 - fy) +
          v10 * (1 - fx) * fy +
          v11 * fx * fy
        );
      }
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// DISPLACEMENT MAP EFFECT
// ============================================================================

/**
 * Displacement Map effect renderer
 * Displaces pixels based on a map layer (stub - requires layer access)
 *
 * Parameters:
 * - displacement_map_layer: layer reference
 * - use_for_horizontal: 'red' | 'green' | 'blue' | 'alpha' | 'luminance'
 * - max_horizontal: pixels
 * - use_for_vertical: 'red' | 'green' | 'blue' | 'alpha' | 'luminance'
 * - max_vertical: pixels
 */
export function displacementMapRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // Displacement map requires a reference layer which isn't available yet
  // For now, return pass-through
  // TODO: Implement when layer reference system is available
  return input;
}

// ============================================================================
// REGISTRATION
// ============================================================================

/**
 * Register all distort effect renderers
 */
export function registerDistortEffects(): void {
  registerEffectRenderer('transform', transformRenderer);
  registerEffectRenderer('warp', warpRenderer);
  registerEffectRenderer('displacement-map', displacementMapRenderer);
}

export default {
  transformRenderer,
  warpRenderer,
  displacementMapRenderer,
  registerDistortEffects
};
