/**
 * Color Correction Effect Renderers
 *
 * Implements common color correction effects:
 * - Brightness & Contrast
 * - Hue/Saturation
 * - Levels
 * - Tint
 */
import {
  registerEffectRenderer,
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams
} from '../effectProcessor';

// ============================================================================
// BRIGHTNESS & CONTRAST
// ============================================================================

/**
 * Brightness & Contrast effect renderer
 *
 * Parameters:
 * - brightness: -150 to 150 (default 0)
 * - contrast: -100 to 100 (default 0)
 * - use_legacy: boolean (legacy mode uses simpler formula)
 */
export function brightnessContrastRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const brightness = (params.brightness ?? 0) / 100; // Normalize to -1.5 to 1.5
  const contrast = (params.contrast ?? 0) / 100;     // Normalize to -1 to 1
  const useLegacy = params.use_legacy ?? false;

  // No change needed
  if (brightness === 0 && contrast === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  // Calculate contrast factor
  const contrastFactor = useLegacy
    ? 1 + contrast
    : (259 * (contrast * 255 + 255)) / (255 * (259 - contrast * 255));

  for (let i = 0; i < data.length; i += 4) {
    // Get RGB values
    let r = data[i];
    let g = data[i + 1];
    let b = data[i + 2];

    // Apply brightness
    r += brightness * 255;
    g += brightness * 255;
    b += brightness * 255;

    // Apply contrast (center around 128)
    r = contrastFactor * (r - 128) + 128;
    g = contrastFactor * (g - 128) + 128;
    b = contrastFactor * (b - 128) + 128;

    // Clamp values
    data[i] = Math.max(0, Math.min(255, r));
    data[i + 1] = Math.max(0, Math.min(255, g));
    data[i + 2] = Math.max(0, Math.min(255, b));
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// HUE/SATURATION
// ============================================================================

/**
 * Convert RGB to HSL
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
 * Convert HSL to RGB
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

/**
 * Hue/Saturation effect renderer
 *
 * Parameters:
 * - master_hue: -180 to 180 degrees (default 0)
 * - master_saturation: -100 to 100 (default 0)
 * - master_lightness: -100 to 100 (default 0)
 * - colorize: boolean (colorize mode)
 */
export function hueSaturationRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const hueShift = (params.master_hue ?? 0) / 360; // Normalize to 0-1
  const saturationShift = (params.master_saturation ?? 0) / 100;
  const lightnessShift = (params.master_lightness ?? 0) / 100;
  const colorize = params.colorize ?? false;

  // No change needed
  if (hueShift === 0 && saturationShift === 0 && lightnessShift === 0 && !colorize) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];

    let [h, s, l] = rgbToHsl(r, g, b);

    if (colorize) {
      // Colorize mode: use hue shift as absolute hue
      h = hueShift;
      s = Math.abs(saturationShift) + 0.25; // Base saturation
    } else {
      // Normal mode: shift values
      h = (h + hueShift) % 1;
      if (h < 0) h += 1;

      // Saturation adjustment
      s = s + s * saturationShift;
    }

    // Lightness adjustment
    l = l + l * lightnessShift;

    // Clamp saturation and lightness
    s = Math.max(0, Math.min(1, s));
    l = Math.max(0, Math.min(1, l));

    const [newR, newG, newB] = hslToRgb(h, s, l);

    data[i] = newR;
    data[i + 1] = newG;
    data[i + 2] = newB;
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// LEVELS
// ============================================================================

/**
 * Levels effect renderer
 *
 * Parameters:
 * - input_black: 0-255 (default 0)
 * - input_white: 0-255 (default 255)
 * - gamma: 0.1-10 (default 1)
 * - output_black: 0-255 (default 0)
 * - output_white: 0-255 (default 255)
 */
export function levelsRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const inputBlack = params.input_black ?? 0;
  const inputWhite = params.input_white ?? 255;
  const gamma = params.gamma ?? 1;
  const outputBlack = params.output_black ?? 0;
  const outputWhite = params.output_white ?? 255;

  // No change needed
  if (inputBlack === 0 && inputWhite === 255 && gamma === 1 &&
      outputBlack === 0 && outputWhite === 255) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  // Build lookup table for performance
  const lut = new Uint8Array(256);
  const inputRange = inputWhite - inputBlack;
  const outputRange = outputWhite - outputBlack;

  for (let i = 0; i < 256; i++) {
    // Input levels
    let value = (i - inputBlack) / inputRange;
    value = Math.max(0, Math.min(1, value));

    // Gamma correction
    value = Math.pow(value, 1 / gamma);

    // Output levels
    value = outputBlack + value * outputRange;
    value = Math.max(0, Math.min(255, value));

    lut[i] = Math.round(value);
  }

  // Apply LUT to all pixels
  for (let i = 0; i < data.length; i += 4) {
    data[i] = lut[data[i]];
    data[i + 1] = lut[data[i + 1]];
    data[i + 2] = lut[data[i + 2]];
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// TINT
// ============================================================================

/**
 * Tint effect renderer - maps black to one color and white to another
 *
 * Parameters:
 * - map_black_to: color { r, g, b, a } (default black)
 * - map_white_to: color { r, g, b, a } (default white)
 * - amount_to_tint: 0-100 (default 100)
 */
export function tintRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const blackColor = params.map_black_to ?? { r: 0, g: 0, b: 0 };
  const whiteColor = params.map_white_to ?? { r: 255, g: 255, b: 255 };
  const amount = (params.amount_to_tint ?? 100) / 100;

  // No change at 0 amount
  if (amount === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];

    // Calculate luminance
    const lum = (r * 0.299 + g * 0.587 + b * 0.114) / 255;

    // Interpolate between black and white colors based on luminance
    const tintR = blackColor.r + (whiteColor.r - blackColor.r) * lum;
    const tintG = blackColor.g + (whiteColor.g - blackColor.g) * lum;
    const tintB = blackColor.b + (whiteColor.b - blackColor.b) * lum;

    // Blend with original based on amount
    data[i] = Math.round(r + (tintR - r) * amount);
    data[i + 1] = Math.round(g + (tintG - g) * amount);
    data[i + 2] = Math.round(b + (tintB - b) * amount);
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// CURVES
// ============================================================================

/**
 * Curve point structure for bezier curves
 */
interface CurvePoint {
  x: number;  // Input value 0-255
  y: number;  // Output value 0-255
}

/**
 * Evaluate a cubic bezier curve at parameter t
 */
function cubicBezier(p0: number, p1: number, p2: number, p3: number, t: number): number {
  const t2 = t * t;
  const t3 = t2 * t;
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;
  return mt3 * p0 + 3 * mt2 * t * p1 + 3 * mt * t2 * p2 + t3 * p3;
}

/**
 * Build a lookup table from curve points using cubic interpolation
 */
function buildCurveLUT(points: CurvePoint[]): Uint8Array {
  const lut = new Uint8Array(256);

  // If no points or only one point, return identity LUT
  if (!points || points.length === 0) {
    for (let i = 0; i < 256; i++) {
      lut[i] = i;
    }
    return lut;
  }

  if (points.length === 1) {
    for (let i = 0; i < 256; i++) {
      lut[i] = Math.max(0, Math.min(255, Math.round(points[0].y)));
    }
    return lut;
  }

  // Sort points by x value
  const sortedPoints = [...points].sort((a, b) => a.x - b.x);

  // Ensure we have points at 0 and 255
  if (sortedPoints[0].x > 0) {
    sortedPoints.unshift({ x: 0, y: sortedPoints[0].y });
  }
  if (sortedPoints[sortedPoints.length - 1].x < 255) {
    sortedPoints.push({ x: 255, y: sortedPoints[sortedPoints.length - 1].y });
  }

  // For each input value, find the output using cubic spline interpolation
  for (let i = 0; i < 256; i++) {
    // Find the segment this value falls into
    let segmentIndex = 0;
    for (let j = 0; j < sortedPoints.length - 1; j++) {
      if (i >= sortedPoints[j].x && i <= sortedPoints[j + 1].x) {
        segmentIndex = j;
        break;
      }
    }

    const p0 = sortedPoints[segmentIndex];
    const p1 = sortedPoints[segmentIndex + 1];

    // Linear interpolation parameter
    const t = (i - p0.x) / (p1.x - p0.x || 1);

    // Calculate control points for smooth curve
    // Use Catmull-Rom style tangents
    let tangent0 = 0;
    let tangent1 = 0;

    if (segmentIndex > 0) {
      const pPrev = sortedPoints[segmentIndex - 1];
      tangent0 = (p1.y - pPrev.y) / (p1.x - pPrev.x || 1) * (p1.x - p0.x);
    }

    if (segmentIndex < sortedPoints.length - 2) {
      const pNext = sortedPoints[segmentIndex + 2];
      tangent1 = (pNext.y - p0.y) / (pNext.x - p0.x || 1) * (p1.x - p0.x);
    }

    // Control points for cubic bezier
    const cp1y = p0.y + tangent0 / 3;
    const cp2y = p1.y - tangent1 / 3;

    // Evaluate cubic bezier
    const value = cubicBezier(p0.y, cp1y, cp2y, p1.y, t);

    lut[i] = Math.max(0, Math.min(255, Math.round(value)));
  }

  return lut;
}

/**
 * Curves effect renderer - Professional color grading curves
 *
 * Parameters:
 * - master_curve: Array of { x, y } points for RGB curve
 * - red_curve: Array of { x, y } points for red channel
 * - green_curve: Array of { x, y } points for green channel
 * - blue_curve: Array of { x, y } points for blue channel
 * - alpha_curve: Array of { x, y } points for alpha channel
 * - blend_with_original: 0-100 (default 100, full effect)
 *
 * Each curve is an array of control points where:
 * - x: input value (0-255)
 * - y: output value (0-255)
 *
 * Default curve is a straight line from (0,0) to (255,255) - identity
 */
export function curvesRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const masterCurve = params.master_curve as CurvePoint[] | undefined;
  const redCurve = params.red_curve as CurvePoint[] | undefined;
  const greenCurve = params.green_curve as CurvePoint[] | undefined;
  const blueCurve = params.blue_curve as CurvePoint[] | undefined;
  const alphaCurve = params.alpha_curve as CurvePoint[] | undefined;
  const blend = (params.blend_with_original ?? 100) / 100;

  // Check if any curves are defined
  const hasCurves = masterCurve || redCurve || greenCurve || blueCurve || alphaCurve;

  if (!hasCurves || blend === 0) {
    return input;
  }

  // Build lookup tables for each channel
  const masterLUT = buildCurveLUT(masterCurve ?? [{ x: 0, y: 0 }, { x: 255, y: 255 }]);
  const redLUT = buildCurveLUT(redCurve ?? [{ x: 0, y: 0 }, { x: 255, y: 255 }]);
  const greenLUT = buildCurveLUT(greenCurve ?? [{ x: 0, y: 0 }, { x: 255, y: 255 }]);
  const blueLUT = buildCurveLUT(blueCurve ?? [{ x: 0, y: 0 }, { x: 255, y: 255 }]);
  const alphaLUT = alphaCurve ? buildCurveLUT(alphaCurve) : null;

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    const origR = data[i];
    const origG = data[i + 1];
    const origB = data[i + 2];
    const origA = data[i + 3];

    // Apply master curve first (affects all RGB channels)
    let r = masterLUT[origR];
    let g = masterLUT[origG];
    let b = masterLUT[origB];

    // Then apply individual channel curves
    r = redLUT[r];
    g = greenLUT[g];
    b = blueLUT[b];

    // Apply alpha curve if defined
    const a = alphaLUT ? alphaLUT[origA] : origA;

    // Blend with original if needed
    if (blend < 1) {
      r = Math.round(origR + (r - origR) * blend);
      g = Math.round(origG + (g - origG) * blend);
      b = Math.round(origB + (b - origB) * blend);
    }

    data[i] = r;
    data[i + 1] = g;
    data[i + 2] = b;
    data[i + 3] = a;
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

/**
 * Convenience function to create a typical S-curve for contrast
 */
export function createSCurve(amount: number = 0.5): CurvePoint[] {
  const midPoint = 128;
  const adjustment = amount * 50;

  return [
    { x: 0, y: 0 },
    { x: 64, y: Math.max(0, 64 - adjustment) },
    { x: midPoint, y: midPoint },
    { x: 192, y: Math.min(255, 192 + adjustment) },
    { x: 255, y: 255 },
  ];
}

/**
 * Convenience function to create a highlight/shadow lift curve
 */
export function createLiftCurve(shadowLift: number = 0, highlightLift: number = 0): CurvePoint[] {
  return [
    { x: 0, y: Math.max(0, Math.min(128, shadowLift)) },
    { x: 128, y: 128 },
    { x: 255, y: Math.max(128, Math.min(255, 255 + highlightLift)) },
  ];
}

// ============================================================================
// GLOW
// ============================================================================

/**
 * Glow effect renderer - Creates a luminous bloom effect
 *
 * Parameters:
 * - glow_threshold: 0-255, pixels above this brightness glow (default 128)
 * - glow_radius: 0-200, blur radius for glow (default 20)
 * - glow_intensity: 0-400, intensity multiplier (default 100)
 * - glow_colors: 'original' | 'a_over_b' | 'custom' (default 'original')
 * - glow_color_a: color for glow (when using custom colors)
 * - glow_color_b: color for secondary glow
 * - glow_operation: 'add' | 'screen' | 'lighten' (default 'add')
 */
export function glowRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const threshold = params.glow_threshold ?? 128;
  const radius = params.glow_radius ?? 20;
  const intensity = (params.glow_intensity ?? 100) / 100;
  const operation = params.glow_operation ?? 'add';

  // No glow if intensity is 0 or radius is 0
  if (intensity === 0 || radius === 0) {
    return input;
  }

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  // Step 1: Extract bright areas above threshold
  const thresholdCanvas = document.createElement('canvas');
  thresholdCanvas.width = width;
  thresholdCanvas.height = height;
  const thresholdCtx = thresholdCanvas.getContext('2d')!;

  const inputData = input.ctx.getImageData(0, 0, width, height);
  const thresholdData = thresholdCtx.createImageData(width, height);

  for (let i = 0; i < inputData.data.length; i += 4) {
    const r = inputData.data[i];
    const g = inputData.data[i + 1];
    const b = inputData.data[i + 2];
    const a = inputData.data[i + 3];

    // Calculate luminance
    const lum = r * 0.299 + g * 0.587 + b * 0.114;

    if (lum > threshold) {
      // Keep pixels above threshold, scaled by intensity
      const scale = ((lum - threshold) / (255 - threshold)) * intensity;
      thresholdData.data[i] = Math.min(255, r * scale);
      thresholdData.data[i + 1] = Math.min(255, g * scale);
      thresholdData.data[i + 2] = Math.min(255, b * scale);
      thresholdData.data[i + 3] = a;
    } else {
      // Set to transparent
      thresholdData.data[i] = 0;
      thresholdData.data[i + 1] = 0;
      thresholdData.data[i + 2] = 0;
      thresholdData.data[i + 3] = 0;
    }
  }

  thresholdCtx.putImageData(thresholdData, 0, 0);

  // Step 2: Blur the threshold image
  const blurCanvas = document.createElement('canvas');
  blurCanvas.width = width;
  blurCanvas.height = height;
  const blurCtx = blurCanvas.getContext('2d')!;

  blurCtx.filter = `blur(${radius}px)`;
  blurCtx.drawImage(thresholdCanvas, 0, 0);

  // Step 3: Composite glow with original
  // First draw original
  output.ctx.drawImage(input.canvas, 0, 0);

  // Then add glow using selected blend mode
  switch (operation) {
    case 'screen':
      output.ctx.globalCompositeOperation = 'screen';
      break;
    case 'lighten':
      output.ctx.globalCompositeOperation = 'lighten';
      break;
    case 'add':
    default:
      output.ctx.globalCompositeOperation = 'lighter';
      break;
  }

  output.ctx.drawImage(blurCanvas, 0, 0);

  // Reset composite operation
  output.ctx.globalCompositeOperation = 'source-over';

  return output;
}

// ============================================================================
// DROP SHADOW (Stylize)
// ============================================================================

/**
 * Drop Shadow effect renderer
 *
 * Parameters:
 * - shadow_color: color { r, g, b, a } (default black with 0.5 alpha)
 * - opacity: 0-100 (default 50)
 * - direction: 0-360 degrees (default 135)
 * - distance: 0-1000 pixels (default 5)
 * - softness: 0-250 blur radius (default 5)
 * - shadow_only: boolean (only show shadow)
 */
export function dropShadowRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const shadowColor = params.shadow_color ?? { r: 0, g: 0, b: 0, a: 0.5 };
  const opacity = (params.opacity ?? 50) / 100;
  const direction = (params.direction ?? 135) * Math.PI / 180;
  const distance = params.distance ?? 5;
  const softness = params.softness ?? 5;
  const shadowOnly = params.shadow_only ?? false;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;

  // Calculate offset from direction and distance
  const offsetX = Math.cos(direction) * distance;
  const offsetY = Math.sin(direction) * distance;

  // Apply shadow using canvas shadow API
  output.ctx.shadowColor = `rgba(${shadowColor.r}, ${shadowColor.g}, ${shadowColor.b}, ${opacity})`;
  output.ctx.shadowBlur = softness;
  output.ctx.shadowOffsetX = offsetX;
  output.ctx.shadowOffsetY = offsetY;

  // Draw the image (shadow will be rendered automatically)
  output.ctx.drawImage(input.canvas, 0, 0);

  // Reset shadow for the second draw
  output.ctx.shadowColor = 'transparent';
  output.ctx.shadowBlur = 0;
  output.ctx.shadowOffsetX = 0;
  output.ctx.shadowOffsetY = 0;

  if (!shadowOnly) {
    // Draw original image on top
    output.ctx.drawImage(input.canvas, 0, 0);
  }

  return output;
}

// ============================================================================
// COLOR BALANCE
// ============================================================================

/**
 * Color Balance effect renderer - Adjust shadows, midtones, and highlights
 *
 * Parameters:
 * - shadow_red: -100 to 100 (cyan to red in shadows)
 * - shadow_green: -100 to 100 (magenta to green in shadows)
 * - shadow_blue: -100 to 100 (yellow to blue in shadows)
 * - midtone_red: -100 to 100 (cyan to red in midtones)
 * - midtone_green: -100 to 100 (magenta to green in midtones)
 * - midtone_blue: -100 to 100 (yellow to blue in midtones)
 * - highlight_red: -100 to 100 (cyan to red in highlights)
 * - highlight_green: -100 to 100 (magenta to green in highlights)
 * - highlight_blue: -100 to 100 (yellow to blue in highlights)
 * - preserve_luminosity: boolean (default true)
 */
export function colorBalanceRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const shadowR = (params.shadow_red ?? 0) / 100;
  const shadowG = (params.shadow_green ?? 0) / 100;
  const shadowB = (params.shadow_blue ?? 0) / 100;
  const midtoneR = (params.midtone_red ?? 0) / 100;
  const midtoneG = (params.midtone_green ?? 0) / 100;
  const midtoneB = (params.midtone_blue ?? 0) / 100;
  const highlightR = (params.highlight_red ?? 0) / 100;
  const highlightG = (params.highlight_green ?? 0) / 100;
  const highlightB = (params.highlight_blue ?? 0) / 100;
  const preserveLuminosity = params.preserve_luminosity ?? true;

  // No change if all values are 0
  if (shadowR === 0 && shadowG === 0 && shadowB === 0 &&
      midtoneR === 0 && midtoneG === 0 && midtoneB === 0 &&
      highlightR === 0 && highlightG === 0 && highlightB === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    let r = data[i];
    let g = data[i + 1];
    let b = data[i + 2];

    // Calculate luminance for tonal range detection
    const lum = (r * 0.299 + g * 0.587 + b * 0.114) / 255;

    // Calculate weights for shadows, midtones, highlights
    // Shadows: weight peaks at lum=0, falls off by lum=0.33
    const shadowWeight = Math.max(0, 1 - lum * 3);
    // Highlights: weight peaks at lum=1, falls off by lum=0.67
    const highlightWeight = Math.max(0, (lum - 0.67) * 3);
    // Midtones: weight peaks at lum=0.5
    const midtoneWeight = 1 - shadowWeight - highlightWeight;

    // Apply adjustments per tonal range
    const rAdjust = shadowR * shadowWeight + midtoneR * midtoneWeight + highlightR * highlightWeight;
    const gAdjust = shadowG * shadowWeight + midtoneG * midtoneWeight + highlightG * highlightWeight;
    const bAdjust = shadowB * shadowWeight + midtoneB * midtoneWeight + highlightB * highlightWeight;

    r = r + rAdjust * 255;
    g = g + gAdjust * 255;
    b = b + bAdjust * 255;

    // Preserve luminosity if enabled
    if (preserveLuminosity) {
      const newLum = (r * 0.299 + g * 0.587 + b * 0.114) / 255;
      if (newLum > 0.001) {
        const lumRatio = lum / newLum;
        r *= lumRatio;
        g *= lumRatio;
        b *= lumRatio;
      }
    }

    // Clamp values
    data[i] = Math.max(0, Math.min(255, Math.round(r)));
    data[i + 1] = Math.max(0, Math.min(255, Math.round(g)));
    data[i + 2] = Math.max(0, Math.min(255, Math.round(b)));
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// EXPOSURE
// ============================================================================

/**
 * Exposure effect renderer - Photographic exposure adjustment
 *
 * Parameters:
 * - exposure: -5 to 5 stops (default 0)
 * - offset: -1 to 1 (default 0) - adds to all values
 * - gamma: 0.1 to 10 (default 1) - gamma correction
 */
export function exposureRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const exposure = params.exposure ?? 0;
  const offset = params.offset ?? 0;
  const gamma = params.gamma ?? 1;

  // No change if all values are default
  if (exposure === 0 && offset === 0 && gamma === 1) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  // Build lookup table for performance
  const lut = new Uint8Array(256);
  const exposureMultiplier = Math.pow(2, exposure);
  const gammaInv = 1 / gamma;

  for (let i = 0; i < 256; i++) {
    let value = i / 255;

    // Apply exposure (multiply)
    value *= exposureMultiplier;

    // Apply offset (add)
    value += offset;

    // Clamp to 0-1 before gamma
    value = Math.max(0, Math.min(1, value));

    // Apply gamma
    value = Math.pow(value, gammaInv);

    lut[i] = Math.round(value * 255);
  }

  // Apply LUT to all pixels
  for (let i = 0; i < data.length; i += 4) {
    data[i] = lut[data[i]];
    data[i + 1] = lut[data[i + 1]];
    data[i + 2] = lut[data[i + 2]];
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// VIBRANCE
// ============================================================================

/**
 * Vibrance effect renderer - Smart saturation that protects skin tones
 *
 * Parameters:
 * - vibrance: -100 to 100 (default 0)
 * - saturation: -100 to 100 (default 0) - standard saturation boost
 */
export function vibranceRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const vibrance = (params.vibrance ?? 0) / 100;
  const saturation = (params.saturation ?? 0) / 100;

  // No change if all values are 0
  if (vibrance === 0 && saturation === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    let r = data[i] / 255;
    let g = data[i + 1] / 255;
    let b = data[i + 2] / 255;

    // Calculate current saturation
    const max = Math.max(r, g, b);
    const min = Math.min(r, g, b);
    const currentSat = max - min;

    // Calculate luminance
    const lum = r * 0.299 + g * 0.587 + b * 0.114;

    // Vibrance: boost less saturated colors more
    // Also protect skin tones (orange-ish colors)
    const skinProtection = 1 - Math.max(0, Math.min(1,
      Math.abs(r - 0.8) * 2 + Math.abs(g - 0.5) * 2 + Math.abs(b - 0.3) * 3
    ));

    // Vibrance amount inversely proportional to current saturation
    const vibranceAmount = vibrance * (1 - currentSat) * (1 - skinProtection * 0.5);

    // Combined saturation adjustment
    const satAdjust = 1 + saturation + vibranceAmount;

    // Apply saturation change
    r = lum + (r - lum) * satAdjust;
    g = lum + (g - lum) * satAdjust;
    b = lum + (b - lum) * satAdjust;

    // Clamp values
    data[i] = Math.max(0, Math.min(255, Math.round(r * 255)));
    data[i + 1] = Math.max(0, Math.min(255, Math.round(g * 255)));
    data[i + 2] = Math.max(0, Math.min(255, Math.round(b * 255)));
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// INVERT
// ============================================================================

/**
 * Invert effect renderer - Inverts colors or specific channels
 *
 * Parameters:
 * - blend: 0-100 (default 100) - blend with original
 * - channel: 'rgb' | 'red' | 'green' | 'blue' | 'hue' | 'saturation' | 'lightness'
 */
export function invertRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const blend = (params.blend ?? 100) / 100;
  const channel = params.channel ?? 'rgb';

  if (blend === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    const origR = data[i];
    const origG = data[i + 1];
    const origB = data[i + 2];

    let r = origR;
    let g = origG;
    let b = origB;

    switch (channel) {
      case 'rgb':
        r = 255 - r;
        g = 255 - g;
        b = 255 - b;
        break;
      case 'red':
        r = 255 - r;
        break;
      case 'green':
        g = 255 - g;
        break;
      case 'blue':
        b = 255 - b;
        break;
      case 'hue':
      case 'saturation':
      case 'lightness': {
        // Convert to HSL, invert component, convert back
        let [h, s, l] = rgbToHsl(r, g, b);
        if (channel === 'hue') h = (h + 0.5) % 1;
        else if (channel === 'saturation') s = 1 - s;
        else if (channel === 'lightness') l = 1 - l;
        [r, g, b] = hslToRgb(h, s, l);
        break;
      }
    }

    // Blend with original
    if (blend < 1) {
      r = Math.round(origR + (r - origR) * blend);
      g = Math.round(origG + (g - origG) * blend);
      b = Math.round(origB + (b - origB) * blend);
    }

    data[i] = r;
    data[i + 1] = g;
    data[i + 2] = b;
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// POSTERIZE
// ============================================================================

/**
 * Posterize effect renderer - Reduce color levels
 *
 * Parameters:
 * - levels: 2-256 (default 6) - number of levels per channel
 */
export function posterizeRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const levels = Math.max(2, Math.min(256, params.levels ?? 6));

  if (levels === 256) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  // Build lookup table
  const lut = new Uint8Array(256);
  const step = 255 / (levels - 1);

  for (let i = 0; i < 256; i++) {
    const level = Math.round(i / 255 * (levels - 1));
    lut[i] = Math.round(level * step);
  }

  // Apply LUT
  for (let i = 0; i < data.length; i += 4) {
    data[i] = lut[data[i]];
    data[i + 1] = lut[data[i + 1]];
    data[i + 2] = lut[data[i + 2]];
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// THRESHOLD
// ============================================================================

/**
 * Threshold effect renderer - Convert to black and white based on threshold
 *
 * Parameters:
 * - threshold: 0-255 (default 128)
 */
export function thresholdRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const threshold = params.threshold ?? 128;

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];

    // Calculate luminance
    const lum = r * 0.299 + g * 0.587 + b * 0.114;

    // Apply threshold
    const value = lum >= threshold ? 255 : 0;

    data[i] = value;
    data[i + 1] = value;
    data[i + 2] = value;
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// REGISTRATION
// ============================================================================

/**
 * Register all color correction effect renderers
 */
export function registerColorEffects(): void {
  registerEffectRenderer('brightness-contrast', brightnessContrastRenderer);
  registerEffectRenderer('hue-saturation', hueSaturationRenderer);
  registerEffectRenderer('levels', levelsRenderer);
  registerEffectRenderer('tint', tintRenderer);
  registerEffectRenderer('curves', curvesRenderer);
  registerEffectRenderer('glow', glowRenderer);
  registerEffectRenderer('drop-shadow', dropShadowRenderer);
  registerEffectRenderer('color-balance', colorBalanceRenderer);
  registerEffectRenderer('exposure', exposureRenderer);
  registerEffectRenderer('vibrance', vibranceRenderer);
  registerEffectRenderer('invert', invertRenderer);
  registerEffectRenderer('posterize', posterizeRenderer);
  registerEffectRenderer('threshold', thresholdRenderer);
}

export default {
  brightnessContrastRenderer,
  hueSaturationRenderer,
  levelsRenderer,
  tintRenderer,
  curvesRenderer,
  glowRenderer,
  dropShadowRenderer,
  colorBalanceRenderer,
  exposureRenderer,
  vibranceRenderer,
  invertRenderer,
  posterizeRenderer,
  thresholdRenderer,
  createSCurve,
  createLiftCurve,
  registerColorEffects
};
