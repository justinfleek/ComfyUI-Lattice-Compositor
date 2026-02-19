/**
 * Color Correction Effect Renderers
 *
 * Implements common color correction effects:
 * - Brightness & Contrast
 * - Hue/Saturation
 * - Levels
 * - Tint
 *
 * Advanced color grading effects are in colorGrading.ts:
 * - Lift/Gamma/Gain
 * - HSL Secondary
 * - Hue vs Curves
 * - Color Match
 */
import type { JSONValue } from "@/types/dataAsset";
import type { RuntimeValue } from "@/types/ses-ambient";
import {
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams,
  registerEffectRenderer,
} from "../effectProcessor";
import { isFiniteNumber, hasXY, isRGBAColor } from "@/utils/typeGuards";

// Import advanced color grading effects
import {
  colorMatchRenderer as _colorMatchRenderer,
  hslSecondaryRenderer as _hslSecondaryRenderer,
  hueVsCurvesRenderer as _hueVsCurvesRenderer,
  liftGammaGainRenderer as _liftGammaGainRenderer,
  registerColorGradingEffects,
} from "./colorGrading";

// Re-export for backwards compatibility
export {
  colorMatchRenderer,
  hslSecondaryRenderer,
  hueVsCurvesRenderer,
  liftGammaGainRenderer,
} from "./colorGrading";

// Local aliases for internal use
const liftGammaGainRenderer = _liftGammaGainRenderer;
const hslSecondaryRenderer = _hslSecondaryRenderer;
const hueVsCurvesRenderer = _hueVsCurvesRenderer;
const colorMatchRenderer = _colorMatchRenderer;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// BRIGHTNESS & CONTRAST
// ═══════════════════════════════════════════════════════════════════════════

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
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate numeric params (NaN causes black pixel corruption)
  // Type proof: brightness ∈ ℝ ∧ finite(brightness) → brightness ∈ [-150, 150]
  const brightnessValue = params.brightness;
  const brightness = isFiniteNumber(brightnessValue)
    ? Math.max(-150, Math.min(150, brightnessValue)) / 100
    : 0;
  // Type proof: contrast ∈ ℝ ∧ finite(contrast) → contrast ∈ [-100, 100]
  const contrastValue = params.contrast;
  const contrast = isFiniteNumber(contrastValue)
    ? Math.max(-100, Math.min(100, contrastValue)) / 100
    : 0;
  // Type proof: use_legacy ∈ {true, false}
  const useLegacy = typeof params.use_legacy === "boolean" ? params.use_legacy : false;

  // No change needed
  if (brightness === 0 && contrast === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
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

// ═══════════════════════════════════════════════════════════════════════════
// HUE/SATURATION
// ═══════════════════════════════════════════════════════════════════════════

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
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate numeric params (NaN causes black pixel corruption)
  // Type proof: master_hue ∈ ℝ ∧ finite(master_hue) → master_hue ∈ [-180, 180]
  const hueValue = params.master_hue;
  const hueShift = isFiniteNumber(hueValue)
    ? Math.max(-180, Math.min(180, hueValue)) / 360
    : 0;
  // Type proof: master_saturation ∈ ℝ ∧ finite(master_saturation) → master_saturation ∈ [-100, 100]
  const satValue = params.master_saturation;
  const saturationShift = isFiniteNumber(satValue)
    ? Math.max(-100, Math.min(100, satValue)) / 100
    : 0;
  // Type proof: master_lightness ∈ ℝ ∧ finite(master_lightness) → master_lightness ∈ [-100, 100]
  const lightValue = params.master_lightness;
  const lightnessShift = isFiniteNumber(lightValue)
    ? Math.max(-100, Math.min(100, lightValue)) / 100
    : 0;
  // Type proof: colorize ∈ {true, false}
  const colorize = typeof params.colorize === "boolean" ? params.colorize : false;

  // No change needed
  if (
    hueShift === 0 &&
    saturationShift === 0 &&
    lightnessShift === 0 &&
    !colorize
  ) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // levels
// ═══════════════════════════════════════════════════════════════════════════

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
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate numeric params (NaN causes black pixel corruption)
  // Type proof: input_black ∈ ℝ ∧ finite(input_black) → input_black ∈ [0, 255]
  const inputBlackValue = params.input_black;
  const inputBlack = isFiniteNumber(inputBlackValue)
    ? Math.max(0, Math.min(255, inputBlackValue))
    : 0;
  // Type proof: input_white ∈ ℝ ∧ finite(input_white) → input_white ∈ [0, 255]
  const inputWhiteValue = params.input_white;
  const inputWhite = isFiniteNumber(inputWhiteValue)
    ? Math.max(0, Math.min(255, inputWhiteValue))
    : 255;
  // Type proof: gamma ∈ ℝ ∧ finite(gamma) ∧ gamma > 0 → gamma ∈ [0.01, 10]
  const gammaValue = params.gamma;
  const gamma = isFiniteNumber(gammaValue) && gammaValue > 0
    ? Math.max(0.01, Math.min(10, gammaValue))
    : 1;
  // Type proof: output_black ∈ ℝ ∧ finite(output_black) → output_black ∈ [0, 255]
  const outputBlackValue = params.output_black;
  const outputBlack = isFiniteNumber(outputBlackValue)
    ? Math.max(0, Math.min(255, outputBlackValue))
    : 0;
  // Type proof: output_white ∈ ℝ ∧ finite(output_white) → output_white ∈ [0, 255]
  const outputWhiteValue = params.output_white;
  const outputWhite = isFiniteNumber(outputWhiteValue)
    ? Math.max(0, Math.min(255, outputWhiteValue))
    : 255;

  // No change needed
  if (
    inputBlack === 0 &&
    inputWhite === 255 &&
    gamma === 1 &&
    outputBlack === 0 &&
    outputWhite === 255
  ) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
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
    value = value ** (1 / gamma);

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                     // tint
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Tint effect renderer - maps black to one color and white to another
 *
 * Parameters:
 * - map_black_to: color { r, g, b, a } (default black)
 * - map_white_to: color { r, g, b, a } (default white)
 * - amount_to_tint: 0-100 (default 100)
 */
// Type guard for color objects
function isColorObject(value: RuntimeValue): value is { r: number; g: number; b: number; a?: number } {
  return (
    typeof value === "object" &&
    value !== null &&
    "r" in value &&
    "g" in value &&
    "b" in value &&
    typeof (value as { r: JSONValue }).r === "number" &&
    typeof (value as { g: JSONValue }).g === "number" &&
    typeof (value as { b: JSONValue }).b === "number"
  );
}

export function tintRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const rawBlackColor = params.map_black_to;
  const rawWhiteColor = params.map_white_to;
  const blackColor = isColorObject(rawBlackColor) ? rawBlackColor : { r: 0, g: 0, b: 0 };
  const whiteColor = isColorObject(rawWhiteColor) ? rawWhiteColor : { r: 255, g: 255, b: 255 };
  // Validate amount (NaN causes black pixel corruption)
  // Type proof: amount_to_tint ∈ ℝ ∧ finite(amount_to_tint) → amount_to_tint ∈ [0, 100]
  const amountValue = params.amount_to_tint;
  const amount = isFiniteNumber(amountValue)
    ? Math.max(0, Math.min(100, amountValue)) / 100
    : 1;

  // No change at 0 amount
  if (amount === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // curves
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Curve point structure for bezier curves
 */
interface CurvePoint {
  x: number; // Input value 0-255
  y: number; // Output value 0-255
}

/**
 * Evaluate a cubic bezier curve at parameter t
 */
function cubicBezier(
  p0: number,
  p1: number,
  p2: number,
  p3: number,
  t: number,
): number {
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
      tangent0 = ((p1.y - pPrev.y) / (p1.x - pPrev.x || 1)) * (p1.x - p0.x);
    }

    if (segmentIndex < sortedPoints.length - 2) {
      const pNext = sortedPoints[segmentIndex + 2];
      tangent1 = ((pNext.y - p0.y) / (pNext.x - p0.x || 1)) * (p1.x - p0.x);
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
  params: EvaluatedEffectParams,
): EffectStackResult {
  const masterCurve = params.master_curve as CurvePoint[] | undefined;
  const redCurve = params.red_curve as CurvePoint[] | undefined;
  const greenCurve = params.green_curve as CurvePoint[] | undefined;
  const blueCurve = params.blue_curve as CurvePoint[] | undefined;
  const alphaCurve = params.alpha_curve as CurvePoint[] | undefined;
  // Validate blend param (NaN causes black pixel corruption)
  // Type proof: blend_with_original ∈ ℝ ∧ finite(blend_with_original) → blend_with_original ∈ [0, 100]
  const blendValue = params.blend_with_original;
  const blend = isFiniteNumber(blendValue)
    ? Math.max(0, Math.min(100, blendValue)) / 100
    : 1;

  // Check if any curves are defined
  const hasCurves =
    masterCurve || redCurve || greenCurve || blueCurve || alphaCurve;

  if (!hasCurves || blend === 0) {
    return input;
  }

  // Build lookup tables for each channel
  // Type proof: masterCurve ∈ CurvePoint[] ∪ {undefined} → CurvePoint[]
  const masterLUT = buildCurveLUT(
    masterCurve !== undefined ? masterCurve : [
      { x: 0, y: 0 },
      { x: 255, y: 255 },
    ],
  );
  // Type proof: redCurve ∈ CurvePoint[] ∪ {undefined} → CurvePoint[]
  const redLUT = buildCurveLUT(
    redCurve !== undefined ? redCurve : [
      { x: 0, y: 0 },
      { x: 255, y: 255 },
    ],
  );
  // Type proof: greenCurve ∈ CurvePoint[] ∪ {undefined} → CurvePoint[]
  const greenLUT = buildCurveLUT(
    greenCurve !== undefined ? greenCurve : [
      { x: 0, y: 0 },
      { x: 255, y: 255 },
    ],
  );
  // Type proof: blueCurve ∈ CurvePoint[] ∪ {undefined} → CurvePoint[]
  const blueLUT = buildCurveLUT(
    blueCurve !== undefined ? blueCurve : [
      { x: 0, y: 0 },
      { x: 255, y: 255 },
    ],
  );
  const alphaLUT = alphaCurve ? buildCurveLUT(alphaCurve) : null;

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
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
export function createLiftCurve(
  shadowLift: number = 0,
  highlightLift: number = 0,
): CurvePoint[] {
  return [
    { x: 0, y: Math.max(0, Math.min(128, shadowLift)) },
    { x: 128, y: 128 },
    { x: 255, y: Math.max(128, Math.min(255, 255 + highlightLift)) },
  ];
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                                     // glow
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Glow effect renderer - Creates a luminous bloom effect
 *
 * Parameters:
 * - glow_threshold: 0-255, pixels above this brightness glow (default 128)
 * - glow_radius: 0-200, blur radius for glow (default 20)
 * - glow_intensity: 0-400, intensity multiplier (default 100)
 * - glow_colors: 'original' | 'ab' (default 'original')
 * - color_a: color for glow (when using 'ab' mode)
 * - color_b: color for secondary glow
 * - color_looping: 'none' | 'sawtooth_ab' | 'sawtooth_ba' | 'triangle'
 * - color_looping_speed: cycles per second (default 1)
 * - glow_dimensions: 'both' | 'horizontal' | 'vertical'
 * - glow_operation: 'add' | 'screen' | 'lighten' (default 'add')
 */
export function glowRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
  frame?: number,
): EffectStackResult {
  // Validate numeric params (NaN causes black pixel corruption)
  // Type proof: glow_threshold ∈ ℝ ∧ finite(glow_threshold) → glow_threshold ∈ ℝ
  const thresholdValue = params.glow_threshold;
  const threshold = isFiniteNumber(thresholdValue) ? thresholdValue : 128;
  // Type proof: glow_radius ∈ ℝ ∧ finite(glow_radius) ∧ glow_radius ≥ 0 → glow_radius ∈ ℝ₊
  const radiusValue = params.glow_radius;
  const radius = isFiniteNumber(radiusValue) ? Math.max(0, radiusValue) : 20;
  // Support both new 'glow_intensity' (0-10 range) and legacy (0-400 percentage)
  // Type proof: glow_intensity ∈ ℝ ∧ finite(glow_intensity) → glow_intensity ∈ [0, 500]
  const intensityValue = params.glow_intensity;
  const validIntensity = isFiniteNumber(intensityValue)
    ? Math.max(0, Math.min(500, intensityValue))
    : 100;
  const intensity =
    validIntensity <= 10 ? validIntensity : validIntensity / 100;

  // Support both 'composite_original' (from definition) and legacy 'glow_operation'
  // composite_original: 'on-top' | 'behind' | 'none'
  // glow_operation: 'add' | 'screen' | 'lighten'
  // Type proof: composite_original ∈ {"on-top", "behind", "none"} ∪ {undefined}
  const compositeValue = params.composite_original;
  const composite = typeof compositeValue === "string" ? compositeValue : "on-top";
  // Type proof: glow_operation ∈ {"add", "screen", "lighten"} ∪ {undefined}
  const operationValue = params.glow_operation;
  const operation = typeof operationValue === "string"
    ? operationValue
    : (composite === "on-top" ? "add" : "lighten");

  // Glow Colors (original or custom A/B colors)
  // Type proof: glow_colors ∈ {"original", "ab"} ∪ {undefined}
  const glowColorsValue = params.glow_colors;
  const glowColors = typeof glowColorsValue === "string" ? glowColorsValue : "original";
  const rawColorA = params.color_a;
  const rawColorB = params.color_b;
  const colorA = isColorObject(rawColorA) ? rawColorA : { r: 255, g: 255, b: 255, a: 1 };
  const colorB = isColorObject(rawColorB) ? rawColorB : { r: 255, g: 128, b: 0, a: 1 };

  // Color Looping (animated color cycling)
  // Type proof: color_looping ∈ {"none", "sawtooth_ab", "sawtooth_ba", "triangle"} ∪ {undefined}
  const colorLoopingValue = params.color_looping;
  const colorLooping = typeof colorLoopingValue === "string" ? colorLoopingValue : "none";
  // Type proof: color_looping_speed ∈ ℝ ∧ finite(color_looping_speed) → color_looping_speed ∈ ℝ₊
  const rawLoopSpeed = params.color_looping_speed;
  const colorLoopingSpeed = isFiniteNumber(rawLoopSpeed) && rawLoopSpeed > 0 ? rawLoopSpeed : 1;

  // Glow Dimensions (horizontal, vertical, or both)
  // Type proof: glow_dimensions ∈ {"both", "horizontal", "vertical"} ∪ {undefined}
  const glowDimensionsValue = params.glow_dimensions;
  const glowDimensions = typeof glowDimensionsValue === "string" ? glowDimensionsValue : "both";

  // No glow if intensity is 0 or radius is 0
  if (intensity === 0 || radius === 0) {
    return input;
  }

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  // Calculate color looping blend factor
  let colorBlend = 0; // 0 = Color A, 1 = Color B
  if (colorLooping !== "none" && frame !== undefined) {
    // Use injected FPS from context, fallback to 16 (WAN standard)
    // Deterministic: Explicit null check for _fps before using
    const fpsRaw = params._fps;
    const fps = (fpsRaw !== undefined && fpsRaw !== null && typeof fpsRaw === "number" && Number.isFinite(fpsRaw) && fpsRaw > 0) ? fpsRaw : 16;
    const time = frame / fps;
    const cycle = (time * colorLoopingSpeed) % 1;

    switch (colorLooping) {
      case "sawtooth_ab":
        // A → B → A → B (smooth ramp from A to B, then snap back)
        colorBlend = cycle;
        break;
      case "sawtooth_ba":
        // B → A → B → A (smooth ramp from B to A, then snap back)
        colorBlend = 1 - cycle;
        break;
      case "triangle":
        // A → B → A (ping-pong)
        colorBlend = cycle < 0.5 ? cycle * 2 : 2 - cycle * 2;
        break;
      default:
        colorBlend = 0;
    }
  }

  // Calculate the effective glow color (lerp between A and B)
  // Type guard ensures colorA and colorB are color objects
  const effectiveColor =
    glowColors === "ab" && isColorObject(colorA) && isColorObject(colorB)
      ? {
          r: colorA.r + (colorB.r - colorA.r) * colorBlend,
          g: colorA.g + (colorB.g - colorA.g) * colorBlend,
          b: colorA.b + (colorB.b - colorA.b) * colorBlend,
          a: (typeof colorA.a === "number" ? colorA.a : 1) + ((typeof colorB.a === "number" ? colorB.a : 1) - (typeof colorA.a === "number" ? colorA.a : 1)) * colorBlend,
        }
      : null;

  // Step 1: Extract bright areas above threshold
  // Use _sourceCanvas if provided (for additive stacking), otherwise use input
  // This ensures stacked glows extract from original layer, not from previous glow output
  const sourceCanvas = params._sourceCanvas as HTMLCanvasElement | undefined;
  const thresholdCanvas = document.createElement("canvas");
  thresholdCanvas.width = width;
  thresholdCanvas.height = height;
  const thresholdCtx = thresholdCanvas.getContext("2d")!;

  // Get image data from source canvas (original) or input canvas (chain)
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const sourceCtx = (sourceCanvas != null && typeof sourceCanvas === "object" && typeof sourceCanvas.getContext === "function") ? sourceCanvas.getContext("2d") : undefined;
  const inputData = sourceCtx
    ? sourceCtx.getImageData(0, 0, width, height)
    : input.ctx.getImageData(0, 0, width, height);
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

      if (effectiveColor) {
        // Apply custom glow color, using luminance as intensity
        thresholdData.data[i] = Math.min(255, effectiveColor.r * scale);
        thresholdData.data[i + 1] = Math.min(255, effectiveColor.g * scale);
        thresholdData.data[i + 2] = Math.min(255, effectiveColor.b * scale);
      } else {
        // Original colors
        thresholdData.data[i] = Math.min(255, r * scale);
        thresholdData.data[i + 1] = Math.min(255, g * scale);
        thresholdData.data[i + 2] = Math.min(255, b * scale);
      }
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

  // Step 2: Blur the threshold image (with dimension control)
  const blurCanvas = document.createElement("canvas");
  blurCanvas.width = width;
  blurCanvas.height = height;
  const blurCtx = blurCanvas.getContext("2d")!;

  // Apply directional or full blur based on glow dimensions
  if (glowDimensions === "horizontal") {
    // Horizontal-only blur: apply blur, then scale vertically to 1px and stretch back
    // This is a CSS filter approximation - true directional blur would need pixel manipulation
    const tempCanvas = document.createElement("canvas");
    tempCanvas.width = width;
    tempCanvas.height = 1;
    const tempCtx = tempCanvas.getContext("2d")!;

    // Draw threshold to 1-pixel height (average vertically)
    tempCtx.drawImage(thresholdCanvas, 0, 0, width, 1);

    // Apply horizontal blur
    const blurTemp = document.createElement("canvas");
    blurTemp.width = width;
    blurTemp.height = 1;
    const blurTempCtx = blurTemp.getContext("2d")!;
    blurTempCtx.filter = `blur(${radius}px)`;
    blurTempCtx.drawImage(tempCanvas, 0, 0);

    // Stretch back to full height
    blurCtx.drawImage(blurTemp, 0, 0, width, height);

    // Multiply with original threshold to restore vertical detail
    blurCtx.globalCompositeOperation = "multiply";
    blurCtx.filter = `blur(${radius}px)`;
    blurCtx.drawImage(thresholdCanvas, 0, 0);
    blurCtx.globalCompositeOperation = "source-over";
  } else if (glowDimensions === "vertical") {
    // Vertical-only blur: similar approach but rotated
    const tempCanvas = document.createElement("canvas");
    tempCanvas.width = 1;
    tempCanvas.height = height;
    const tempCtx = tempCanvas.getContext("2d")!;

    // Draw threshold to 1-pixel width (average horizontally)
    tempCtx.drawImage(thresholdCanvas, 0, 0, 1, height);

    // Apply vertical blur
    const blurTemp = document.createElement("canvas");
    blurTemp.width = 1;
    blurTemp.height = height;
    const blurTempCtx = blurTemp.getContext("2d")!;
    blurTempCtx.filter = `blur(${radius}px)`;
    blurTempCtx.drawImage(tempCanvas, 0, 0);

    // Stretch back to full width
    blurCtx.drawImage(blurTemp, 0, 0, width, height);

    // Multiply with original threshold to restore horizontal detail
    blurCtx.globalCompositeOperation = "multiply";
    blurCtx.filter = `blur(${radius}px)`;
    blurCtx.drawImage(thresholdCanvas, 0, 0);
    blurCtx.globalCompositeOperation = "source-over";
  } else {
    // Both dimensions - standard blur
    blurCtx.filter = `blur(${radius}px)`;
    blurCtx.drawImage(thresholdCanvas, 0, 0);
  }

  // Step 3: Composite glow with original based on composite mode
  if (composite === "none") {
    // Show glow only, no original
    output.ctx.drawImage(blurCanvas, 0, 0);
  } else if (composite === "behind") {
    // Draw glow first, then original on top
    output.ctx.drawImage(blurCanvas, 0, 0);
    output.ctx.globalCompositeOperation = "source-over";
    output.ctx.drawImage(input.canvas, 0, 0);
  } else {
    // 'on-top' mode (default): Draw original, then glow on top with blend mode
    output.ctx.drawImage(input.canvas, 0, 0);

    // Add glow using selected blend mode
    switch (operation) {
      case "screen":
        output.ctx.globalCompositeOperation = "screen";
        break;
      case "lighten":
        output.ctx.globalCompositeOperation = "lighten";
        break;
      default:
        output.ctx.globalCompositeOperation = "lighter";
        break;
    }

    output.ctx.drawImage(blurCanvas, 0, 0);
  }

  // Reset composite operation
  output.ctx.globalCompositeOperation = "source-over";

  return output;
}

// ═══════════════════════════════════════════════════════════════════════════
// DROP SHADOW (Stylize)
// ═══════════════════════════════════════════════════════════════════════════

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
  params: EvaluatedEffectParams,
): EffectStackResult {
  const rawShadowColor = params.shadow_color;
  const shadowColor = isColorObject(rawShadowColor) 
    ? rawShadowColor 
    : { r: 0, g: 0, b: 0, a: 0.5 };
  // Validate numeric params (NaN causes visual corruption)
  // Type proof: opacity ∈ ℝ ∧ finite(opacity) → opacity ∈ [0, 100]
  const opacityValue = params.opacity;
  const opacity = isFiniteNumber(opacityValue)
    ? Math.max(0, Math.min(100, opacityValue)) / 100
    : 0.5;
  // Type proof: direction ∈ ℝ ∧ finite(direction) → direction ∈ [0, 360]
  const directionValue = params.direction;
  const directionDeg = isFiniteNumber(directionValue)
    ? Math.max(0, Math.min(360, directionValue))
    : 135;
  const direction = (directionDeg * Math.PI) / 180;
  // Type proof: distance ∈ ℝ ∧ finite(distance) → distance ∈ ℝ₊
  const rawDistance = params.distance;
  const distance = isFiniteNumber(rawDistance) && rawDistance >= 0 ? rawDistance : 5;
  // Type proof: softness ∈ ℝ ∧ finite(softness) → softness ∈ ℝ₊
  const rawSoftness = params.softness;
  const softness = isFiniteNumber(rawSoftness) && rawSoftness >= 0 ? rawSoftness : 5;
  // Type proof: shadow_only ∈ {true, false}
  const shadowOnly = typeof params.shadow_only === "boolean" ? params.shadow_only : false;

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
  output.ctx.shadowColor = "transparent";
  output.ctx.shadowBlur = 0;
  output.ctx.shadowOffsetX = 0;
  output.ctx.shadowOffsetY = 0;

  if (!shadowOnly) {
    // Draw original image on top
    output.ctx.drawImage(input.canvas, 0, 0);
  }

  return output;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                         // color // balance
// ═══════════════════════════════════════════════════════════════════════════

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
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate numeric params (NaN causes black pixel corruption)
  const safeDiv100 = (val: RuntimeValue, def: number) => {
    // Type proof: val ∈ ℝ ∧ finite(val) → val ∈ ℝ
    const raw = isFiniteNumber(val) ? val : def;
    return raw / 100;
  };
  const shadowR = safeDiv100(params.shadow_red, 0);
  const shadowG = safeDiv100(params.shadow_green, 0);
  const shadowB = safeDiv100(params.shadow_blue, 0);
  const midtoneR = safeDiv100(params.midtone_red, 0);
  const midtoneG = safeDiv100(params.midtone_green, 0);
  const midtoneB = safeDiv100(params.midtone_blue, 0);
  const highlightR = safeDiv100(params.highlight_red, 0);
  const highlightG = safeDiv100(params.highlight_green, 0);
  const highlightB = safeDiv100(params.highlight_blue, 0);
  // Type proof: preserve_luminosity ∈ {true, false}
  const preserveLuminosity = typeof params.preserve_luminosity === "boolean" ? params.preserve_luminosity : true;

  // No change if all values are 0
  if (
    shadowR === 0 &&
    shadowG === 0 &&
    shadowB === 0 &&
    midtoneR === 0 &&
    midtoneG === 0 &&
    midtoneB === 0 &&
    highlightR === 0 &&
    highlightG === 0 &&
    highlightB === 0
  ) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
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
    const rAdjust =
      shadowR * shadowWeight +
      midtoneR * midtoneWeight +
      highlightR * highlightWeight;
    const gAdjust =
      shadowG * shadowWeight +
      midtoneG * midtoneWeight +
      highlightG * highlightWeight;
    const bAdjust =
      shadowB * shadowWeight +
      midtoneB * midtoneWeight +
      highlightB * highlightWeight;

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                 // exposure
// ═══════════════════════════════════════════════════════════════════════════

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
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate numeric params (NaN causes black pixel corruption)
  // Type proof: exposure ∈ ℝ ∧ finite(exposure) → exposure ∈ ℝ
  const rawExposure = params.exposure;
  const exposure = isFiniteNumber(rawExposure) ? rawExposure : 0;
  // Type proof: offset ∈ ℝ ∧ finite(offset) → offset ∈ ℝ
  const rawOffset = params.offset;
  const offset = isFiniteNumber(rawOffset) ? rawOffset : 0;
  // Type proof: gamma ∈ ℝ ∧ finite(gamma) ∧ gamma > 0 → gamma ∈ ℝ₊
  const rawGamma = params.gamma;
  const gamma = isFiniteNumber(rawGamma) && rawGamma > 0 ? rawGamma : 1;

  // No change if all values are default
  if (exposure === 0 && offset === 0 && gamma === 1) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
  const data = imageData.data;

  // Build lookup table for performance
  const lut = new Uint8Array(256);
  const exposureMultiplier = 2 ** exposure;
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
    value = value ** gammaInv;

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                 // vibrance
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Vibrance effect renderer - Smart saturation that protects skin tones
 *
 * Parameters:
 * - vibrance: -100 to 100 (default 0)
 * - saturation: -100 to 100 (default 0) - standard saturation boost
 */
export function vibranceRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate numeric params (NaN causes black pixel corruption)
  // System F/Omega: Use safeCoordinateDefault for bounded values
  const vibranceValue = typeof params.vibrance === "number" ? params.vibrance : 0;
  const vibrance = Math.max(-100, Math.min(100, isFiniteNumber(vibranceValue) ? vibranceValue : 0)) / 100;
  const saturationValue = typeof params.saturation === "number" ? params.saturation : 0;
  const saturation = Math.max(-100, Math.min(100, isFiniteNumber(saturationValue) ? saturationValue : 0)) / 100;

  // No change if all values are 0
  if (vibrance === 0 && saturation === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
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
    const skinProtection =
      1 -
      Math.max(
        0,
        Math.min(
          1,
          Math.abs(r - 0.8) * 2 + Math.abs(g - 0.5) * 2 + Math.abs(b - 0.3) * 3,
        ),
      );

    // Vibrance amount inversely proportional to current saturation
    const vibranceAmount =
      vibrance * (1 - currentSat) * (1 - skinProtection * 0.5);

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // invert
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Invert effect renderer - Inverts colors or specific channels
 *
 * Parameters:
 * - blend: 0-100 (default 100) - blend with original
 * - channel: 'rgb' | 'red' | 'green' | 'blue' | 'hue' | 'saturation' | 'lightness'
 */
export function invertRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate blend param (NaN causes black pixel corruption)
  // Type proof: blend ∈ ℝ ∧ finite(blend) → blend ∈ [0, 100]
  const rawBlend = params.blend;
  const blend = isFiniteNumber(rawBlend)
    ? Math.max(0, Math.min(100, rawBlend)) / 100
    : 1;
  // Type proof: channel ∈ {"rgb", "red", "green", "blue", "alpha"} ∪ {undefined}
  const channelValue = params.channel;
  const channel = typeof channelValue === "string" ? channelValue : "rgb";

  if (blend === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    const origR = data[i];
    const origG = data[i + 1];
    const origB = data[i + 2];

    let r = origR;
    let g = origG;
    let b = origB;

    switch (channel) {
      case "rgb":
        r = 255 - r;
        g = 255 - g;
        b = 255 - b;
        break;
      case "red":
        r = 255 - r;
        break;
      case "green":
        g = 255 - g;
        break;
      case "blue":
        b = 255 - b;
        break;
      case "hue":
      case "saturation":
      case "lightness": {
        // Convert to HSL, invert component, convert back
        let [h, s, l] = rgbToHsl(r, g, b);
        if (channel === "hue") h = (h + 0.5) % 1;
        else if (channel === "saturation") s = 1 - s;
        else if (channel === "lightness") l = 1 - l;
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                // posterize
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Posterize effect renderer - Reduce color levels
 *
 * Parameters:
 * - levels: 2-256 (default 6) - number of levels per channel
 */
export function posterizeRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate levels (NaN bypasses Math.max/min clamps, corrupting LUT)
  // Type proof: levels ∈ ℕ ∧ finite(levels) → levels ∈ [2, 256]
  const rawLevels = params.levels;
  const levels = isFiniteNumber(rawLevels) && Number.isInteger(rawLevels)
    ? Math.max(2, Math.min(256, rawLevels))
    : 6;

  if (levels === 256) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
  const data = imageData.data;

  // Build lookup table
  const lut = new Uint8Array(256);
  const step = 255 / (levels - 1);

  for (let i = 0; i < 256; i++) {
    const level = Math.round((i / 255) * (levels - 1));
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                // threshold
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Threshold effect renderer - Convert to black and white based on threshold
 *
 * Parameters:
 * - threshold: 0-255 (default 128)
 */
export function thresholdRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate threshold param (NaN causes incorrect threshold comparison)
  // Type proof: threshold ∈ ℝ ∧ finite(threshold) → threshold ∈ ℝ
  const thresholdValue = params.threshold;
  const threshold = isFiniteNumber(thresholdValue) ? thresholdValue : 128;

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                 // vignette
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Vignette effect renderer
 *
 * Creates a darkening around the edges of the image, commonly used
 * to focus attention on the center.
 *
 * Parameters:
 * - amount: -100 to 100 (negative = lighten edges, positive = darken)
 * - midpoint: 0 to 100 (where falloff starts from center)
 * - roundness: -100 to 100 (negative = horizontal, positive = vertical, 0 = circular)
 * - feather: 0 to 100 (edge softness)
 */
export function vignetteRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  // Validate numeric params (NaN causes black pixel corruption)
  // Type proof: amount ∈ ℝ ∧ finite(amount) → amount ∈ [-100, 100]
  const rawAmount = params.amount;
  const amount = isFiniteNumber(rawAmount)
    ? Math.max(-100, Math.min(100, rawAmount)) / 100
    : 0;
  // Type proof: midpoint ∈ ℝ ∧ finite(midpoint) → midpoint ∈ [0, 100]
  const rawMidpoint = params.midpoint;
  const midpoint = isFiniteNumber(rawMidpoint)
    ? Math.max(0, Math.min(100, rawMidpoint)) / 100
    : 0.5;
  // Type proof: roundness ∈ ℝ ∧ finite(roundness) → roundness ∈ [-100, 100]
  const rawRoundness = params.roundness;
  const roundness = isFiniteNumber(rawRoundness)
    ? Math.max(-100, Math.min(100, rawRoundness)) / 100
    : 0;
  // Type proof: feather ∈ ℝ ∧ finite(feather) → feather ∈ [0, 100]
  const rawFeather = params.feather;
  const feather = isFiniteNumber(rawFeather)
    ? Math.max(0, Math.min(100, rawFeather)) / 100
    : 0.5;

  // No change needed
  if (amount === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
  const data = imageData.data;
  const width = input.canvas.width;
  const height = input.canvas.height;

  const centerX = width / 2;
  const centerY = height / 2;

  // Calculate aspect ratio adjustments based on roundness
  const aspectX = 1 + (roundness > 0 ? roundness * 0.5 : 0);
  const aspectY = 1 + (roundness < 0 ? -roundness * 0.5 : 0);

  // Max distance from center (normalized)
  const maxDist = Math.sqrt(centerX * centerX + centerY * centerY);

  // Feather affects the falloff curve
  const featherMult = Math.max(0.01, feather);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = (y * width + x) * 4;

      // Calculate distance from center with aspect ratio
      const dx = (x - centerX) * aspectX;
      const dy = (y - centerY) * aspectY;
      const dist = Math.sqrt(dx * dx + dy * dy) / maxDist;

      // Calculate vignette factor based on distance and midpoint
      let factor = 0;
      if (dist > midpoint) {
        // Smooth falloff using smoothstep
        const t = (dist - midpoint) / (1 - midpoint + 0.001);
        const smoothT = t * t * (3 - 2 * t); // Smoothstep
        factor = smoothT ** (1 / featherMult);
      }

      // Apply vignette (darken or lighten based on amount sign)
      const multiplier = 1 - factor * amount;

      data[idx] = Math.max(0, Math.min(255, data[idx] * multiplier));
      data[idx + 1] = Math.max(0, Math.min(255, data[idx + 1] * multiplier));
      data[idx + 2] = Math.max(0, Math.min(255, data[idx + 2] * multiplier));
    }
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ═══════════════════════════════════════════════════════════════════════════
// LUT (Look-Up Table)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * LUT storage for parsed .cube files
 */
interface LUT3D {
  title: string;
  size: number;
  domainMin: [number, number, number];
  domainMax: [number, number, number];
  data: Float32Array; // RGB values in row-major order
}

// Global LUT cache
const lutCache = new Map<string, LUT3D>();

/**
 * Parse a .cube LUT file
 */
export function parseCubeLUT(content: string): LUT3D {
  const lines = content.split("\n");
  let title = "Untitled";
  let size = 0;
  let domainMin: [number, number, number] = [0, 0, 0];
  let domainMax: [number, number, number] = [1, 1, 1];
  const dataLines: string[] = [];

  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith("#")) continue;

    if (trimmed.startsWith("TITLE")) {
      title = trimmed.replace(/^TITLE\s*"?|"?\s*$/g, "");
    } else if (trimmed.startsWith("LUT_3D_SIZE")) {
      size = parseInt(trimmed.split(/\s+/)[1], 10);
    } else if (trimmed.startsWith("DOMAIN_MIN")) {
      const parts = trimmed.split(/\s+/).slice(1).map(Number);
      // Type proof: parts[i] ∈ ℝ ∪ {undefined} → parts[i] ∈ ℝ
      domainMin = [
        isFiniteNumber(parts[0]) ? parts[0] : 0,
        isFiniteNumber(parts[1]) ? parts[1] : 0,
        isFiniteNumber(parts[2]) ? parts[2] : 0,
      ];
    } else if (trimmed.startsWith("DOMAIN_MAX")) {
      const parts = trimmed.split(/\s+/).slice(1).map(Number);
      // Type proof: parts[i] ∈ ℝ ∪ {undefined} → parts[i] ∈ ℝ
      domainMax = [
        isFiniteNumber(parts[0]) ? parts[0] : 1,
        isFiniteNumber(parts[1]) ? parts[1] : 1,
        isFiniteNumber(parts[2]) ? parts[2] : 1,
      ];
    } else if (/^[\d.\-e]+\s+[\d.\-e]+\s+[\d.\-e]+/.test(trimmed)) {
      dataLines.push(trimmed);
    }
  }

  if (size === 0) {
    throw new Error("Invalid .cube file: missing LUT_3D_SIZE");
  }

  const data = new Float32Array(size * size * size * 3);
  for (let i = 0; i < dataLines.length && i < size * size * size; i++) {
    const parts = dataLines[i].split(/\s+/).map(Number);
    // Type proof: parts[i] ∈ ℝ ∪ {undefined} → parts[i] ∈ ℝ
    data[i * 3] = isFiniteNumber(parts[0]) ? parts[0] : 0;
    data[i * 3 + 1] = isFiniteNumber(parts[1]) ? parts[1] : 0;
    data[i * 3 + 2] = isFiniteNumber(parts[2]) ? parts[2] : 0;
  }

  return { title, size, domainMin, domainMax, data };
}

/**
 * Trilinear interpolation in 3D LUT
 */
function sampleLUT3D(
  lut: LUT3D,
  r: number,
  g: number,
  b: number,
): [number, number, number] {
  const size = lut.size;
  const maxIdx = size - 1;

  // Scale input to LUT indices
  const rIdx = r * maxIdx;
  const gIdx = g * maxIdx;
  const bIdx = b * maxIdx;

  // Get integer and fractional parts
  const r0 = Math.floor(rIdx);
  const g0 = Math.floor(gIdx);
  const b0 = Math.floor(bIdx);
  const r1 = Math.min(r0 + 1, maxIdx);
  const g1 = Math.min(g0 + 1, maxIdx);
  const b1 = Math.min(b0 + 1, maxIdx);

  const rFrac = rIdx - r0;
  const gFrac = gIdx - g0;
  const bFrac = bIdx - b0;

  // Helper to get LUT value at index
  const getLUT = (
    ri: number,
    gi: number,
    bi: number,
    channel: number,
  ): number => {
    const idx = ((bi * size + gi) * size + ri) * 3 + channel;
    // Type proof: lut.data[idx] ∈ ℝ ∪ {undefined} → lut.data[idx] ∈ ℝ
    const value = lut.data[idx];
    return isFiniteNumber(value) ? value : 0;
  };

  // Trilinear interpolation for each channel
  const result: [number, number, number] = [0, 0, 0];
  for (let c = 0; c < 3; c++) {
    const c000 = getLUT(r0, g0, b0, c);
    const c100 = getLUT(r1, g0, b0, c);
    const c010 = getLUT(r0, g1, b0, c);
    const c110 = getLUT(r1, g1, b0, c);
    const c001 = getLUT(r0, g0, b1, c);
    const c101 = getLUT(r1, g0, b1, c);
    const c011 = getLUT(r0, g1, b1, c);
    const c111 = getLUT(r1, g1, b1, c);

    // Interpolate along R
    const c00 = c000 + (c100 - c000) * rFrac;
    const c10 = c010 + (c110 - c010) * rFrac;
    const c01 = c001 + (c101 - c001) * rFrac;
    const c11 = c011 + (c111 - c011) * rFrac;

    // Interpolate along G
    const c0 = c00 + (c10 - c00) * gFrac;
    const c1 = c01 + (c11 - c01) * gFrac;

    // Interpolate along B
    result[c] = c0 + (c1 - c0) * bFrac;
  }

  return result;
}

/**
 * LUT effect renderer
 *
 * Applies a 3D Look-Up Table for color grading.
 *
 * Parameters:
 * - lutData: Base64-encoded .cube file content or LUT ID from cache
 * - intensity: 0 to 100 (blend with original)
 */
export function lutRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const lutData = params.lutData as string;
  // Validate intensity param (NaN causes black pixel corruption)
  // Type proof: intensity ∈ ℝ ∧ finite(intensity) → intensity ∈ [0, 100]
  const intensityValue = params.intensity;
  const intensity = isFiniteNumber(intensityValue)
    ? Math.max(0, Math.min(100, intensityValue)) / 100
    : 1;

  if (!lutData || intensity === 0) {
    return input;
  }

  // Try to get LUT from cache or parse it
  let lut: LUT3D;
  if (lutCache.has(lutData)) {
    lut = lutCache.get(lutData)!;
  } else {
    try {
      // Assume lutData is base64-encoded .cube content
      const content = atob(lutData);
      lut = parseCubeLUT(content);
      lutCache.set(lutData, lut);
    } catch (e) {
      console.warn("Failed to parse LUT:", e);
      return input;
    }
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(
    0,
    0,
    input.canvas.width,
    input.canvas.height,
  );
  const data = imageData.data;

  for (let i = 0; i < data.length; i += 4) {
    // Normalize input RGB to 0-1
    const r = data[i] / 255;
    const g = data[i + 1] / 255;
    const b = data[i + 2] / 255;

    // Sample LUT
    const [lr, lg, lb] = sampleLUT3D(lut, r, g, b);

    // Blend with original based on intensity
    data[i] = Math.max(
      0,
      Math.min(255, (r * (1 - intensity) + lr * intensity) * 255),
    );
    data[i + 1] = Math.max(
      0,
      Math.min(255, (g * (1 - intensity) + lg * intensity) * 255),
    );
    data[i + 2] = Math.max(
      0,
      Math.min(255, (b * (1 - intensity) + lb * intensity) * 255),
    );
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

/**
 * Register a LUT in the cache by name
 */
export function registerLUT(name: string, cubeContent: string): void {
  const lut = parseCubeLUT(cubeContent);
  lutCache.set(name, lut);
}

/**
 * Get list of registered LUT names
 */
export function getRegisteredLUTs(): string[] {
  return Array.from(lutCache.keys());
}

/**
 * Clear LUT cache
 */
export function clearLUTCache(): void {
  lutCache.clear();
}

// NOTE: Advanced color grading effects (liftGammaGainRenderer, hslSecondaryRenderer,
// hueVsCurvesRenderer, colorMatchRenderer) have been moved to colorGrading.ts

// ═══════════════════════════════════════════════════════════════════════════
//                                                             // registration
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Register all color correction effect renderers
 */
export function registerColorEffects(): void {
  // Register basic color effects
  registerEffectRenderer("brightness-contrast", brightnessContrastRenderer);
  registerEffectRenderer("hue-saturation", hueSaturationRenderer);
  registerEffectRenderer("levels", levelsRenderer);
  registerEffectRenderer("tint", tintRenderer);
  registerEffectRenderer("curves", curvesRenderer);
  registerEffectRenderer("glow", glowRenderer);
  registerEffectRenderer("drop-shadow", dropShadowRenderer);
  registerEffectRenderer("color-balance", colorBalanceRenderer);
  registerEffectRenderer("exposure", exposureRenderer);
  registerEffectRenderer("vibrance", vibranceRenderer);
  registerEffectRenderer("invert", invertRenderer);
  registerEffectRenderer("posterize", posterizeRenderer);
  registerEffectRenderer("threshold", thresholdRenderer);
  registerEffectRenderer("vignette", vignetteRenderer);
  registerEffectRenderer("lut", lutRenderer);

  // Register advanced color grading effects from colorGrading.ts
  registerColorGradingEffects();
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
  vignetteRenderer,
  lutRenderer,
  liftGammaGainRenderer,
  hslSecondaryRenderer,
  hueVsCurvesRenderer,
  colorMatchRenderer,
  parseCubeLUT,
  registerLUT,
  getRegisteredLUTs,
  clearLUTCache,
  createSCurve,
  createLiftCurve,
  registerColorEffects,
};
