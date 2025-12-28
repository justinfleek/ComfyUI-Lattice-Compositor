/**
 * Advanced Color Grading Effect Renderers
 *
 * Professional color grading tools:
 * - Lift/Gamma/Gain (ASC CDL-style three-way color correction)
 * - HSL Secondary (Qualify and correct specific color ranges)
 * - Hue vs Curves (HSL-space curve adjustments)
 * - Color Match (Match color distribution to reference)
 *
 * Extracted from colorRenderer.ts for modularity.
 */
import {
  registerEffectRenderer,
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams
} from '../effectProcessor';

// ============================================================================
// LIFT/GAMMA/GAIN
// ============================================================================

/**
 * Lift/Gamma/Gain effect renderer - ASC CDL-style three-way color correction
 *
 * Formula per channel: output = (input * gain + lift) ^ (1/gamma)
 *
 * Parameters:
 * - lift_red/green/blue: -1 to 1 (adds to shadows)
 * - gamma_red/green/blue: 0.1 to 4 (midtone curve, 1 = no change)
 * - gain_red/green/blue: 0 to 4 (multiplies highlights, 1 = no change)
 */
export function liftGammaGainRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // Lift (shadow adjustment) - validate for NaN
  const liftRRaw = params.lift_red ?? 0;
  const liftGRaw = params.lift_green ?? 0;
  const liftBRaw = params.lift_blue ?? 0;
  const liftR = Number.isFinite(liftRRaw) ? Math.max(-1, Math.min(1, liftRRaw)) : 0;
  const liftG = Number.isFinite(liftGRaw) ? Math.max(-1, Math.min(1, liftGRaw)) : 0;
  const liftB = Number.isFinite(liftBRaw) ? Math.max(-1, Math.min(1, liftBRaw)) : 0;

  // Gamma (midtone adjustment) - validate for NaN
  const gammaRRaw = params.gamma_red ?? 1;
  const gammaGRaw = params.gamma_green ?? 1;
  const gammaBRaw = params.gamma_blue ?? 1;
  const gammaR = Number.isFinite(gammaRRaw) ? Math.max(0.1, Math.min(4, gammaRRaw)) : 1;
  const gammaG = Number.isFinite(gammaGRaw) ? Math.max(0.1, Math.min(4, gammaGRaw)) : 1;
  const gammaB = Number.isFinite(gammaBRaw) ? Math.max(0.1, Math.min(4, gammaBRaw)) : 1;

  // Gain (highlight adjustment) - validate for NaN
  const gainRRaw = params.gain_red ?? 1;
  const gainGRaw = params.gain_green ?? 1;
  const gainBRaw = params.gain_blue ?? 1;
  const gainR = Number.isFinite(gainRRaw) ? Math.max(0, Math.min(4, gainRRaw)) : 1;
  const gainG = Number.isFinite(gainGRaw) ? Math.max(0, Math.min(4, gainGRaw)) : 1;
  const gainB = Number.isFinite(gainBRaw) ? Math.max(0, Math.min(4, gainBRaw)) : 1;

  // No change if all values are default
  if (liftR === 0 && liftG === 0 && liftB === 0 &&
      gammaR === 1 && gammaG === 1 && gammaB === 1 &&
      gainR === 1 && gainG === 1 && gainB === 1) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  // Build LUTs for each channel for performance
  const lutR = new Uint8Array(256);
  const lutG = new Uint8Array(256);
  const lutB = new Uint8Array(256);

  // sRGB gamma functions
  const sRGBToLinear = (v: number): number => {
    const normalized = v / 255;
    return normalized <= 0.04045
      ? normalized / 12.92
      : Math.pow((normalized + 0.055) / 1.055, 2.4);
  };

  const linearToSRGB = (v: number): number => {
    const clamped = Math.max(0, Math.min(1, v));
    return clamped <= 0.0031308
      ? Math.round(clamped * 12.92 * 255)
      : Math.round((1.055 * Math.pow(clamped, 1 / 2.4) - 0.055) * 255);
  };

  // Build LUTs
  for (let i = 0; i < 256; i++) {
    // Convert to linear space
    const linearR = sRGBToLinear(i);
    const linearG = sRGBToLinear(i);
    const linearB = sRGBToLinear(i);

    // Apply ASC CDL formula: (input * gain + lift) ^ (1/gamma)
    // Lift is applied before gamma, affecting primarily shadows
    const gradedR = Math.pow(Math.max(0, linearR * gainR + liftR), 1 / Math.max(0.1, gammaR));
    const gradedG = Math.pow(Math.max(0, linearG * gainG + liftG), 1 / Math.max(0.1, gammaG));
    const gradedB = Math.pow(Math.max(0, linearB * gainB + liftB), 1 / Math.max(0.1, gammaB));

    // Convert back to sRGB
    lutR[i] = linearToSRGB(gradedR);
    lutG[i] = linearToSRGB(gradedG);
    lutB[i] = linearToSRGB(gradedB);
  }

  // Apply LUTs
  for (let i = 0; i < data.length; i += 4) {
    data[i] = lutR[data[i]];
    data[i + 1] = lutG[data[i + 1]];
    data[i + 2] = lutB[data[i + 2]];
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// HSL SECONDARY QUALIFICATION
// ============================================================================

/**
 * HSL Secondary effect renderer - Qualify and correct specific color ranges
 *
 * Parameters:
 * Qualification:
 * - hue_center: 0-360 (target hue)
 * - hue_width: 0-180 (range around center)
 * - hue_falloff: 0-90 (soft edge transition)
 * - sat_min/max: 0-100 (saturation range)
 * - sat_falloff: 0-50 (saturation soft edge)
 * - lum_min/max: 0-100 (luminance range)
 * - lum_falloff: 0-50 (luminance soft edge)
 *
 * Correction:
 * - hue_shift: -180 to 180
 * - sat_adjust: -100 to 100
 * - lum_adjust: -100 to 100
 *
 * Preview:
 * - show_mask: boolean (shows qualification mask)
 */
export function hslSecondaryRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // Helper to safely get numeric params
  const safeNum = (val: unknown, def: number, min?: number, max?: number): number => {
    const num = typeof val === 'number' && Number.isFinite(val) ? val : def;
    if (min !== undefined && max !== undefined) return Math.max(min, Math.min(max, num));
    return num;
  };

  // Qualification parameters - validate for NaN
  const hueCenter = safeNum(params.hue_center, 0, 0, 360);
  const hueWidth = safeNum(params.hue_width, 30, 0, 180);
  const hueFalloff = safeNum(params.hue_falloff, 10, 0, 90);
  const satMin = safeNum(params.sat_min, 0, 0, 100) / 100;
  const satMax = safeNum(params.sat_max, 100, 0, 100) / 100;
  const satFalloff = safeNum(params.sat_falloff, 10, 0, 50) / 100;
  const lumMin = safeNum(params.lum_min, 0, 0, 100) / 100;
  const lumMax = safeNum(params.lum_max, 100, 0, 100) / 100;
  const lumFalloff = safeNum(params.lum_falloff, 10, 0, 50) / 100;

  // Correction parameters - validate for NaN
  const hueShift = safeNum(params.hue_shift, 0, -180, 180);
  const satAdjust = safeNum(params.sat_adjust, 0, -100, 100) / 100;
  const lumAdjust = safeNum(params.lum_adjust, 0, -100, 100) / 100;

  // Preview
  const showMask = params.show_mask ?? false;

  // No change if no correction applied
  if (!showMask && hueShift === 0 && satAdjust === 0 && lumAdjust === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  // Helper: RGB to HSL
  const rgbToHsl = (r: number, g: number, b: number): [number, number, number] => {
    const rn = r / 255;
    const gn = g / 255;
    const bn = b / 255;
    const max = Math.max(rn, gn, bn);
    const min = Math.min(rn, gn, bn);
    const l = (max + min) / 2;

    if (max === min) return [0, 0, l];

    const d = max - min;
    const s = l > 0.5 ? d / (2 - max - min) : d / (max + min);

    let h: number;
    switch (max) {
      case rn: h = ((gn - bn) / d + (gn < bn ? 6 : 0)) / 6; break;
      case gn: h = ((bn - rn) / d + 2) / 6; break;
      default: h = ((rn - gn) / d + 4) / 6; break;
    }
    return [h * 360, s, l];
  };

  // Helper: HSL to RGB
  const hslToRgb = (h: number, s: number, l: number): [number, number, number] => {
    h = ((h % 360) + 360) % 360 / 360;
    if (s === 0) {
      const v = Math.round(l * 255);
      return [v, v, v];
    }
    const hue2rgb = (p: number, q: number, t: number): number => {
      if (t < 0) t += 1;
      if (t > 1) t -= 1;
      if (t < 1/6) return p + (q - p) * 6 * t;
      if (t < 1/2) return q;
      if (t < 2/3) return p + (q - p) * (2/3 - t) * 6;
      return p;
    };
    const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
    const p = 2 * l - q;
    return [
      Math.round(hue2rgb(p, q, h + 1/3) * 255),
      Math.round(hue2rgb(p, q, h) * 255),
      Math.round(hue2rgb(p, q, h - 1/3) * 255)
    ];
  };

  // Soft range function with falloff
  const softRange = (value: number, min: number, max: number, falloff: number): number => {
    if (value < min - falloff || value > max + falloff) return 0;
    if (value >= min && value <= max) return 1;

    if (value < min) {
      // Fade in from min - falloff to min
      return falloff > 0 ? (value - (min - falloff)) / falloff : 0;
    } else {
      // Fade out from max to max + falloff
      return falloff > 0 ? 1 - (value - max) / falloff : 0;
    }
  };

  // Hue range function (handles wraparound)
  const hueMatch = (hue: number, center: number, width: number, falloff: number): number => {
    // Calculate shortest distance on color wheel
    let diff = Math.abs(hue - center);
    if (diff > 180) diff = 360 - diff;

    const halfWidth = width / 2;
    if (diff <= halfWidth) return 1;
    if (diff > halfWidth + falloff) return 0;
    return 1 - (diff - halfWidth) / falloff;
  };

  // Process pixels
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];

    const [h, s, l] = rgbToHsl(r, g, b);

    // Compute qualification mask
    const hMatch = hueMatch(h, hueCenter, hueWidth, hueFalloff);
    const sMatch = softRange(s, satMin, satMax, satFalloff);
    const lMatch = softRange(l, lumMin, lumMax, lumFalloff);
    const qualification = hMatch * sMatch * lMatch;

    if (showMask) {
      // Show qualification mask as grayscale
      const maskValue = Math.round(qualification * 255);
      data[i] = maskValue;
      data[i + 1] = maskValue;
      data[i + 2] = maskValue;
    } else if (qualification > 0) {
      // Apply correction with qualification strength
      const newH = h + hueShift * qualification;
      const newS = Math.max(0, Math.min(1, s + satAdjust * qualification));
      const newL = Math.max(0, Math.min(1, l + lumAdjust * qualification));

      const [newR, newG, newB] = hslToRgb(newH, newS, newL);

      // Blend based on qualification
      data[i] = Math.round(r + (newR - r) * qualification);
      data[i + 1] = Math.round(g + (newG - g) * qualification);
      data[i + 2] = Math.round(b + (newB - b) * qualification);
    }
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// HUE VS CURVES
// ============================================================================

/**
 * Hue vs Curves effect renderer - HSL-space curve adjustments
 *
 * Curve Types (each is array of {x, y} points):
 * - hue_vs_hue: Shift specific hues to different hues (x: 0-360, y: -180 to +180 delta)
 * - hue_vs_sat: Adjust saturation for specific hues (x: 0-360, y: -100 to +100 delta)
 * - hue_vs_lum: Adjust luminance for specific hues (x: 0-360, y: -100 to +100 delta)
 * - lum_vs_sat: Adjust saturation based on luminance (x: 0-100, y: -100 to +100 delta)
 * - sat_vs_sat: Compress/expand saturation range (x: 0-100, y: 0-100 output)
 */
export function hueVsCurvesRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // Parse curve data (arrays of control points)
  const hueVsHue: Array<{x: number, y: number}> = params.hue_vs_hue ?? [];
  const hueVsSat: Array<{x: number, y: number}> = params.hue_vs_sat ?? [];
  const hueVsLum: Array<{x: number, y: number}> = params.hue_vs_lum ?? [];
  const lumVsSat: Array<{x: number, y: number}> = params.lum_vs_sat ?? [];
  const satVsSat: Array<{x: number, y: number}> = params.sat_vs_sat ?? [];

  // No curves defined = no change
  if (hueVsHue.length === 0 && hueVsSat.length === 0 && hueVsLum.length === 0 &&
      lumVsSat.length === 0 && satVsSat.length === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;

  // Build LUTs from curves
  const buildCurveLUT = (
    points: Array<{x: number, y: number}>,
    inputRange: number,
    outputRange: number,
    isDelta: boolean = true
  ): Float32Array => {
    const lut = new Float32Array(Math.ceil(inputRange) + 1);

    if (points.length === 0) {
      // Identity: no change (0 for delta, input for absolute)
      for (let i = 0; i <= inputRange; i++) {
        lut[i] = isDelta ? 0 : i;
      }
      return lut;
    }

    // Sort points by x
    const sorted = [...points].sort((a, b) => a.x - b.x);

    // Interpolate between points
    for (let i = 0; i <= inputRange; i++) {
      const x = i;

      // Find surrounding points
      let p0 = sorted[0];
      let p1 = sorted[sorted.length - 1];

      for (let j = 0; j < sorted.length - 1; j++) {
        if (x >= sorted[j].x && x <= sorted[j + 1].x) {
          p0 = sorted[j];
          p1 = sorted[j + 1];
          break;
        }
      }

      // Linear interpolation
      if (p0.x === p1.x) {
        lut[i] = p0.y;
      } else {
        const t = (x - p0.x) / (p1.x - p0.x);
        lut[i] = p0.y + (p1.y - p0.y) * t;
      }

      // Clamp output
      if (isDelta) {
        lut[i] = Math.max(-outputRange, Math.min(outputRange, lut[i]));
      } else {
        lut[i] = Math.max(0, Math.min(outputRange, lut[i]));
      }
    }

    return lut;
  };

  // Build LUTs
  const hueVsHueLUT = buildCurveLUT(hueVsHue, 360, 180, true);
  const hueVsSatLUT = buildCurveLUT(hueVsSat, 360, 100, true);
  const hueVsLumLUT = buildCurveLUT(hueVsLum, 360, 100, true);
  const lumVsSatLUT = buildCurveLUT(lumVsSat, 100, 100, true);
  const satVsSatLUT = buildCurveLUT(satVsSat, 100, 100, false);

  // RGB <-> HSL helpers
  const rgbToHsl = (r: number, g: number, b: number): [number, number, number] => {
    const rn = r / 255, gn = g / 255, bn = b / 255;
    const max = Math.max(rn, gn, bn), min = Math.min(rn, gn, bn);
    const l = (max + min) / 2;
    if (max === min) return [0, 0, l];
    const d = max - min;
    const s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    let h: number;
    switch (max) {
      case rn: h = ((gn - bn) / d + (gn < bn ? 6 : 0)) / 6; break;
      case gn: h = ((bn - rn) / d + 2) / 6; break;
      default: h = ((rn - gn) / d + 4) / 6; break;
    }
    return [h * 360, s * 100, l * 100];
  };

  const hslToRgb = (h: number, s: number, l: number): [number, number, number] => {
    h = ((h % 360) + 360) % 360 / 360;
    s = s / 100;
    l = l / 100;
    if (s === 0) { const v = Math.round(l * 255); return [v, v, v]; }
    const hue2rgb = (p: number, q: number, t: number): number => {
      if (t < 0) t += 1; if (t > 1) t -= 1;
      if (t < 1/6) return p + (q - p) * 6 * t;
      if (t < 1/2) return q;
      if (t < 2/3) return p + (q - p) * (2/3 - t) * 6;
      return p;
    };
    const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
    const p = 2 * l - q;
    return [
      Math.round(hue2rgb(p, q, h + 1/3) * 255),
      Math.round(hue2rgb(p, q, h) * 255),
      Math.round(hue2rgb(p, q, h - 1/3) * 255)
    ];
  };

  // Process pixels
  for (let i = 0; i < data.length; i += 4) {
    let [h, s, l] = rgbToHsl(data[i], data[i + 1], data[i + 2]);

    const hueIdx = Math.round(h) % 360;
    const satIdx = Math.round(s);
    const lumIdx = Math.round(l);

    // Apply curves in order
    // 1. Hue vs Hue (delta)
    if (hueVsHue.length > 0) {
      h = h + hueVsHueLUT[hueIdx];
    }

    // 2. Hue vs Sat (delta)
    if (hueVsSat.length > 0) {
      s = s + hueVsSatLUT[hueIdx];
    }

    // 3. Hue vs Lum (delta)
    if (hueVsLum.length > 0) {
      l = l + hueVsLumLUT[hueIdx];
    }

    // 4. Lum vs Sat (delta based on luminance)
    if (lumVsSat.length > 0) {
      s = s + lumVsSatLUT[lumIdx];
    }

    // 5. Sat vs Sat (absolute remapping)
    if (satVsSat.length > 0) {
      s = satVsSatLUT[Math.round(Math.max(0, Math.min(100, s)))];
    }

    // Clamp final values
    h = ((h % 360) + 360) % 360;
    s = Math.max(0, Math.min(100, s));
    l = Math.max(0, Math.min(100, l));

    const [r, g, b] = hslToRgb(h, s, l);
    data[i] = r;
    data[i + 1] = g;
    data[i + 2] = b;
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// COLOR MATCH
// ============================================================================

/**
 * Color Match effect renderer - Match color distribution to reference
 *
 * Parameters:
 * - reference_histogram_r: Uint32Array (256 bins for red channel reference)
 * - reference_histogram_g: Uint32Array (256 bins for green channel reference)
 * - reference_histogram_b: Uint32Array (256 bins for blue channel reference)
 * - reference_pixels: number (total pixel count in reference)
 * - strength: 0-100 (blend with original)
 * - match_luminance: boolean (default true)
 * - match_color: boolean (default true)
 */
export function colorMatchRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const refHistR = params.reference_histogram_r as Uint32Array | undefined;
  const refHistG = params.reference_histogram_g as Uint32Array | undefined;
  const refHistB = params.reference_histogram_b as Uint32Array | undefined;
  const refPixelsRaw = params.reference_pixels as number | undefined;
  const refPixels = typeof refPixelsRaw === 'number' && Number.isFinite(refPixelsRaw) && refPixelsRaw > 0
    ? refPixelsRaw : 0;
  const strengthRaw = (params.strength ?? 100) / 100;
  const strength = Number.isFinite(strengthRaw) ? Math.max(0, Math.min(1, strengthRaw)) : 0;
  const matchLuminance = params.match_luminance ?? true;
  const matchColor = params.match_color ?? true;

  // No reference = no change (also check refPixels > 0 to prevent div/0)
  if (!refHistR || !refHistG || !refHistB || refPixels <= 0 || strength === 0) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const imageData = input.ctx.getImageData(0, 0, input.canvas.width, input.canvas.height);
  const data = imageData.data;
  const pixelCount = input.canvas.width * input.canvas.height;

  // Early return if source image is empty (prevents div/0)
  if (pixelCount <= 0) {
    return input;
  }

  // Compute source histograms
  const srcHistR = new Uint32Array(256);
  const srcHistG = new Uint32Array(256);
  const srcHistB = new Uint32Array(256);

  for (let i = 0; i < data.length; i += 4) {
    srcHistR[data[i]]++;
    srcHistG[data[i + 1]]++;
    srcHistB[data[i + 2]]++;
  }

  // Build histogram matching LUTs
  const buildMatchingLUT = (srcHist: Uint32Array, refHist: Uint32Array): Uint8Array => {
    const lut = new Uint8Array(256);

    // Compute CDFs
    const srcCDF = new Float32Array(256);
    const refCDF = new Float32Array(256);

    srcCDF[0] = srcHist[0] / pixelCount;
    refCDF[0] = refHist[0] / refPixels;

    for (let i = 1; i < 256; i++) {
      srcCDF[i] = srcCDF[i - 1] + srcHist[i] / pixelCount;
      refCDF[i] = refCDF[i - 1] + refHist[i] / refPixels;
    }

    // Build LUT
    for (let i = 0; i < 256; i++) {
      const srcVal = srcCDF[i];
      let bestMatch = 0;
      let bestDiff = Math.abs(refCDF[0] - srcVal);

      for (let j = 1; j < 256; j++) {
        const diff = Math.abs(refCDF[j] - srcVal);
        if (diff < bestDiff) {
          bestDiff = diff;
          bestMatch = j;
        }
      }

      lut[i] = bestMatch;
    }

    return lut;
  };

  // Build LUTs based on matching mode
  let lutR: Uint8Array | null = null;
  let lutG: Uint8Array | null = null;
  let lutB: Uint8Array | null = null;

  if (matchColor) {
    lutR = buildMatchingLUT(srcHistR, refHistR);
    lutG = buildMatchingLUT(srcHistG, refHistG);
    lutB = buildMatchingLUT(srcHistB, refHistB);
  }

  // For luminance matching, build a luminance LUT
  let lumLUT: Uint8Array | null = null;
  if (matchLuminance && !matchColor) {
    // Compute luminance histograms
    const srcLumHist = new Uint32Array(256);
    const refLumHist = new Uint32Array(256);

    // Source luminance
    for (let i = 0; i < data.length; i += 4) {
      const lum = Math.round(data[i] * 0.2126 + data[i + 1] * 0.7152 + data[i + 2] * 0.0722);
      srcLumHist[Math.min(255, lum)]++;
    }

    // Reference luminance (estimated from RGB histograms)
    // This is an approximation - ideally we'd have the reference image
    for (let i = 0; i < 256; i++) {
      const avgCount = (refHistR[i] + refHistG[i] + refHistB[i]) / 3;
      refLumHist[i] = Math.round(avgCount);
    }

    lumLUT = buildMatchingLUT(srcLumHist, refLumHist);
  }

  // Apply color matching
  for (let i = 0; i < data.length; i += 4) {
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];

    let newR = r, newG = g, newB = b;

    if (matchColor && lutR && lutG && lutB) {
      newR = lutR[r];
      newG = lutG[g];
      newB = lutB[b];
    } else if (matchLuminance && lumLUT) {
      // Apply luminance shift while preserving color ratios
      const lum = r * 0.2126 + g * 0.7152 + b * 0.0722;
      const newLum = lumLUT[Math.round(lum)];
      const lumRatio = lum > 0 ? newLum / lum : 1;

      newR = Math.min(255, Math.round(r * lumRatio));
      newG = Math.min(255, Math.round(g * lumRatio));
      newB = Math.min(255, Math.round(b * lumRatio));
    }

    // Blend with strength
    data[i] = Math.round(r + (newR - r) * strength);
    data[i + 1] = Math.round(g + (newG - g) * strength);
    data[i + 2] = Math.round(b + (newB - b) * strength);
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// REGISTRATION
// ============================================================================

/**
 * Register all color grading effect renderers
 */
export function registerColorGradingEffects(): void {
  registerEffectRenderer('lift-gamma-gain', liftGammaGainRenderer);
  registerEffectRenderer('hsl-secondary', hslSecondaryRenderer);
  registerEffectRenderer('hue-vs-curves', hueVsCurvesRenderer);
  registerEffectRenderer('color-match', colorMatchRenderer);
}
