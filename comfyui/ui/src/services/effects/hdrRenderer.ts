/**
 * hdrRenderer.ts - HDR/LAB Color Space Effects
 *
 * Provides professional HDR processing using LAB color space for
 * perceptually accurate luminance adjustments.
 *
 * Based on ComfyUI-SuperBeasts HDR node concepts.
 */

// =============================================================================
// TYPES
// =============================================================================

export interface HDRParams {
  intensity: number; // 0.0 - 5.0, overall HDR effect strength
  shadowIntensity: number; // 0.0 - 1.0, shadow recovery
  highlightIntensity: number; // 0.0 - 1.0, highlight recovery
  gamma: number; // 0.1 - 3.0, gamma correction
  contrast: number; // 0.0 - 2.0, contrast enhancement
  saturationBoost: number; // 0.0 - 2.0, color saturation
}

export interface LABColor {
  L: number; // Lightness: 0-100
  a: number; // Green-Red: -128 to 127
  b: number; // Blue-Yellow: -128 to 127
}

export interface RGBColor {
  r: number; // 0-255
  g: number; // 0-255
  b: number; // 0-255
}

export interface XYZColor {
  X: number;
  Y: number;
  Z: number;
}

// =============================================================================
// COLOR SPACE CONVERSION
// =============================================================================

// D65 illuminant reference values
const REF_X = 95.047;
const REF_Y = 100.0;
const REF_Z = 108.883;

/**
 * Convert RGB to XYZ color space
 */
function rgbToXyz(rgb: RGBColor): XYZColor {
  // Normalize and linearize RGB
  let r = rgb.r / 255;
  let g = rgb.g / 255;
  let b = rgb.b / 255;

  // sRGB gamma correction (inverse)
  r = r > 0.04045 ? ((r + 0.055) / 1.055) ** 2.4 : r / 12.92;
  g = g > 0.04045 ? ((g + 0.055) / 1.055) ** 2.4 : g / 12.92;
  b = b > 0.04045 ? ((b + 0.055) / 1.055) ** 2.4 : b / 12.92;

  // Scale to 100
  r *= 100;
  g *= 100;
  b *= 100;

  // Convert to XYZ using sRGB matrix (D65)
  return {
    X: r * 0.4124564 + g * 0.3575761 + b * 0.1804375,
    Y: r * 0.2126729 + g * 0.7151522 + b * 0.072175,
    Z: r * 0.0193339 + g * 0.119192 + b * 0.9503041,
  };
}

/**
 * Convert XYZ to RGB color space
 */
function xyzToRgb(xyz: XYZColor): RGBColor {
  const x = xyz.X / 100;
  const y = xyz.Y / 100;
  const z = xyz.Z / 100;

  // Convert XYZ to linear RGB
  let r = x * 3.2404542 + y * -1.5371385 + z * -0.4985314;
  let g = x * -0.969266 + y * 1.8760108 + z * 0.041556;
  let b = x * 0.0556434 + y * -0.2040259 + z * 1.0572252;

  // Apply sRGB gamma correction
  r = r > 0.0031308 ? 1.055 * r ** (1 / 2.4) - 0.055 : 12.92 * r;
  g = g > 0.0031308 ? 1.055 * g ** (1 / 2.4) - 0.055 : 12.92 * g;
  b = b > 0.0031308 ? 1.055 * b ** (1 / 2.4) - 0.055 : 12.92 * b;

  // Clamp and scale to 0-255
  return {
    r: Math.max(0, Math.min(255, Math.round(r * 255))),
    g: Math.max(0, Math.min(255, Math.round(g * 255))),
    b: Math.max(0, Math.min(255, Math.round(b * 255))),
  };
}

/**
 * Convert XYZ to LAB color space
 */
function xyzToLab(xyz: XYZColor): LABColor {
  let x = xyz.X / REF_X;
  let y = xyz.Y / REF_Y;
  let z = xyz.Z / REF_Z;

  // Apply LAB conversion function
  const epsilon = 0.008856;
  const kappa = 903.3;

  x = x > epsilon ? x ** (1 / 3) : (kappa * x + 16) / 116;
  y = y > epsilon ? y ** (1 / 3) : (kappa * y + 16) / 116;
  z = z > epsilon ? z ** (1 / 3) : (kappa * z + 16) / 116;

  return {
    L: 116 * y - 16,
    a: 500 * (x - y),
    b: 200 * (y - z),
  };
}

/**
 * Convert LAB to XYZ color space
 */
function labToXyz(lab: LABColor): XYZColor {
  const y = (lab.L + 16) / 116;
  const x = lab.a / 500 + y;
  const z = y - lab.b / 200;

  const epsilon = 0.008856;
  const kappa = 903.3;

  const x3 = x * x * x;
  const z3 = z * z * z;

  return {
    X: REF_X * (x3 > epsilon ? x3 : (116 * x - 16) / kappa),
    Y:
      REF_Y *
      (lab.L > kappa * epsilon ? ((lab.L + 16) / 116) ** 3 : lab.L / kappa),
    Z: REF_Z * (z3 > epsilon ? z3 : (116 * z - 16) / kappa),
  };
}

/**
 * Convert RGB to LAB
 */
export function rgbToLab(rgb: RGBColor): LABColor {
  return xyzToLab(rgbToXyz(rgb));
}

/**
 * Convert LAB to RGB
 */
export function labToRgb(lab: LABColor): RGBColor {
  return xyzToRgb(labToXyz(lab));
}

// =============================================================================
// HDR PROCESSING
// =============================================================================

/**
 * Create luminance mask based on LAB L channel
 */
function createLuminanceMask(
  L: number,
  targetRange: "shadows" | "midtones" | "highlights",
): number {
  // Normalize L to 0-1
  const normalizedL = L / 100;

  switch (targetRange) {
    case "shadows":
      // Affects darker areas more strongly
      return 1 - normalizedL ** 0.5;

    case "midtones":
      // Bell curve centered at 0.5
      return 1 - 4 * (normalizedL - 0.5) ** 2;

    case "highlights":
      // Affects lighter areas more strongly
      return normalizedL ** 0.5;

    default:
      return 1;
  }
}

/**
 * Apply HDR tone mapping to a single LAB pixel
 */
function processLABPixel(lab: LABColor, params: HDRParams): LABColor {
  let { L, a, b } = lab;

  // Calculate luminance masks
  const shadowMask = createLuminanceMask(L, "shadows");
  const highlightMask = createLuminanceMask(L, "highlights");

  // Shadow recovery: lift dark areas
  const shadowLift =
    shadowMask * params.shadowIntensity * params.intensity * 20;
  L = L + shadowLift;

  // Highlight recovery: compress bright areas
  const highlightCompress =
    highlightMask * params.highlightIntensity * params.intensity * 15;
  L = L - highlightCompress;

  // Apply gamma correction
  L = (L / 100) ** (1 / params.gamma) * 100;

  // Apply contrast (S-curve)
  if (params.contrast !== 1.0) {
    const normalizedL = L / 100;
    const contrastFactor = params.contrast;

    // S-curve contrast
    const contrastedL =
      normalizedL < 0.5
        ? 0.5 * (2 * normalizedL) ** contrastFactor
        : 1 - 0.5 * (2 * (1 - normalizedL)) ** contrastFactor;

    L = contrastedL * 100;
  }

  // Apply saturation boost to a/b channels
  if (params.saturationBoost !== 1.0) {
    const satFactor = params.saturationBoost * params.intensity;
    a = a * satFactor;
    b = b * satFactor;
  }

  // Clamp values
  L = Math.max(0, Math.min(100, L));
  a = Math.max(-128, Math.min(127, a));
  b = Math.max(-128, Math.min(127, b));

  return { L, a, b };
}

/**
 * Apply HDR effect to an ImageData object
 */
export function applyHDREffect(input: ImageData, params: HDRParams): ImageData {
  const output = new ImageData(
    new Uint8ClampedArray(input.data),
    input.width,
    input.height,
  );

  const data = output.data;

  for (let i = 0; i < data.length; i += 4) {
    // Get RGB values
    const rgb: RGBColor = {
      r: data[i],
      g: data[i + 1],
      b: data[i + 2],
    };

    // Convert to LAB
    const lab = rgbToLab(rgb);

    // Process in LAB space
    const processedLab = processLABPixel(lab, params);

    // Convert back to RGB
    const processedRgb = labToRgb(processedLab);

    // Write back
    data[i] = processedRgb.r;
    data[i + 1] = processedRgb.g;
    data[i + 2] = processedRgb.b;
    // Alpha unchanged
  }

  return output;
}

// =============================================================================
// ADDITIONAL LAB-BASED EFFECTS
// =============================================================================

export interface ColorBalanceLABParams {
  shadowsCyan_Red: number; // -100 to 100
  shadowsMagenta_Green: number;
  shadowsYellow_Blue: number;
  midtonesCyan_Red: number;
  midtonesMagenta_Green: number;
  midtonesYellow_Blue: number;
  highlightsCyan_Red: number;
  highlightsMagenta_Green: number;
  highlightsYellow_Blue: number;
  preserveLuminosity: boolean;
}

/**
 * Apply color balance adjustments in LAB space
 */
export function applyColorBalanceLAB(
  input: ImageData,
  params: ColorBalanceLABParams,
): ImageData {
  const output = new ImageData(
    new Uint8ClampedArray(input.data),
    input.width,
    input.height,
  );

  const data = output.data;

  for (let i = 0; i < data.length; i += 4) {
    const rgb: RGBColor = {
      r: data[i],
      g: data[i + 1],
      b: data[i + 2],
    };

    const lab = rgbToLab(rgb);
    const originalL = lab.L;

    // Calculate masks
    const shadowMask = createLuminanceMask(lab.L, "shadows");
    const midtoneMask = createLuminanceMask(lab.L, "midtones");
    const highlightMask = createLuminanceMask(lab.L, "highlights");

    // Apply shadow adjustments
    lab.a += shadowMask * params.shadowsCyan_Red * 0.5;
    lab.b += shadowMask * params.shadowsYellow_Blue * 0.5;
    // Magenta-Green affects both a and b
    lab.a += shadowMask * params.shadowsMagenta_Green * 0.25;
    lab.b -= shadowMask * params.shadowsMagenta_Green * 0.25;

    // Apply midtone adjustments
    lab.a += midtoneMask * params.midtonesCyan_Red * 0.5;
    lab.b += midtoneMask * params.midtonesYellow_Blue * 0.5;
    lab.a += midtoneMask * params.midtonesMagenta_Green * 0.25;
    lab.b -= midtoneMask * params.midtonesMagenta_Green * 0.25;

    // Apply highlight adjustments
    lab.a += highlightMask * params.highlightsCyan_Red * 0.5;
    lab.b += highlightMask * params.highlightsYellow_Blue * 0.5;
    lab.a += highlightMask * params.highlightsMagenta_Green * 0.25;
    lab.b -= highlightMask * params.highlightsMagenta_Green * 0.25;

    // Preserve luminosity if requested
    if (params.preserveLuminosity) {
      lab.L = originalL;
    }

    // Clamp
    lab.L = Math.max(0, Math.min(100, lab.L));
    lab.a = Math.max(-128, Math.min(127, lab.a));
    lab.b = Math.max(-128, Math.min(127, lab.b));

    const processedRgb = labToRgb(lab);

    data[i] = processedRgb.r;
    data[i + 1] = processedRgb.g;
    data[i + 2] = processedRgb.b;
  }

  return output;
}

export interface SelectiveColorLABParams {
  targetHue: number; // 0-360 (which hue to affect)
  hueRange: number; // 0-180 (range around target hue)
  hueShift: number; // -180 to 180
  saturationAdjust: number; // -100 to 100
  lightnessAdjust: number; // -100 to 100
}

/**
 * Apply selective color adjustments targeting specific hues
 */
export function applySelectiveColorLAB(
  input: ImageData,
  params: SelectiveColorLABParams,
): ImageData {
  const output = new ImageData(
    new Uint8ClampedArray(input.data),
    input.width,
    input.height,
  );

  const data = output.data;

  for (let i = 0; i < data.length; i += 4) {
    const rgb: RGBColor = {
      r: data[i],
      g: data[i + 1],
      b: data[i + 2],
    };

    const lab = rgbToLab(rgb);

    // Calculate hue from a/b
    let hue = (Math.atan2(lab.b, lab.a) * 180) / Math.PI;
    if (hue < 0) hue += 360;

    // Calculate saturation (chroma)
    const chroma = Math.sqrt(lab.a * lab.a + lab.b * lab.b);

    // Calculate how much this pixel should be affected
    let hueDiff = Math.abs(hue - params.targetHue);
    if (hueDiff > 180) hueDiff = 360 - hueDiff;

    const influence = Math.max(0, 1 - hueDiff / params.hueRange);

    if (influence > 0 && chroma > 5) {
      // Only affect saturated pixels
      // Apply hue shift
      const newHue = hue + params.hueShift * influence;
      const newHueRad = (newHue * Math.PI) / 180;

      // Apply saturation adjustment
      const satFactor = 1 + (params.saturationAdjust / 100) * influence;
      const newChroma = chroma * satFactor;

      // Update a/b
      lab.a = newChroma * Math.cos(newHueRad);
      lab.b = newChroma * Math.sin(newHueRad);

      // Apply lightness adjustment
      lab.L += params.lightnessAdjust * influence * 0.5;
    }

    // Clamp
    lab.L = Math.max(0, Math.min(100, lab.L));
    lab.a = Math.max(-128, Math.min(127, lab.a));
    lab.b = Math.max(-128, Math.min(127, lab.b));

    const processedRgb = labToRgb(lab);

    data[i] = processedRgb.r;
    data[i + 1] = processedRgb.g;
    data[i + 2] = processedRgb.b;
  }

  return output;
}

// =============================================================================
// DEFAULT VALUES
// =============================================================================

export const DEFAULT_HDR_PARAMS: HDRParams = {
  intensity: 1.0,
  shadowIntensity: 0.3,
  highlightIntensity: 0.3,
  gamma: 1.0,
  contrast: 1.0,
  saturationBoost: 1.0,
};

export const DEFAULT_COLOR_BALANCE_LAB_PARAMS: ColorBalanceLABParams = {
  shadowsCyan_Red: 0,
  shadowsMagenta_Green: 0,
  shadowsYellow_Blue: 0,
  midtonesCyan_Red: 0,
  midtonesMagenta_Green: 0,
  midtonesYellow_Blue: 0,
  highlightsCyan_Red: 0,
  highlightsMagenta_Green: 0,
  highlightsYellow_Blue: 0,
  preserveLuminosity: true,
};

export const DEFAULT_SELECTIVE_COLOR_LAB_PARAMS: SelectiveColorLABParams = {
  targetHue: 0,
  hueRange: 30,
  hueShift: 0,
  saturationAdjust: 0,
  lightnessAdjust: 0,
};

// =============================================================================
// EFFECT DEFINITIONS FOR REGISTRATION
// =============================================================================

export const HDR_EFFECT_DEFINITIONS = {
  hdr: {
    name: "HDR",
    category: "color",
    description: "HDR tone mapping with LAB color space processing",
    parameters: [
      {
        name: "Intensity",
        type: "slider",
        min: 0,
        max: 5,
        default: 1,
        step: 0.1,
      },
      {
        name: "Shadow Intensity",
        type: "slider",
        min: 0,
        max: 1,
        default: 0.3,
        step: 0.05,
      },
      {
        name: "Highlight Intensity",
        type: "slider",
        min: 0,
        max: 1,
        default: 0.3,
        step: 0.05,
      },
      {
        name: "Gamma",
        type: "slider",
        min: 0.1,
        max: 3,
        default: 1,
        step: 0.05,
      },
      {
        name: "Contrast",
        type: "slider",
        min: 0,
        max: 2,
        default: 1,
        step: 0.05,
      },
      {
        name: "Saturation Boost",
        type: "slider",
        min: 0,
        max: 2,
        default: 1,
        step: 0.05,
      },
    ],
  },

  "color-balance-lab": {
    name: "Color Balance (LAB)",
    category: "color",
    description: "Color balance adjustments in perceptually uniform LAB space",
    parameters: [
      {
        name: "Shadows Cyan-Red",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      {
        name: "Shadows Magenta-Green",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      {
        name: "Shadows Yellow-Blue",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      {
        name: "Midtones Cyan-Red",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      {
        name: "Midtones Magenta-Green",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      {
        name: "Midtones Yellow-Blue",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      {
        name: "Highlights Cyan-Red",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      {
        name: "Highlights Magenta-Green",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      {
        name: "Highlights Yellow-Blue",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      { name: "Preserve Luminosity", type: "checkbox", default: true },
    ],
  },

  "selective-color-lab": {
    name: "Selective Color (LAB)",
    category: "color",
    description: "Target and adjust specific color ranges in LAB space",
    parameters: [
      {
        name: "Target Hue",
        type: "slider",
        min: 0,
        max: 360,
        default: 0,
        step: 1,
      },
      {
        name: "Hue Range",
        type: "slider",
        min: 0,
        max: 180,
        default: 30,
        step: 1,
      },
      {
        name: "Hue Shift",
        type: "slider",
        min: -180,
        max: 180,
        default: 0,
        step: 1,
      },
      {
        name: "Saturation Adjust",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
      {
        name: "Lightness Adjust",
        type: "slider",
        min: -100,
        max: 100,
        default: 0,
        step: 1,
      },
    ],
  },
};
