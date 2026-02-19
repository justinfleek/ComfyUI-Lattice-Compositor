/**
 * LAB Color Space Utilities
 *
 * Provides CIE LAB, XYZ, and YUV color space conversions
 * for professional color correction and analysis.
 *
 * Uses D65 illuminant (standard for sRGB)
 * LAB L* range: 0-100, a* and b* range: -128 to +127
 */

//                                                                       // d65
const D65_X = 95.047;
const D65_Y = 100.0;
const D65_Z = 108.883;

// sRGB to XYZ conversion matrix (D65)
const SRGB_TO_XYZ_MATRIX = [
  [0.4124564, 0.3575761, 0.1804375],
  [0.2126729, 0.7151522, 0.072175],
  [0.0193339, 0.119192, 0.9503041],
];

//                                                                       // xyz
const XYZ_TO_SRGB_MATRIX = [
  [3.2404542, -1.5371385, -0.4985314],
  [-0.969266, 1.8760108, 0.041556],
  [0.0556434, -0.2040259, 1.0572252],
];

//                                                                        // bt
export const BT709_R = 0.2126;
export const BT709_G = 0.7152;
export const BT709_B = 0.0722;

/**
 * LAB color type
 */
export interface LAB {
  L: number; // 0-100
  a: number; // -128 to +127 (green to red)
  b: number; // -128 to +127 (blue to yellow)
}

/**
 * XYZ color type
 */
export interface XYZ {
  X: number;
  Y: number;
  Z: number;
}

/**
 * YUV color type (for vectorscope)
 */
export interface YUV {
  Y: number; // Luminance (0-1)
  U: number; // Blue-Yellow chrominance (-0.5 to +0.5)
  V: number; // Red-Cyan chrominance (-0.5 to +0.5)
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// sRGB <-> Linear RGB Conversion
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert sRGB component (0-255) to linear RGB (0-1)
 * Applies inverse gamma correction
 */
export function sRGBToLinear(value: number): number {
  const v = value / 255;
  if (v <= 0.04045) {
    return v / 12.92;
  }
  return ((v + 0.055) / 1.055) ** 2.4;
}

/**
 * Convert linear RGB (0-1) to sRGB component (0-255)
 * Applies gamma correction
 */
export function linearToSRGB(value: number): number {
  let v: number;
  if (value <= 0.0031308) {
    v = value * 12.92;
  } else {
    v = 1.055 * value ** (1 / 2.4) - 0.055;
  }
  return Math.round(Math.max(0, Math.min(255, v * 255)));
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                       // rgb
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert RGB (0-255) to XYZ color space
 */
export function rgbToXyz(r: number, g: number, b: number): XYZ {
  // Convert to linear RGB
  const rLinear = sRGBToLinear(r);
  const gLinear = sRGBToLinear(g);
  const bLinear = sRGBToLinear(b);

  // Apply matrix transformation
  const X =
    rLinear * SRGB_TO_XYZ_MATRIX[0][0] +
    gLinear * SRGB_TO_XYZ_MATRIX[0][1] +
    bLinear * SRGB_TO_XYZ_MATRIX[0][2];
  const Y =
    rLinear * SRGB_TO_XYZ_MATRIX[1][0] +
    gLinear * SRGB_TO_XYZ_MATRIX[1][1] +
    bLinear * SRGB_TO_XYZ_MATRIX[1][2];
  const Z =
    rLinear * SRGB_TO_XYZ_MATRIX[2][0] +
    gLinear * SRGB_TO_XYZ_MATRIX[2][1] +
    bLinear * SRGB_TO_XYZ_MATRIX[2][2];

  return { X: X * 100, Y: Y * 100, Z: Z * 100 };
}

/**
 * Convert XYZ to RGB (0-255)
 */
export function xyzToRgb(
  X: number,
  Y: number,
  Z: number,
): [number, number, number] {
  // Normalize XYZ values
  const x = X / 100;
  const y = Y / 100;
  const z = Z / 100;

  // Apply matrix transformation to get linear RGB
  const rLinear =
    x * XYZ_TO_SRGB_MATRIX[0][0] +
    y * XYZ_TO_SRGB_MATRIX[0][1] +
    z * XYZ_TO_SRGB_MATRIX[0][2];
  const gLinear =
    x * XYZ_TO_SRGB_MATRIX[1][0] +
    y * XYZ_TO_SRGB_MATRIX[1][1] +
    z * XYZ_TO_SRGB_MATRIX[1][2];
  const bLinear =
    x * XYZ_TO_SRGB_MATRIX[2][0] +
    y * XYZ_TO_SRGB_MATRIX[2][1] +
    z * XYZ_TO_SRGB_MATRIX[2][2];

  return [linearToSRGB(rLinear), linearToSRGB(gLinear), linearToSRGB(bLinear)];
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                       // xyz
// ════════════════════════════════════════════════════════════════════════════

/**
 * Lab f(t) function for XYZ to LAB conversion
 */
function labF(t: number): number {
  const delta = 6 / 29;
  const delta3 = delta * delta * delta;

  if (t > delta3) {
    return t ** (1 / 3);
  }
  return t / (3 * delta * delta) + 4 / 29;
}

/**
 * Inverse Lab f(t) function for LAB to XYZ conversion
 */
function labFInverse(t: number): number {
  const delta = 6 / 29;

  if (t > delta) {
    return t * t * t;
  }
  return 3 * delta * delta * (t - 4 / 29);
}

/**
 * Convert XYZ to CIE LAB
 */
export function xyzToLab(X: number, Y: number, Z: number): LAB {
  const xn = X / D65_X;
  const yn = Y / D65_Y;
  const zn = Z / D65_Z;

  const fx = labF(xn);
  const fy = labF(yn);
  const fz = labF(zn);

  return {
    L: 116 * fy - 16,
    a: 500 * (fx - fy),
    b: 200 * (fy - fz),
  };
}

/**
 * Convert CIE LAB to XYZ
 */
export function labToXyz(L: number, a: number, b: number): XYZ {
  const fy = (L + 16) / 116;
  const fx = a / 500 + fy;
  const fz = fy - b / 200;

  return {
    X: D65_X * labFInverse(fx),
    Y: D65_Y * labFInverse(fy),
    Z: D65_Z * labFInverse(fz),
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                       // rgb
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert RGB (0-255) directly to CIE LAB
 */
export function rgbToLab(r: number, g: number, b: number): LAB {
  const xyz = rgbToXyz(r, g, b);
  return xyzToLab(xyz.X, xyz.Y, xyz.Z);
}

/**
 * Convert CIE LAB directly to RGB (0-255)
 */
export function labToRgb(
  L: number,
  a: number,
  b: number,
): [number, number, number] {
  const xyz = labToXyz(L, a, b);
  return xyzToRgb(xyz.X, xyz.Y, xyz.Z);
}

// ════════════════════════════════════════════════════════════════════════════
// Color Difference (Delta E)
// ════════════════════════════════════════════════════════════════════════════

/**
 * Calculate Delta E (CIE76) - basic Euclidean distance in LAB space
 * Values interpretation:
 * - 0-1: Not perceptible by human eyes
 * - 1-2: Perceptible through close observation
 * - 2-10: Perceptible at a glance
 * - 11-49: Colors are more similar than opposite
 * - 100: Colors are exact opposite
 */
export function deltaE76(lab1: LAB, lab2: LAB): number {
  const dL = lab1.L - lab2.L;
  const da = lab1.a - lab2.a;
  const db = lab1.b - lab2.b;

  return Math.sqrt(dL * dL + da * da + db * db);
}

/**
 * Calculate Delta E (CIE94) - weighted formula for graphics applications
 * More perceptually uniform than CIE76
 */
export function deltaE94(lab1: LAB, lab2: LAB): number {
  // Weighting factors for graphic arts
  const kL = 1;
  const kC = 1;
  const kH = 1;
  const K1 = 0.045;
  const K2 = 0.015;

  const dL = lab1.L - lab2.L;
  const C1 = Math.sqrt(lab1.a * lab1.a + lab1.b * lab1.b);
  const C2 = Math.sqrt(lab2.a * lab2.a + lab2.b * lab2.b);
  const dC = C1 - C2;
  const da = lab1.a - lab2.a;
  const db = lab1.b - lab2.b;
  const dH2 = da * da + db * db - dC * dC;
  const dH = dH2 > 0 ? Math.sqrt(dH2) : 0;

  const SL = 1;
  const SC = 1 + K1 * C1;
  const SH = 1 + K2 * C1;

  const term1 = dL / (kL * SL);
  const term2 = dC / (kC * SC);
  const term3 = dH / (kH * SH);

  return Math.sqrt(term1 * term1 + term2 * term2 + term3 * term3);
}

/**
 * Calculate Delta E (CIEDE2000) - most accurate formula
 * Best for critical color matching applications
 */
export function deltaE2000(lab1: LAB, lab2: LAB): number {
  const L1 = lab1.L,
    a1 = lab1.a,
    b1 = lab1.b;
  const L2 = lab2.L,
    a2 = lab2.a,
    b2 = lab2.b;

  // Step 1: Calculate C'i and h'i
  const C1 = Math.sqrt(a1 * a1 + b1 * b1);
  const C2 = Math.sqrt(a2 * a2 + b2 * b2);
  const Cb = (C1 + C2) / 2;

  const G = 0.5 * (1 - Math.sqrt(Cb ** 7 / (Cb ** 7 + 25 ** 7)));

  const a1p = a1 * (1 + G);
  const a2p = a2 * (1 + G);

  const C1p = Math.sqrt(a1p * a1p + b1 * b1);
  const C2p = Math.sqrt(a2p * a2p + b2 * b2);

  const h1p = (Math.atan2(b1, a1p) * 180) / Math.PI;
  const h1pAdj = h1p >= 0 ? h1p : h1p + 360;
  const h2p = (Math.atan2(b2, a2p) * 180) / Math.PI;
  const h2pAdj = h2p >= 0 ? h2p : h2p + 360;

  // Step 2: Calculate dL', dC', dH'
  const dLp = L2 - L1;
  const dCp = C2p - C1p;

  let dhp: number;
  if (C1p * C2p === 0) {
    dhp = 0;
  } else if (Math.abs(h2pAdj - h1pAdj) <= 180) {
    dhp = h2pAdj - h1pAdj;
  } else if (h2pAdj - h1pAdj > 180) {
    dhp = h2pAdj - h1pAdj - 360;
  } else {
    dhp = h2pAdj - h1pAdj + 360;
  }

  const dHp = 2 * Math.sqrt(C1p * C2p) * Math.sin((dhp * Math.PI) / 360);

  // Step 3: Calculate CIEDE2000
  const Lbp = (L1 + L2) / 2;
  const Cbp = (C1p + C2p) / 2;

  let Hbp: number;
  if (C1p * C2p === 0) {
    Hbp = h1pAdj + h2pAdj;
  } else if (Math.abs(h1pAdj - h2pAdj) <= 180) {
    Hbp = (h1pAdj + h2pAdj) / 2;
  } else if (h1pAdj + h2pAdj < 360) {
    Hbp = (h1pAdj + h2pAdj + 360) / 2;
  } else {
    Hbp = (h1pAdj + h2pAdj - 360) / 2;
  }

  const T =
    1 -
    0.17 * Math.cos(((Hbp - 30) * Math.PI) / 180) +
    0.24 * Math.cos((2 * Hbp * Math.PI) / 180) +
    0.32 * Math.cos(((3 * Hbp + 6) * Math.PI) / 180) -
    0.2 * Math.cos(((4 * Hbp - 63) * Math.PI) / 180);

  const dTheta = 30 * Math.exp(-(((Hbp - 275) / 25) ** 2));
  const RC = 2 * Math.sqrt(Cbp ** 7 / (Cbp ** 7 + 25 ** 7));

  const SL = 1 + (0.015 * (Lbp - 50) ** 2) / Math.sqrt(20 + (Lbp - 50) ** 2);
  const SC = 1 + 0.045 * Cbp;
  const SH = 1 + 0.015 * Cbp * T;
  const RT = -Math.sin((2 * dTheta * Math.PI) / 180) * RC;

  const kL = 1,
    kC = 1,
    kH = 1;

  return Math.sqrt(
    (dLp / (kL * SL)) ** 2 +
      (dCp / (kC * SC)) ** 2 +
      (dHp / (kH * SH)) ** 2 +
      RT * (dCp / (kC * SC)) * (dHp / (kH * SH)),
  );
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                       // rgb
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert RGB (0-255) to YUV (BT.709)
 * Used for vectorscope display
 */
export function rgbToYuv(r: number, g: number, b: number): YUV {
  const rn = r / 255;
  const gn = g / 255;
  const bn = b / 255;

  //                                                                        // bt
  const Y = BT709_R * rn + BT709_G * gn + BT709_B * bn;
  const U = (0.5 * (bn - Y)) / (1 - BT709_B);
  const V = (0.5 * (rn - Y)) / (1 - BT709_R);

  return { Y, U, V };
}

/**
 * Convert YUV to RGB (0-255)
 */
export function yuvToRgb(
  Y: number,
  U: number,
  V: number,
): [number, number, number] {
  const r = Y + 2 * V * (1 - BT709_R);
  const g =
    Y -
    (2 * U * BT709_B * (1 - BT709_B)) / BT709_G -
    (2 * V * BT709_R * (1 - BT709_R)) / BT709_G;
  const b = Y + 2 * U * (1 - BT709_B);

  return [
    Math.round(Math.max(0, Math.min(255, r * 255))),
    Math.round(Math.max(0, Math.min(255, g * 255))),
    Math.round(Math.max(0, Math.min(255, b * 255))),
  ];
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                       // rgb
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert RGB (0-255) to HSL
 * H: 0-360, S: 0-1, L: 0-1
 */
export function rgbToHsl(
  r: number,
  g: number,
  b: number,
): [number, number, number] {
  const rn = r / 255;
  const gn = g / 255;
  const bn = b / 255;

  const max = Math.max(rn, gn, bn);
  const min = Math.min(rn, gn, bn);
  const l = (max + min) / 2;

  if (max === min) {
    return [0, 0, l]; // achromatic
  }

  const d = max - min;
  const s = l > 0.5 ? d / (2 - max - min) : d / (max + min);

  let h: number;
  switch (max) {
    case rn:
      h = ((gn - bn) / d + (gn < bn ? 6 : 0)) / 6;
      break;
    case gn:
      h = ((bn - rn) / d + 2) / 6;
      break;
    default:
      h = ((rn - gn) / d + 4) / 6;
      break;
  }

  return [h * 360, s, l];
}

/**
 * Convert HSL to RGB (0-255)
 * H: 0-360, S: 0-1, L: 0-1
 */
export function hslToRgb(
  h: number,
  s: number,
  l: number,
): [number, number, number] {
  h = ((h % 360) + 360) % 360; // Normalize hue
  h /= 360;

  if (s === 0) {
    const v = Math.round(l * 255);
    return [v, v, v];
  }

  const hue2rgb = (p: number, q: number, t: number): number => {
    if (t < 0) t += 1;
    if (t > 1) t -= 1;
    if (t < 1 / 6) return p + (q - p) * 6 * t;
    if (t < 1 / 2) return q;
    if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
    return p;
  };

  const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
  const p = 2 * l - q;

  return [
    Math.round(hue2rgb(p, q, h + 1 / 3) * 255),
    Math.round(hue2rgb(p, q, h) * 255),
    Math.round(hue2rgb(p, q, h - 1 / 3) * 255),
  ];
}

// ════════════════════════════════════════════════════════════════════════════
// Utility Functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Calculate luminance (BT.709) from RGB (0-255)
 * Returns 0-255
 */
export function rgbToLuminance(r: number, g: number, b: number): number {
  return Math.round(BT709_R * r + BT709_G * g + BT709_B * b);
}

/**
 * Check if a color is within a tolerance of neutral gray
 * Uses LAB a* and b* components
 */
export function isNeutral(
  r: number,
  g: number,
  b: number,
  tolerance: number = 5,
): boolean {
  const lab = rgbToLab(r, g, b);
  return Math.abs(lab.a) < tolerance && Math.abs(lab.b) < tolerance;
}

/**
 * Get the complementary color
 */
export function complementary(
  r: number,
  g: number,
  b: number,
): [number, number, number] {
  const [h, s, l] = rgbToHsl(r, g, b);
  return hslToRgb((h + 180) % 360, s, l);
}

/**
 * Clamp a value between min and max
 */
export function clamp(value: number, min: number, max: number): number {
  return Math.max(min, Math.min(max, value));
}

/**
 * Linear interpolation between two values
 */
export function lerp(a: number, b: number, t: number): number {
  return a + (b - a) * t;
}

/**
 * Smoothstep function for smooth transitions
 */
export function smoothstep(edge0: number, edge1: number, x: number): number {
  const t = clamp((x - edge0) / (edge1 - edge0), 0, 1);
  return t * t * (3 - 2 * t);
}
