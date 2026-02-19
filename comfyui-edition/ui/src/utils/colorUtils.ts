/**
 * Color Utility Functions
 * HSV, RGB, HSL conversions and hex parsing
 */

import { clamp } from "./arrayUtils";

export type RGB = [number, number, number];
export type HSV = [number, number, number];
export type HSL = [number, number, number];
export type RGBA = [number, number, number, number];

/**
 * Convert HSV to RGB
 * @param h Hue (0-360)
 * @param s Saturation (0-1)
 * @param v Value (0-1)
 * @returns RGB tuple (0-255 each)
 */
export function hsvToRgb(h: number, s: number, v: number): RGB {
  h = ((h % 360) + 360) % 360;
  const c = v * s;
  const x = c * (1 - Math.abs(((h / 60) % 2) - 1));
  const m = v - c;

  let r = 0,
    g = 0,
    b = 0;
  if (h < 60) {
    r = c;
    g = x;
    b = 0;
  } else if (h < 120) {
    r = x;
    g = c;
    b = 0;
  } else if (h < 180) {
    r = 0;
    g = c;
    b = x;
  } else if (h < 240) {
    r = 0;
    g = x;
    b = c;
  } else if (h < 300) {
    r = x;
    g = 0;
    b = c;
  } else {
    r = c;
    g = 0;
    b = x;
  }

  return [
    Math.round((r + m) * 255),
    Math.round((g + m) * 255),
    Math.round((b + m) * 255),
  ];
}

/**
 * Convert RGB to HSV
 * @param r Red (0-255)
 * @param g Green (0-255)
 * @param b Blue (0-255)
 * @returns HSV tuple [hue (0-360), saturation (0-1), value (0-1)]
 */
export function rgbToHsv(r: number, g: number, b: number): HSV {
  r /= 255;
  g /= 255;
  b /= 255;

  const max = Math.max(r, g, b);
  const min = Math.min(r, g, b);
  const d = max - min;

  let h = 0;
  const s = max === 0 ? 0 : d / max;
  const v = max;

  if (d !== 0) {
    switch (max) {
      case r:
        h = ((g - b) / d + (g < b ? 6 : 0)) * 60;
        break;
      case g:
        h = ((b - r) / d + 2) * 60;
        break;
      case b:
        h = ((r - g) / d + 4) * 60;
        break;
    }
  }

  return [h, s, v];
}

/**
 * Convert HSL to RGB
 * @param h Hue (0-360)
 * @param s Saturation (0-1)
 * @param l Lightness (0-1)
 * @returns RGB tuple (0-255 each)
 */
export function hslToRgb(h: number, s: number, l: number): RGB {
  h = ((h % 360) + 360) % 360;
  const c = (1 - Math.abs(2 * l - 1)) * s;
  const x = c * (1 - Math.abs(((h / 60) % 2) - 1));
  const m = l - c / 2;

  let r = 0,
    g = 0,
    b = 0;
  if (h < 60) {
    r = c;
    g = x;
    b = 0;
  } else if (h < 120) {
    r = x;
    g = c;
    b = 0;
  } else if (h < 180) {
    r = 0;
    g = c;
    b = x;
  } else if (h < 240) {
    r = 0;
    g = x;
    b = c;
  } else if (h < 300) {
    r = x;
    g = 0;
    b = c;
  } else {
    r = c;
    g = 0;
    b = x;
  }

  return [
    Math.round((r + m) * 255),
    Math.round((g + m) * 255),
    Math.round((b + m) * 255),
  ];
}

/**
 * Convert RGB to HSL
 * @param r Red (0-255)
 * @param g Green (0-255)
 * @param b Blue (0-255)
 * @returns HSL tuple [hue (0-360), saturation (0-1), lightness (0-1)]
 */
export function rgbToHsl(r: number, g: number, b: number): HSL {
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
        h = ((g - b) / d + (g < b ? 6 : 0)) * 60;
        break;
      case g:
        h = ((b - r) / d + 2) * 60;
        break;
      case b:
        h = ((r - g) / d + 4) * 60;
        break;
    }
  }

  return [h, s, l];
}

/**
 * Convert hex color to RGB
 * 
 * System F/Omega proof: Explicit validation of hex string format
 * Type proof: hex ∈ string → RGB (non-nullable)
 * Mathematical proof: Hex string must be valid 3, 6, or 8 character format to parse RGB values
 * 
 * @param hex Hex color string (#RGB, #RRGGBB, or #RRGGBBAA)
 * @returns RGB tuple (throws error if invalid - wrap in try/catch for expected "invalid hex" case)
 */
export function hexToRgb(hex: string): RGB {
  hex = hex.replace(/^#/, "");

  // Handle short format #RGB
  if (hex.length === 3) {
    hex = hex[0] + hex[0] + hex[1] + hex[1] + hex[2] + hex[2];
  }

  // Handle #RRGGBB or #RRGGBBAA
  if (hex.length === 6 || hex.length === 8) {
    const r = parseInt(hex.slice(0, 2), 16);
    const g = parseInt(hex.slice(2, 4), 16);
    const b = parseInt(hex.slice(4, 6), 16);

    if (!Number.isNaN(r) && !Number.isNaN(g) && !Number.isNaN(b)) {
      return [r, g, b];
    }
  }

  // System F/Omega proof: Explicit validation of hex string format
  // Type proof: hex ∈ string → [number, number, number] (non-nullable)
  // Mathematical proof: Hex string must be valid 3, 6, or 8 character format to parse RGB values
  throw new Error(
    `[colorUtils] Cannot convert hex to RGB: Invalid hex string format. ` +
    `Hex string: "${hex}", length: ${hex.length}, expected: 3, 6, or 8 characters (after # removal). ` +
    `Hex string must match format #RGB, #RRGGBB, or #RRGGBBAA. ` +
    `Wrap in try/catch if "invalid hex" is an expected state.`
  );
}

/**
 * Convert hex color to RGBA
 * 
 * System F/Omega proof: Explicit validation of hex string format
 * Type proof: hex ∈ string → RGBA (non-nullable)
 * Mathematical proof: Hex string must be valid 3, 6, or 8 character format to parse RGBA values
 * 
 * @param hex Hex color string (#RGB, #RRGGBB, or #RRGGBBAA)
 * @returns RGBA tuple (throws error if invalid - wrap in try/catch for expected "invalid hex" case)
 */
export function hexToRgba(hex: string): RGBA {
  hex = hex.replace(/^#/, "");

  // Handle short format #RGB
  if (hex.length === 3) {
    hex = `${hex[0] + hex[0] + hex[1] + hex[1] + hex[2] + hex[2]}ff`;
  }

  // Handle #RRGGBB (add alpha)
  if (hex.length === 6) {
    hex = `${hex}ff`;
  }

  if (hex.length === 8) {
    const r = parseInt(hex.slice(0, 2), 16);
    const g = parseInt(hex.slice(2, 4), 16);
    const b = parseInt(hex.slice(4, 6), 16);
    const a = parseInt(hex.slice(6, 8), 16) / 255;

    if (
      !Number.isNaN(r) &&
      !Number.isNaN(g) &&
      !Number.isNaN(b) &&
      !Number.isNaN(a)
    ) {
      return [r, g, b, a];
    }
  }

  // System F/Omega proof: Explicit validation of hex string format
  // Type proof: hex ∈ string → [number, number, number, number] (non-nullable)
  // Mathematical proof: Hex string must be valid 8 character format to parse RGBA values
  throw new Error(
    `[colorUtils] Cannot convert hex to RGBA: Invalid hex string format. ` +
    `Hex string: "${hex}", length: ${hex.length}, expected: 8 characters (after # removal). ` +
    `Hex string must match format #RRGGBBAA. ` +
    `Wrap in try/catch if "invalid hex" is an expected state.`
  );
}

/**
 * Convert RGB to hex color string
 * @param r Red (0-255)
 * @param g Green (0-255)
 * @param b Blue (0-255)
 * @returns Hex color string (#RRGGBB)
 */
export function rgbToHex(r: number, g: number, b: number): string {
  const toHex = (n: number) =>
    Math.max(0, Math.min(255, Math.round(n)))
      .toString(16)
      .padStart(2, "0");
  return `#${toHex(r)}${toHex(g)}${toHex(b)}`;
}

/**
 * Convert RGBA to hex color string with alpha
 * @param r Red (0-255)
 * @param g Green (0-255)
 * @param b Blue (0-255)
 * @param a Alpha (0-1)
 * @returns Hex color string (#RRGGBBAA)
 */
export function rgbaToHex(r: number, g: number, b: number, a: number): string {
  const toHex = (n: number) =>
    Math.max(0, Math.min(255, Math.round(n)))
      .toString(16)
      .padStart(2, "0");
  return `#${toHex(r)}${toHex(g)}${toHex(b)}${toHex(a * 255)}`;
}

/**
 * Convert HSV to hex color string
 */
export function hsvToHex(h: number, s: number, v: number): string {
  const [r, g, b] = hsvToRgb(h, s, v);
  return rgbToHex(r, g, b);
}

/**
 * Convert hex to HSV
 * 
 * System F/Omega proof: Explicit validation of hex string via hexToRgb dependency
 * Type proof: hex ∈ string → HSV (non-nullable)
 * Mathematical proof: Hex string must be valid to convert to RGB, then to HSV
 */
export function hexToHsv(hex: string): HSV {
  // System F/Omega pattern: hexToRgb throws error for invalid hex - propagate
  const rgb = hexToRgb(hex);
  return rgbToHsv(rgb[0], rgb[1], rgb[2]);
}

/**
 * Parse any color string to RGB
 * Supports: hex, rgb(), rgba(), hsl(), hsla()
 * 
 * System F/Omega proof: Explicit validation of color string format
 * Type proof: color ∈ string → RGB (non-nullable)
 * Mathematical proof: Color string must match hex, rgb/rgba, or hsl/hsla format
 */
export function parseColor(color: string): RGB {
  color = color.trim().toLowerCase();

  // Hex
  if (color.startsWith("#")) {
    return hexToRgb(color);
  }

  // rgb() or rgba()
  const rgbMatch = color.match(/rgba?\s*\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)/);
  if (rgbMatch) {
    return [
      parseInt(rgbMatch[1], 10),
      parseInt(rgbMatch[2], 10),
      parseInt(rgbMatch[3], 10),
    ];
  }

  // hsl() or hsla()
  const hslMatch = color.match(
    /hsla?\s*\(\s*(\d+)\s*,\s*(\d+)%?\s*,\s*(\d+)%?/,
  );
  if (hslMatch) {
    return hslToRgb(
      parseInt(hslMatch[1], 10),
      parseInt(hslMatch[2], 10) / 100,
      parseInt(hslMatch[3], 10) / 100,
    );
  }

  // System F/Omega proof: Explicit validation of color string format
  // Type proof: color ∈ string → [number, number, number] (non-nullable)
  // Mathematical proof: Color string must match hex, rgb/rgba, or hsl/hsla format
  throw new Error(
    `[colorUtils] Cannot parse color string: Invalid format. ` +
    `Color string: "${color}", expected formats: #RGB, #RRGGBB, rgb(r,g,b), rgba(r,g,b,a), hsl(h,s%,l%), hsla(h,s%,l%,a). ` +
    `Color string must match one of the supported CSS color formats. ` +
    `Wrap in try/catch if "invalid color" is an expected state.`
  );
}

/**
 * Linear interpolation between two colors
 */
export function lerpColor(color1: string, color2: string, t: number): string {
  const rgb1 = hexToRgb(color1);
  const rgb2 = hexToRgb(color2);

  if (!rgb1 || !rgb2) return color1;

  t = clamp(t, 0, 1);

  return rgbToHex(
    Math.round(rgb1[0] + (rgb2[0] - rgb1[0]) * t),
    Math.round(rgb1[1] + (rgb2[1] - rgb1[1]) * t),
    Math.round(rgb1[2] + (rgb2[2] - rgb1[2]) * t),
  );
}

/**
 * Get contrasting text color (black or white) for a background
 */
export function getContrastColor(bgColor: string): string {
  const rgb = hexToRgb(bgColor);
  if (!rgb) return "#ffffff";

  // Calculate luminance
  const luminance = (0.299 * rgb[0] + 0.587 * rgb[1] + 0.114 * rgb[2]) / 255;
  return luminance > 0.5 ? "#000000" : "#ffffff";
}

/**
 * Standard color swatches
 */
export const STANDARD_SWATCHES = [
  "#ff0000",
  "#ff8000",
  "#ffff00",
  "#80ff00",
  "#00ff00",
  "#00ff80",
  "#00ffff",
  "#0080ff",
  "#0000ff",
  "#8000ff",
  "#ff00ff",
  "#ff0080",
  "#ffffff",
  "#c0c0c0",
  "#808080",
  "#404040",
  "#000000",
];
