export const clearAppElement = () => {
  const app = document.getElementById('app');
  if (app) {
    app.innerHTML = '';
  }
};

// ═══════════════════════════════════════════════════════════════════════════════
// WCAG 2.1 Contrast Calculation - Proper Implementation
// https://www.w3.org/TR/WCAG21/#dfn-contrast-ratio
// ═══════════════════════════════════════════════════════════════════════════════

// Parse hex color to RGB object
const hexToRgb = (hex) => {
  // Remove # if present
  const h = hex.replace(/^#/, '');
  // Handle 3-char hex
  const fullHex = h.length === 3 
    ? h.split('').map(c => c + c).join('') 
    : h;
  const num = parseInt(fullHex, 16);
  return {
    r: (num >> 16) & 255,
    g: (num >> 8) & 255,
    b: num & 255
  };
};

// Linearize sRGB channel value (0-255) to linear RGB (0-1)
// Per WCAG 2.1: https://www.w3.org/TR/WCAG21/#dfn-relative-luminance
const linearize = (channel) => {
  const srgb = channel / 255;
  return srgb <= 0.03928
    ? srgb / 12.92
    : Math.pow((srgb + 0.055) / 1.055, 2.4);
};

// Calculate relative luminance
// L = 0.2126 * R + 0.7152 * G + 0.0722 * B
const relativeLuminance = (hex) => {
  const { r, g, b } = hexToRgb(hex);
  return 0.2126 * linearize(r) + 0.7152 * linearize(g) + 0.0722 * linearize(b);
};

// Calculate WCAG contrast ratio between two colors
// Returns a value between 1 and 21
export const calculateContrastRatioFFI = (color1) => (color2) => {
  const l1 = relativeLuminance(color1);
  const l2 = relativeLuminance(color2);
  const lighter = Math.max(l1, l2);
  const darker = Math.min(l1, l2);
  const ratio = (lighter + 0.05) / (darker + 0.05);
  console.log('[WCAG] Calculating contrast:', color1, 'vs', color2, '=', ratio.toFixed(2));
  return ratio;
};

// Format contrast ratio to string with 2 decimal places
export const formatContrastRatioFFI = (ratio) => {
  return ratio.toFixed(2) + ':1';
};

// Truncate number to integer
export const truncateFFI = (n) => Math.trunc(n);

// Convert int to number
export const intToNumberFFI = (n) => n;
