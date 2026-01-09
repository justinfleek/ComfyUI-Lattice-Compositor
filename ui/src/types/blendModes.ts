// ============================================================
// BLEND MODES - Industry standard compatibility
// ============================================================
// Extracted from project.ts for better modularity
// ============================================================

/**
 * Blend Modes - Industry standard compatibility
 * Organized by category matching professional animation software groupings
 */
export type BlendMode =
  // Normal
  | "normal"
  | "dissolve"
  // Darken
  | "darken"
  | "multiply"
  | "color-burn"
  | "linear-burn"
  | "darker-color"
  // Lighten
  | "lighten"
  | "screen"
  | "color-dodge"
  | "linear-dodge"
  | "lighter-color"
  | "add"
  // Contrast
  | "overlay"
  | "soft-light"
  | "hard-light"
  | "vivid-light"
  | "linear-light"
  | "pin-light"
  | "hard-mix"
  // Inversion
  | "difference"
  | "exclusion"
  | "subtract"
  | "divide"
  // Component (HSL)
  | "hue"
  | "saturation"
  | "color"
  | "luminosity"
  // Utility/Advanced modes
  | "stencil-alpha"
  | "stencil-luma"
  | "silhouette-alpha"
  | "silhouette-luma"
  | "alpha-add"
  | "luminescent-premul"
  // Classic blend modes (legacy compatibility)
  | "classic-color-burn"
  | "classic-color-dodge";

/**
 * Blend mode categories for UI organization
 */
export const BLEND_MODE_CATEGORIES = {
  normal: ["normal", "dissolve"],
  darken: ["darken", "multiply", "color-burn", "linear-burn", "darker-color"],
  lighten: [
    "lighten",
    "screen",
    "color-dodge",
    "linear-dodge",
    "lighter-color",
    "add",
  ],
  contrast: [
    "overlay",
    "soft-light",
    "hard-light",
    "vivid-light",
    "linear-light",
    "pin-light",
    "hard-mix",
  ],
  inversion: ["difference", "exclusion", "subtract", "divide"],
  component: ["hue", "saturation", "color", "luminosity"],
  utility: [
    "stencil-alpha",
    "stencil-luma",
    "silhouette-alpha",
    "silhouette-luma",
    "alpha-add",
    "luminescent-premul",
  ],
} as const;

/**
 * Get blend mode category
 */
export function getBlendModeCategory(
  mode: BlendMode,
): keyof typeof BLEND_MODE_CATEGORIES {
  for (const [category, modes] of Object.entries(BLEND_MODE_CATEGORIES)) {
    if ((modes as readonly string[]).includes(mode)) {
      return category as keyof typeof BLEND_MODE_CATEGORIES;
    }
  }
  return "normal";
}

/**
 * Get all blend modes in a category
 */
export function getBlendModesInCategory(
  category: keyof typeof BLEND_MODE_CATEGORIES,
): BlendMode[] {
  return [...BLEND_MODE_CATEGORIES[category]] as BlendMode[];
}

/**
 * Get all blend modes
 */
export function getAllBlendModes(): BlendMode[] {
  return Object.values(BLEND_MODE_CATEGORIES).flat() as BlendMode[];
}
