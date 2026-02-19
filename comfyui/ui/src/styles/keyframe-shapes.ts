/**
 * Semantic Keyframe Shape System
 *
 * Based on reference UI showing 16 distinct keyframe shapes.
 * Each shape has semantic meaning indicating the type of interpolation.
 *
 * Reference: original-5d0a56a0844a97b4f6b1703890289d40.webp (bottom row)
 */

export interface KeyframeShapeDefinition {
  /** SVG path data */
  path: string;
  /** Width in pixels */
  width: number;
  /** Height in pixels */
  height: number;
  /** Optional fill color override */
  fill?: string;
  /** Whether shape should be stroked instead of filled */
  stroke?: boolean;
}

/**
 * All keyframe shape definitions
 * Centered at (width/2, height/2), designed for 24px height
 */
export const KEYFRAME_SHAPES: Record<string, KeyframeShapeDefinition> = {
  // ========================================
  // BAR SHAPES (for holds/markers)
  // ========================================

  /** Mini - Short vertical bar for subtle keyframes */
  mini: {
    path: "M1,8 L1,16",
    width: 2,
    height: 24,
    stroke: true,
  },

  /** Extend - Taller bar for extended holds */
  extend: {
    path: "M2,4 L2,20",
    width: 4,
    height: 24,
    stroke: true,
  },

  /** Long - Full height bar for long duration markers */
  long: {
    path: "M2,0 L2,24",
    width: 4,
    height: 24,
    stroke: true,
  },

  // ========================================
  // ROUND HEAD SHAPES (for smooth starts)
  // ========================================

  /** Round Head - Circle top for smooth interpolation start */
  roundHead: {
    path: "M4,4 a4,4 0 1,1 0.01,0 M4,8 L4,20",
    width: 8,
    height: 24,
    stroke: true,
  },

  /** RH Extend - Circle with extended bar */
  rhExtend: {
    path: "M4,4 a4,4 0 1,1 0.01,0 M4,8 L4,16 L8,16 L8,20 L0,20 L0,16 L4,16",
    width: 8,
    height: 24,
    stroke: true,
  },

  /** RH Long - Circle with long bar */
  rhLong: {
    path: "M4,4 a4,4 0 1,1 0.01,0 M4,8 L4,24",
    width: 8,
    height: 24,
    stroke: true,
  },

  /** RH Outline - Outline circle variant */
  rhOutline: {
    path: "M4,4 a4,4 0 1,1 0.01,0 M4,8 L4,24",
    width: 8,
    height: 24,
    stroke: true,
    fill: "none",
  },

  // ========================================
  // WIDE SHAPES (for timing windows)
  // ========================================

  /** Wide - Horizontal bar for wide timing window */
  wide: {
    path: "M0,10 L12,10 L12,14 L0,14 Z",
    width: 12,
    height: 24,
  },

  /** Wide Hammer - Bar with hard stop end */
  wideHammer: {
    path: "M0,10 L10,10 L10,6 L12,6 L12,18 L10,18 L10,14 L0,14 Z",
    width: 12,
    height: 24,
  },

  // ========================================
  // EASE SHAPES (for interpolation types)
  // ========================================

  /** Pill - Rounded rectangle for eased transitions */
  pill: {
    path: "M3,8 L9,8 A3,3 0 0,1 9,16 L3,16 A3,3 0 0,1 3,8 Z",
    width: 12,
    height: 24,
  },

  /** Watch - Hourglass shape for ease in-out */
  watch: {
    path: "M2,6 L10,6 L10,8 L7,12 L10,16 L10,18 L2,18 L2,16 L5,12 L2,8 Z",
    width: 12,
    height: 24,
  },

  /** Triangle - Directional ramp (ease in or out) */
  triangle: {
    path: "M0,20 L6,4 L12,20 Z",
    width: 12,
    height: 24,
  },

  /** Diamond - Standard keyframe (linear) */
  diamond: {
    path: "M6,2 L11,12 L6,22 L1,12 Z",
    width: 12,
    height: 24,
  },

  /** Martini - Inverted triangle (ease out with hold) */
  martini: {
    path: "M1,4 L11,4 L6,18 L6,22 L6,18 Z",
    width: 12,
    height: 24,
  },

  // ========================================
  // POINT SHAPES (for discrete keyframes)
  // ========================================

  /** Radio - Filled circle point */
  radio: {
    path: "M6,6 a6,6 0 1,1 0.01,0 Z",
    width: 12,
    height: 24,
  },

  /** Radio Long - Circle with extension bar */
  radioLong: {
    path: "M6,6 a6,6 0 1,1 0.01,0 Z M6,12 L6,24",
    width: 12,
    height: 24,
  },
};

/**
 * Map easing types to keyframe shapes
 */
export function getShapeForEasing(
  easing: string,
): keyof typeof KEYFRAME_SHAPES {
  const easingLower = easing.toLowerCase();

  // Hold/Step
  if (easingLower === "hold" || easingLower === "step") {
    return "extend";
  }

  // Linear
  if (easingLower === "linear") {
    return "diamond";
  }

  // Ease In variants
  if (easingLower.startsWith("easein") && !easingLower.includes("out")) {
    return "triangle";
  }

  // Ease Out variants
  if (easingLower.startsWith("easeout") || easingLower === "easeout") {
    return "martini";
  }

  // Ease In-Out variants (including all the cubic, quart, etc.)
  if (easingLower.includes("inout") || easingLower === "easeinout") {
    return "pill";
  }

  // Bezier (custom curves)
  if (easingLower === "bezier" || easingLower === "cubic-bezier") {
    return "watch";
  }

  // Elastic
  if (easingLower.includes("elastic")) {
    return "radioLong";
  }

  // Bounce
  if (easingLower.includes("bounce")) {
    return "radio";
  }

  // Spring
  if (easingLower.includes("spring")) {
    return "roundHead";
  }

  // Default to diamond
  return "diamond";
}

/**
 * Get SVG element for a keyframe shape
 */
export function createKeyframeSVG(
  shape: keyof typeof KEYFRAME_SHAPES,
  color: string = "#8B5CF6",
  scale: number = 1,
): string {
  const def = KEYFRAME_SHAPES[shape];
  if (!def) return "";

  const width = def.width * scale;
  const height = def.height * scale;
  const transform = scale !== 1 ? `transform="scale(${scale})"` : "";

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  const fill = (def.fill !== null && def.fill !== undefined && typeof def.fill === "string" && def.fill.length > 0) ? def.fill : color;
  const stroke = def.stroke
    ? `stroke="${color}" stroke-width="2" fill="none"`
    : `fill="${fill}"`;

  return `
    <svg width="${width}" height="${height}" viewBox="0 0 ${def.width} ${def.height}">
      <path d="${def.path}" ${stroke} ${transform} />
    </svg>
  `.trim();
}

/**
 * Keyframe shape legend (for UI display)
 */
export const KEYFRAME_SHAPE_LEGEND: Array<{
  id: keyof typeof KEYFRAME_SHAPES;
  name: string;
  description: string;
  easing: string[];
}> = [
  {
    id: "mini",
    name: "Mini",
    description: "Subtle/micro keyframes",
    easing: [],
  },
  {
    id: "extend",
    name: "Extend",
    description: "Hold keyframe",
    easing: ["hold", "step"],
  },
  { id: "long", name: "Long", description: "Long duration marker", easing: [] },
  {
    id: "roundHead",
    name: "Round Head",
    description: "Smooth start",
    easing: ["spring"],
  },
  {
    id: "rhExtend",
    name: "RH Extend",
    description: "Smooth with hold",
    easing: [],
  },
  {
    id: "rhLong",
    name: "RH Long",
    description: "Smooth with long hold",
    easing: [],
  },
  {
    id: "rhOutline",
    name: "RH Outline",
    description: "Outline variant",
    easing: [],
  },
  { id: "wide", name: "Wide", description: "Wide timing window", easing: [] },
  {
    id: "wideHammer",
    name: "Wide Hammer",
    description: "Hard stop after wide",
    easing: [],
  },
  {
    id: "pill",
    name: "Pill",
    description: "Eased transition",
    easing: ["easeInOut"],
  },
  {
    id: "watch",
    name: "Watch",
    description: "Custom bezier curve",
    easing: ["bezier"],
  },
  {
    id: "triangle",
    name: "Triangle",
    description: "Ease in (accelerating)",
    easing: ["easeIn"],
  },
  {
    id: "diamond",
    name: "Diamond",
    description: "Linear (standard)",
    easing: ["linear"],
  },
  {
    id: "martini",
    name: "Martini",
    description: "Ease out (decelerating)",
    easing: ["easeOut"],
  },
  {
    id: "radio",
    name: "Radio",
    description: "Point keyframe",
    easing: ["bounce"],
  },
  {
    id: "radioLong",
    name: "Radio Long",
    description: "Point with extension",
    easing: ["elastic"],
  },
];
