// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// MASK TYPES - Layer masks and track mattes
// ═══════════════════════════════════════════════════════════════════════════
// Extracted from project.ts for better modularity
// ═══════════════════════════════════════════════════════════════════════════

import type { AnimatableProperty } from "./animation";

// ═══════════════════════════════════════════════════════════════════════════
// MATTE TYPES (Track Mattes)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Matte source types (uses layer above as matte source)
 */
export type MatteType =
  | "none" // No matte source
  | "alpha" // Use alpha channel of matte layer
  | "alpha_inverted" // Invert alpha of matte layer
  | "luma" // Use luminance of matte layer
  | "luma_inverted"; // Invert luminance of matte layer

/** @deprecated Use MatteType instead */
export type TrackMatteType = MatteType;

// ═══════════════════════════════════════════════════════════════════════════
//                                                             // mask // mode
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Mask mode determines how multiple masks combine
 */
export type MaskMode =
  | "add" // Union of masks (default)
  | "subtract" // Subtract this mask from previous
  | "intersect" // Intersection with previous
  | "lighten" // Max of mask values
  | "darken" // Min of mask values
  | "difference" // Absolute difference
  | "none"; // Mask is disabled

// ═══════════════════════════════════════════════════════════════════════════
//                                          // mask // path // and // vertices
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Mask path - collection of bezier vertices forming a closed shape
 */
export interface MaskPath {
  closed: boolean;
  vertices: MaskVertex[];
}

/**
 * Mask vertex - point with optional bezier handles
 */
export interface MaskVertex {
  // Position (relative to layer bounds, 0-1 or pixel coordinates)
  x: number;
  y: number;

  // Incoming tangent (from previous vertex)
  inTangentX: number;
  inTangentY: number;

  // Outgoing tangent (to next vertex)
  outTangentX: number;
  outTangentY: number;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                            // layer // mask
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Layer mask - bezier path that clips layer content
 */
export interface LayerMask {
  id: string;
  name: string;
  enabled: boolean;
  locked: boolean;
  mode: MaskMode;
  inverted: boolean;

  // Mask path (bezier curve)
  path: AnimatableProperty<MaskPath>;

  // Mask properties
  opacity: AnimatableProperty<number>; // 0-100
  feather: AnimatableProperty<number>; // Blur amount in pixels
  featherX?: AnimatableProperty<number>; // Horizontal feather (if different)
  featherY?: AnimatableProperty<number>; // Vertical feather (if different)
  expansion: AnimatableProperty<number>; // Expand/contract mask boundary

  // Color tint for mask display in UI
  color: string; // Hex color for visualization
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // helper // functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Helper to create a mask AnimatableProperty
 */
function createMaskAnimatableProperty<T>(
  name: string,
  value: T,
  type: "number" | "position" | "color" | "enum" | "vector3" = "number",
): AnimatableProperty<T> {
  return {
    id: `mask_prop_${name}_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
    name,
    type,
    value,
    animated: false,
    keyframes: [],
  };
}

/**
 * Create a default rectangular mask covering the full layer
 */
export function createDefaultMask(
  id: string,
  width: number,
  height: number,
): LayerMask {
  return {
    id,
    name: "Mask 1",
    enabled: true,
    locked: false,
    mode: "add",
    inverted: false,
    path: createMaskAnimatableProperty<MaskPath>(
      "Mask Path",
      {
        closed: true,
        vertices: [
          {
            x: 0,
            y: 0,
            inTangentX: 0,
            inTangentY: 0,
            outTangentX: 0,
            outTangentY: 0,
          },
          {
            x: width,
            y: 0,
            inTangentX: 0,
            inTangentY: 0,
            outTangentX: 0,
            outTangentY: 0,
          },
          {
            x: width,
            y: height,
            inTangentX: 0,
            inTangentY: 0,
            outTangentX: 0,
            outTangentY: 0,
          },
          {
            x: 0,
            y: height,
            inTangentX: 0,
            inTangentY: 0,
            outTangentX: 0,
            outTangentY: 0,
          },
        ],
      },
      "position",
    ),
    opacity: createMaskAnimatableProperty<number>(
      "Mask Opacity",
      100,
      "number",
    ),
    feather: createMaskAnimatableProperty<number>("Mask Feather", 0, "number"),
    expansion: createMaskAnimatableProperty<number>(
      "Mask Expansion",
      0,
      "number",
    ),
    color: "#FFFF00", // Yellow default
  };
}

/**
 * Create an elliptical mask
 */
export function createEllipseMask(
  id: string,
  centerX: number,
  centerY: number,
  radiusX: number,
  radiusY: number,
): LayerMask {
  // Bezier approximation of ellipse (kappa = 4 * (sqrt(2) - 1) / 3)
  const kappa = 0.5522847498;
  const ox = radiusX * kappa; // Control point offset horizontal
  const oy = radiusY * kappa; // Control point offset vertical

  return {
    id,
    name: "Mask 1",
    enabled: true,
    locked: false,
    mode: "add",
    inverted: false,
    path: createMaskAnimatableProperty<MaskPath>(
      "Mask Path",
      {
        closed: true,
        vertices: [
          {
            x: centerX,
            y: centerY - radiusY,
            inTangentX: -ox,
            inTangentY: 0,
            outTangentX: ox,
            outTangentY: 0,
          },
          {
            x: centerX + radiusX,
            y: centerY,
            inTangentX: 0,
            inTangentY: -oy,
            outTangentX: 0,
            outTangentY: oy,
          },
          {
            x: centerX,
            y: centerY + radiusY,
            inTangentX: ox,
            inTangentY: 0,
            outTangentX: -ox,
            outTangentY: 0,
          },
          {
            x: centerX - radiusX,
            y: centerY,
            inTangentX: 0,
            inTangentY: oy,
            outTangentX: 0,
            outTangentY: -oy,
          },
        ],
      },
      "position",
    ),
    opacity: createMaskAnimatableProperty<number>(
      "Mask Opacity",
      100,
      "number",
    ),
    feather: createMaskAnimatableProperty<number>("Mask Feather", 0, "number"),
    expansion: createMaskAnimatableProperty<number>(
      "Mask Expansion",
      0,
      "number",
    ),
    color: "#00FFFF", // Cyan
  };
}
