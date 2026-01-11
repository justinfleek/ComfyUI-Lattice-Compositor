/**
 * Text Animator Actions - Helpers
 *
 * Helper functions for text animator operations.
 */

import type { Layer, TextData } from "@/types/project";
import { hexToRgba, rgbToHex } from "@/utils/colorUtils";
import type { TextAnimatorStore, TextPathConfig } from "./types";

// ============================================================================
// EXTENDED TYPES FOR DYNAMIC PROPERTIES
// ============================================================================

/**
 * TextData extended with optional path configuration.
 * The pathConfig property is dynamically added at runtime.
 */
export interface TextDataWithPath extends TextData {
  pathConfig?: TextPathConfig;
}

// ============================================================================
// COLOR CONVERSION HELPERS
// ============================================================================

/**
 * Convert RGBA object {r, g, b, a} to hex string
 */
export function rgbaObjectToHex(rgba: {
  r: number;
  g: number;
  b: number;
  a?: number;
}): string {
  const r = Math.max(0, Math.min(255, Math.round(rgba.r)));
  const g = Math.max(0, Math.min(255, Math.round(rgba.g)));
  const b = Math.max(0, Math.min(255, Math.round(rgba.b)));
  return rgbToHex(r, g, b); // Use rgbToHex (no alpha in hex for fillColor)
}

/**
 * Convert hex string to RGBA object {r, g, b, a}
 */
export function hexToRgbaObject(hex: string): {
  r: number;
  g: number;
  b: number;
  a: number;
} {
  const rgba = hexToRgba(hex);
  if (rgba) {
    return { r: rgba[0], g: rgba[1], b: rgba[2], a: Math.round(rgba[3] * 255) };
  }
  // Default to black if invalid
  return { r: 0, g: 0, b: 0, a: 255 };
}

/**
 * Check if value is an RGBA color object
 */
export function isRgbaObject(
  value: unknown,
): value is { r: number; g: number; b: number; a?: number } {
  return (
    typeof value === "object" &&
    value !== null &&
    typeof (value as Record<string, unknown>).r === "number" &&
    typeof (value as Record<string, unknown>).g === "number" &&
    typeof (value as Record<string, unknown>).b === "number" &&
    ((value as Record<string, unknown>).a === undefined ||
      typeof (value as Record<string, unknown>).a === "number")
  );
}

// ============================================================================
// LAYER/DATA ACCESS HELPERS
// ============================================================================

/**
 * Get a text layer by ID and validate it's a text layer
 */
export function getTextLayer(
  store: TextAnimatorStore,
  layerId: string,
): Layer | undefined {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "text") return undefined;
  return layer;
}

/**
 * Get text data from layer
 */
export function getTextData(layer: Layer): TextData | undefined {
  return layer.data as TextData | undefined;
}

/**
 * Ensure animators array exists on text data
 */
export function ensureAnimatorsArray(textData: TextData): void {
  if (!textData.animators) {
    textData.animators = [];
  }
}

/**
 * Generate unique ID
 */
export function generateId(prefix: string = "ta"): string {
  return `${prefix}_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

/**
 * Update modified timestamp on store
 */
export function updateModified(store: TextAnimatorStore): void {
  store.project.meta.modified = new Date().toISOString();
}
