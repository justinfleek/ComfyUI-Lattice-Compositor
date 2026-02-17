/**
 * Expression Types
 *
 * Type definitions used across expression modules.
 */

import type { FootageDataAccessor } from "@/types/dataAsset";
import type { Keyframe } from "@/types/project";

// ============================================================
// EXPRESSION CONTEXT
// ============================================================

export interface ExpressionContext {
  // Time
  time: number; // Current time in seconds
  frame: number; // Current frame number
  fps: number; // Frames per second
  duration: number; // Composition duration

  // Composition info
  compWidth: number; // Composition width in pixels
  compHeight: number; // Composition height in pixels

  // Layer info
  layerId: string;
  layerIndex: number;
  layerName: string;
  inPoint: number; // Layer start time
  outPoint: number; // Layer end time

  // Property info
  propertyName: string;
  value: number | number[]; // Current interpolated value
  velocity: number | number[]; // Current velocity

  // Keyframe info
  numKeys: number;
  keyframes: Keyframe<number | number[]>[];

  // External data (JSON-driven) - unused, kept for future extensibility
  // If used, should be typed based on actual JSON schema
  data?: never;

  // Expression control parameters (for effect("Slider")("Slider") access)
  // Values are numbers (sliders), strings (text), or booleans (checkboxes)
  params: Record<string, number | string | boolean>;

  // Other layer properties (for linking)
  getLayerProperty: (
    layerId: string,
    propertyPath: string,
  ) => number | number[] | null;

  // Data-driven animation (footage access)
  footage: (name: string) => FootageDataAccessor | null;

  // === Enhanced layer/effect access for thisLayer/thisComp ===

  // Current layer's transform values (for thisLayer.transform)
  layerTransform: {
    position: number[];
    rotation: number[];
    scale: number[];
    opacity: number;
    origin: number[]; // anchor point
  };

  // Current layer's effects (for thisLayer.effect())
  layerEffects: Array<{
    name: string;
    effectKey: string;
    enabled: boolean;
    parameters: Record<string, number | number[] | string | boolean>;
  }>;

  // All layers in composition (for thisComp.layer(name))
  allLayers: Array<{
    id: string;
    name: string;
    index: number;
  }>;

  // Get effect parameter value from any layer
  getLayerEffectParam: (
    layerId: string,
    effectName: string,
    paramName: string,
  ) => number | number[] | string | boolean | null;
}

// ============================================================
// EXPRESSION DEFINITION
// ============================================================

export interface Expression {
  type: "preset" | "function" | "custom";
  name: string;
  params: Record<string, number | string | boolean>;
  enabled: boolean;
  code?: string; // For custom expressions - JavaScript code string
}

// ============================================================
// EXPRESSION VALIDATION
// ============================================================

export interface ExpressionValidationResult {
  valid: boolean;
  error?: string;
  errorLine?: number;
  errorColumn?: number;
}

// ============================================================
// SOURCE RECT (for sourceRectAtTime)
// ============================================================

/**
 * Source rectangle interface matching industry standards
 */
export interface SourceRect {
  top: number; // Y position of top edge
  left: number; // X position of left edge
  width: number; // Width of content
  height: number; // Height of content
}

// ============================================================
// TEXT SOURCE INFO
// ============================================================

export interface TextSourceInfo {
  text: string;
  fontSize: number;
  fontFamily: string;
  fontStyle: string;
  fillColor: string; // Hex color string (e.g., "#FF0000")
  strokeColor: string; // Hex color string (e.g., "#000000")
  strokeWidth: number;
  tracking: number;
  leading: number;
}

// ============================================================
// TEXT ANIMATOR CONTEXT
// ============================================================

/**
 * Text animator context for per-character expressions
 */
export interface TextAnimatorContext extends ExpressionContext {
  // Per-character index (0-based)
  textIndex: number;
  // Total character count
  textTotal: number;
  // Character being animated
  char: string;
  // Selector value (0-1 range based on selector)
  selectorValue: number;
  // Word index (if text is split by words)
  wordIndex?: number;
  // Line index (for multi-line text)
  lineIndex?: number;
  // Character position in word
  charInWord?: number;
  // Character position in line
  charInLine?: number;
}
