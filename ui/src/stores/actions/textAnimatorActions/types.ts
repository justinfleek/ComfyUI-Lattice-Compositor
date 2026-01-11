/**
 * Text Animator Actions - Types
 *
 * Store interface and configuration types for text animators.
 */

import type { Composition, Layer } from "@/types/project";
import type { TextAnimatorProperties } from "@/types/text";

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface TextAnimatorStore {
  project: {
    meta: { modified: string };
  };
  currentFrame: number;
  getActiveCompLayers(): Layer[];
  getActiveComp(): Composition | null;
  pushHistory(): void;
}

// ============================================================================
// TYPES
// ============================================================================

export interface CharacterTransform {
  index: number;
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number };
  opacity: number;
  tracking: number;
  fillColor?: { r: number; g: number; b: number; a: number };
  strokeWidth?: number;
}

export interface AddTextAnimatorConfig {
  name?: string;
  properties?: Partial<TextAnimatorProperties>;
}

export interface RangeSelectorConfig {
  start?: number;
  end?: number;
  offset?: number;
  shape?: "square" | "ramp_up" | "ramp_down" | "triangle" | "round" | "smooth";
  amount?: number;
  smoothness?: number;
  basedOn?: "characters" | "words" | "lines";
  randomizeOrder?: boolean;
}

export interface ExpressionSelectorConfig {
  expression?: string;
  mode?: "add" | "subtract" | "intersect" | "min" | "max" | "difference";
  basedOn?: "characters" | "words" | "lines";
}

export interface WigglySelectorConfig {
  mode?: "add" | "subtract" | "intersect" | "min" | "max" | "difference";
  maxAmount?: number;
  minAmount?: number;
  wigglesPerSecond?: number;
  correlation?: number;
  lockDimensions?: boolean;
  randomSeed?: number;
}

export interface TextPathConfig {
  pathPoints: import("@/types/project").ControlPoint[];
  closed?: boolean;
  reversed?: boolean;
  perpendicularToPath?: boolean;
  forceAlignment?: boolean;
  firstMargin?: number;
  lastMargin?: number;
  offset?: number;
  align?: "left" | "center" | "right";
}
