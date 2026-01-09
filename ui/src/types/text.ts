// ============================================================
// TEXT TYPES - Text layers and animators
// ============================================================
// Extracted from project.ts for better modularity
// ============================================================

import type { AnimatableProperty } from "./animation";

// ============================================================
// TEXT DATA (Professional Feature Set)
// ============================================================

export interface TextData {
  // Source Text
  text: string;
  fontFamily: string;
  fontSize: number;
  fontWeight: string;
  fontStyle: "normal" | "italic";
  fill: string; // Color hex
  stroke: string; // Color hex
  strokeWidth: number;

  // Character Properties (from Context Menu / Animators)
  tracking: number; // Tracking (spacing)
  lineSpacing: number; // Leading
  lineAnchor: number; // 0% to 100%
  characterOffset: number; // Integer shift
  characterValue: number; // Unicode shift
  blur: { x: number; y: number }; // Per-character blur

  // Paragraph (legacy aliases)
  letterSpacing: number; // Alias for tracking
  lineHeight: number; // Alias for lineSpacing
  textAlign: "left" | "center" | "right";

  // Path Options (Professional Feature Set)
  pathLayerId: string | null;
  pathReversed: boolean; // Reverse Path direction
  pathPerpendicularToPath: boolean; // Characters perpendicular to path tangent
  pathForceAlignment: boolean; // Force alignment to path
  pathFirstMargin: number; // First Margin (pixels from path start)
  pathLastMargin: number; // Last Margin (pixels from path end)
  pathOffset: number; // 0-100%, animatable - shifts all characters along path
  pathAlign: "left" | "center" | "right"; // Baseline alignment

  // More Options (Advanced)
  anchorPointGrouping: "character" | "word" | "line" | "all";
  groupingAlignment: { x: number; y: number }; // Percentages
  fillAndStroke: "fill-over-stroke" | "stroke-over-fill";
  interCharacterBlending: "normal" | "multiply" | "screen" | "overlay";

  // 3D Text
  perCharacter3D: boolean;

  // Advanced Character Properties (Tutorial 7)
  baselineShift?: number; // Vertical shift in pixels
  textCase?: "normal" | "uppercase" | "lowercase" | "smallCaps";
  verticalAlign?: "normal" | "superscript" | "subscript";

  // OpenType Features (Phase 2: Text System)
  kerning?: boolean; // Enable/disable kerning (default: true)
  ligatures?: boolean; // Enable standard ligatures (default: true)
  discretionaryLigatures?: boolean; // Enable discretionary ligatures (default: false)
  smallCapsFeature?: boolean; // Use OpenType small caps (default: false)
  stylisticSet?: number; // Stylistic set 1-20 (0 = none)

  // Advanced Paragraph Properties (Tutorial 7)
  firstLineIndent?: number; // Pixels
  spaceBefore?: number; // Pixels before paragraph
  spaceAfter?: number; // Pixels after paragraph

  // Text Animators (per-character animation)
  animators?: TextAnimator[];
}

// ============================================================
// TEXT ANIMATOR (Per-character animation like AE)
// ============================================================

export interface TextAnimator {
  id: string;
  name: string;
  enabled: boolean;

  // Selectors (can have multiple - Range, Wiggly, Expression)
  rangeSelector: TextRangeSelector;
  wigglySelector?: TextWigglySelector;
  expressionSelector?: TextExpressionSelector;

  // Animatable Properties
  properties: TextAnimatorProperties;
}

export interface TextRangeSelector {
  // Units mode
  mode: "percent" | "index";

  // Selection range (0-100 for percent, integers for index)
  start: AnimatableProperty<number>;
  end: AnimatableProperty<number>;
  offset: AnimatableProperty<number>;

  // Selection unit
  basedOn: "characters" | "characters_excluding_spaces" | "words" | "lines";

  // Shape for selection falloff
  shape: "square" | "ramp_up" | "ramp_down" | "triangle" | "round" | "smooth";

  // Selector Mode (Tutorial 7 - how multiple selectors combine)
  selectorMode?:
    | "add"
    | "subtract"
    | "intersect"
    | "min"
    | "max"
    | "difference";

  // Advanced parameters (Tutorial 7)
  amount?: number; // 0-100%, overall influence of this selector
  smoothness?: number; // 0-100%, smoothing of selection edges

  // Randomness
  randomizeOrder: boolean;
  randomSeed: number;

  // Easing
  ease: { high: number; low: number }; // 0-100
}

// Wiggly Selector - adds randomization to property values (Tutorial 7)
export interface TextWigglySelector {
  enabled: boolean;

  // Mode for combining with other selectors
  mode: "add" | "subtract" | "intersect" | "min" | "max" | "difference";

  // Amount of wiggle influence
  maxAmount: number; // 0-100%
  minAmount: number; // 0-100%

  // Temporal settings
  wigglesPerSecond: number; // How fast values change

  // Correlation - how much characters move together
  // 0% = fully random per character, 100% = all move together (wave)
  correlation: number;

  // Lock dimensions - X and Y wiggle together
  lockDimensions: boolean;

  // Spatial settings
  basedOn: "characters" | "characters_excluding_spaces" | "words" | "lines";

  // Random seed for deterministic results
  randomSeed: number;
}

// Expression Selector - programmatic control via expressions (Tutorial 7)
export interface TextExpressionSelector {
  enabled: boolean;

  // Mode for combining with other selectors
  mode: "add" | "subtract" | "intersect" | "min" | "max" | "difference";

  // The expression that calculates amount per character
  // Available variables: textIndex, textTotal, selectorValue, time, frame
  amountExpression: string;

  // Based on unit
  basedOn: "characters" | "characters_excluding_spaces" | "words" | "lines";
}

// Union type for text animator property values
type TextAnimatorValue = number | string | { x: number; y: number };

export interface TextAnimatorProperties {
  // Index signature for dynamic property access
  // Uses union type instead of 'any' for better type safety
  [key: string]: AnimatableProperty<TextAnimatorValue> | undefined;

  // Transform properties
  position?: AnimatableProperty<{ x: number; y: number }>;
  anchorPoint?: AnimatableProperty<{ x: number; y: number }>;
  scale?: AnimatableProperty<{ x: number; y: number }>;
  rotation?: AnimatableProperty<number>;
  skew?: AnimatableProperty<number>;
  skewAxis?: AnimatableProperty<number>;

  // Style properties
  opacity?: AnimatableProperty<number>;
  fillColor?: AnimatableProperty<string>;
  fillBrightness?: AnimatableProperty<number>;
  fillSaturation?: AnimatableProperty<number>;
  fillHue?: AnimatableProperty<number>;
  strokeColor?: AnimatableProperty<string>;
  strokeWidth?: AnimatableProperty<number>;

  // Character properties
  tracking?: AnimatableProperty<number>;
  lineAnchor?: AnimatableProperty<number>;
  lineSpacing?: AnimatableProperty<number>;
  characterOffset?: AnimatableProperty<number>;
  blur?: AnimatableProperty<{ x: number; y: number }>;
}

// Text Animator Presets
export type TextAnimatorPresetType =
  | "typewriter"
  | "fade_in_by_character"
  | "fade_in_by_word"
  | "bounce_in"
  | "wave"
  | "scale_in"
  | "rotate_in"
  | "slide_in_left"
  | "slide_in_right"
  | "blur_in"
  | "random_fade";

// ============================================================
// HELPER FUNCTIONS
// ============================================================

/**
 * Create default text data
 */
export function createDefaultTextData(): TextData {
  return {
    text: "Text",
    fontFamily: "Arial",
    fontSize: 72,
    fontWeight: "normal",
    fontStyle: "normal",
    fill: "#ffffff",
    stroke: "",
    strokeWidth: 0,
    tracking: 0,
    lineSpacing: 1.2,
    lineAnchor: 50,
    characterOffset: 0,
    characterValue: 0,
    blur: { x: 0, y: 0 },
    letterSpacing: 0,
    lineHeight: 1.2,
    textAlign: "center",
    pathLayerId: null,
    pathReversed: false,
    pathPerpendicularToPath: true,
    pathForceAlignment: false,
    pathFirstMargin: 0,
    pathLastMargin: 0,
    pathOffset: 0,
    pathAlign: "center",
    anchorPointGrouping: "character",
    groupingAlignment: { x: 50, y: 50 },
    fillAndStroke: "fill-over-stroke",
    interCharacterBlending: "normal",
    perCharacter3D: false,
  };
}
