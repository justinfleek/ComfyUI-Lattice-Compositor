/**
 * Text Animator Service
 *
 * Provides After Effects-style text animation with:
 * - Range selectors (character, word, line based)
 * - Wiggly selectors (randomization)
 * - Expression selectors (programmatic control)
 * - Per-character property animation
 * - Built-in animation presets
 *
 * Tutorial 7: Kinetic Typography - Complete Implementation
 */

import type {
  AnimatableProperty,
  TextAnimator,
  TextAnimatorPresetType,
  TextAnimatorProperties,
  TextExpressionSelector,
  TextRangeSelector,
  TextWigglySelector,
} from "@/types/project";
import { evaluateSimpleExpression } from "./expressions/sesEvaluator";
import { SeededRandom } from "./particleSystem";

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

function generateId(): string {
  return `animator_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
}

function createAnimatableProp<T>(
  value: T,
  name: string,
): AnimatableProperty<T> {
  return {
    id: generateId(),
    name,
    type:
      typeof value === "number"
        ? "number"
        : typeof value === "string"
          ? "string"
          : "object",
    value,
    animated: false,
    keyframes: [],
  } as AnimatableProperty<T>;
}

/**
 * Get the interpolated value of an animatable property at a given frame.
 * Handles both static values and keyframe interpolation.
 *
 * @param prop - The animatable property
 * @param frame - The frame number to evaluate at
 * @returns The interpolated value
 */
export function getAnimatableValue<T>(
  prop: AnimatableProperty<T>,
  frame: number,
): T {
  if (!prop.animated || !prop.keyframes || prop.keyframes.length === 0) {
    return prop.value;
  }

  const keyframes = [...prop.keyframes].sort((a, b) => a.frame - b.frame);

  // Before first keyframe
  if (frame <= keyframes[0].frame) {
    return keyframes[0].value as T;
  }

  // After last keyframe
  if (frame >= keyframes[keyframes.length - 1].frame) {
    return keyframes[keyframes.length - 1].value as T;
  }

  // Find surrounding keyframes and interpolate
  for (let i = 0; i < keyframes.length - 1; i++) {
    if (frame >= keyframes[i].frame && frame <= keyframes[i + 1].frame) {
      const t =
        (frame - keyframes[i].frame) /
        (keyframes[i + 1].frame - keyframes[i].frame);
      const v1 = keyframes[i].value;
      const v2 = keyframes[i + 1].value;

      // Handle different value types
      if (typeof v1 === "number" && typeof v2 === "number") {
        return (v1 + (v2 - v1) * t) as T;
      }

      // Handle object types (position, scale, etc.)
      if (
        typeof v1 === "object" &&
        v1 !== null &&
        typeof v2 === "object" &&
        v2 !== null
      ) {
        const result: Record<string, number> = {};
        for (const key of Object.keys(v1 as object)) {
          const val1 = (v1 as Record<string, number>)[key];
          const val2 = (v2 as Record<string, number>)[key];
          if (typeof val1 === "number" && typeof val2 === "number") {
            result[key] = val1 + (val2 - val1) * t;
          } else {
            result[key] = val1;
          }
        }
        return result as T;
      }

      // For non-interpolatable types, return v1
      return v1 as T;
    }
  }

  return prop.value;
}

// ============================================================================
// DEFAULT VALUES
// ============================================================================

export const DEFAULT_RANGE_SELECTOR: TextRangeSelector = {
  mode: "percent",
  start: createAnimatableProp(0, "Start"),
  end: createAnimatableProp(100, "End"),
  offset: createAnimatableProp(0, "Offset"),
  basedOn: "characters",
  shape: "square",
  selectorMode: "add",
  amount: 100,
  smoothness: 100,
  randomizeOrder: false,
  randomSeed: 12345,
  ease: { high: 100, low: 0 },
};

// Default Wiggly Selector (Tutorial 7)
export const DEFAULT_WIGGLY_SELECTOR: TextWigglySelector = {
  enabled: false,
  mode: "add",
  maxAmount: 100,
  minAmount: 0,
  wigglesPerSecond: 2,
  correlation: 50,
  lockDimensions: false,
  basedOn: "characters",
  randomSeed: 54321,
};

// Default Expression Selector (Tutorial 7)
export const DEFAULT_EXPRESSION_SELECTOR: TextExpressionSelector = {
  enabled: false,
  mode: "add",
  amountExpression: "selectorValue * textIndex / textTotal",
  basedOn: "characters",
};

export const DEFAULT_ANIMATOR_PROPERTIES: TextAnimatorProperties = {};

// ============================================================================
// CREATE ANIMATOR
// ============================================================================

export function createTextAnimator(name?: string): TextAnimator {
  // Deep copy range selector to avoid shared references
  return {
    id: generateId(),
    name: name || "Animator 1",
    enabled: true,
    rangeSelector: {
      mode: DEFAULT_RANGE_SELECTOR.mode,
      start: createAnimatableProp(0, "Start"),
      end: createAnimatableProp(100, "End"),
      offset: createAnimatableProp(0, "Offset"),
      basedOn: DEFAULT_RANGE_SELECTOR.basedOn,
      shape: DEFAULT_RANGE_SELECTOR.shape,
      selectorMode: DEFAULT_RANGE_SELECTOR.selectorMode,
      amount: DEFAULT_RANGE_SELECTOR.amount,
      smoothness: DEFAULT_RANGE_SELECTOR.smoothness,
      randomizeOrder: DEFAULT_RANGE_SELECTOR.randomizeOrder,
      randomSeed: DEFAULT_RANGE_SELECTOR.randomSeed,
      ease: { ...DEFAULT_RANGE_SELECTOR.ease },
    },
    properties: { ...DEFAULT_ANIMATOR_PROPERTIES },
  };
}

// ============================================================================
// ANIMATOR PRESETS
// ============================================================================

export interface TextAnimatorPreset {
  type: TextAnimatorPresetType;
  name: string;
  description: string;
  duration: number; // frames
  create: (duration: number) => TextAnimator;
}

export const TEXT_ANIMATOR_PRESETS: Record<
  TextAnimatorPresetType,
  TextAnimatorPreset
> = {
  typewriter: {
    type: "typewriter",
    name: "Typewriter",
    description: "Characters appear one by one from left to right",
    duration: 60,
    create: (duration: number) => ({
      id: generateId(),
      name: "Typewriter",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        end: createAnimatableProp(100, "End"),
        basedOn: "characters",
        shape: "square",
      },
      properties: {
        opacity: createAnimatableProp(0, "Opacity"), // Characters start invisible
      },
    }),
  },

  fade_in_by_character: {
    type: "fade_in_by_character",
    name: "Fade In (Characters)",
    description: "Characters fade in from transparent",
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: "Fade In",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: "characters",
        shape: "ramp_down",
      },
      properties: {
        opacity: createAnimatableProp(0, "Opacity"),
      },
    }),
  },

  fade_in_by_word: {
    type: "fade_in_by_word",
    name: "Fade In (Words)",
    description: "Words fade in from transparent",
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: "Fade In Words",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: "words",
        shape: "ramp_down",
      },
      properties: {
        opacity: createAnimatableProp(0, "Opacity"),
      },
    }),
  },

  bounce_in: {
    type: "bounce_in",
    name: "Bounce In",
    description: "Characters bounce in from above",
    duration: 60,
    create: (duration: number) => ({
      id: generateId(),
      name: "Bounce In",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: "characters",
        shape: "ramp_down",
      },
      properties: {
        position: createAnimatableProp({ x: 0, y: -100 }, "Position"),
        opacity: createAnimatableProp(0, "Opacity"),
      },
    }),
  },

  wave: {
    type: "wave",
    name: "Wave",
    description: "Characters move up and down in a wave pattern",
    duration: 60,
    create: (_duration: number) => ({
      id: generateId(),
      name: "Wave",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        offset: createAnimatablePropWithKeyframes(0, "Offset", [
          { frame: 0, value: 0 },
          { frame: 30, value: 100 },
          { frame: 60, value: 0 },
        ]),
        basedOn: "characters",
        shape: "triangle",
      },
      properties: {
        position: createAnimatableProp({ x: 0, y: -20 }, "Position"),
      },
    }),
  },

  scale_in: {
    type: "scale_in",
    name: "Scale In",
    description: "Characters scale up from zero",
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: "Scale In",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: "characters",
        shape: "ramp_down",
      },
      properties: {
        scale: createAnimatableProp({ x: 0, y: 0 }, "Scale"),
        opacity: createAnimatableProp(0, "Opacity"),
      },
    }),
  },

  rotate_in: {
    type: "rotate_in",
    name: "Rotate In",
    description: "Characters rotate into place",
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: "Rotate In",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: "characters",
        shape: "ramp_down",
      },
      properties: {
        rotation: createAnimatableProp(-90, "Rotation"),
        opacity: createAnimatableProp(0, "Opacity"),
      },
    }),
  },

  slide_in_left: {
    type: "slide_in_left",
    name: "Slide In (Left)",
    description: "Characters slide in from the left",
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: "Slide Left",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: "characters",
        shape: "ramp_down",
      },
      properties: {
        position: createAnimatableProp({ x: -100, y: 0 }, "Position"),
        opacity: createAnimatableProp(0, "Opacity"),
      },
    }),
  },

  slide_in_right: {
    type: "slide_in_right",
    name: "Slide In (Right)",
    description: "Characters slide in from the right",
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: "Slide Right",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: "characters",
        shape: "ramp_down",
      },
      properties: {
        position: createAnimatableProp({ x: 100, y: 0 }, "Position"),
        opacity: createAnimatableProp(0, "Opacity"),
      },
    }),
  },

  blur_in: {
    type: "blur_in",
    name: "Blur In",
    description: "Characters unblur as they appear",
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: "Blur In",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: "characters",
        shape: "ramp_down",
      },
      properties: {
        blur: createAnimatableProp({ x: 20, y: 20 }, "Blur"),
        opacity: createAnimatableProp(0, "Opacity"),
      },
    }),
  },

  random_fade: {
    type: "random_fade",
    name: "Random Fade",
    description: "Characters fade in randomly",
    duration: 60,
    create: (duration: number) => ({
      id: generateId(),
      name: "Random Fade",
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, "Start", [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: "characters",
        shape: "square",
        randomizeOrder: true,
        randomSeed: Math.floor(Math.random() * 99999),
      },
      properties: {
        opacity: createAnimatableProp(0, "Opacity"),
      },
    }),
  },
};

// ============================================================================
// HELPER: Create animatable property with keyframes
// ============================================================================

function createAnimatablePropWithKeyframes<T>(
  value: T,
  name: string,
  keyframes: Array<{ frame: number; value: T }>,
  type: "number" | "color" | "position" | "enum" | "vector3" = "number",
): AnimatableProperty<T> {
  return {
    id: generateId(),
    name,
    type,
    value,
    animated: keyframes.length > 0,
    keyframes: keyframes.map((kf) => ({
      id: generateId(),
      frame: kf.frame,
      value: kf.value,
      interpolation: "bezier" as const,
      inHandle: { frame: -5, value: 0, enabled: true },
      outHandle: { frame: 5, value: 0, enabled: true },
      controlMode: "smooth" as const,
    })),
  };
}

// ============================================================================
// APPLY PRESET
// ============================================================================

export function applyTextAnimatorPreset(
  presetType: TextAnimatorPresetType,
  duration: number = 45,
): TextAnimator {
  const preset = TEXT_ANIMATOR_PRESETS[presetType];
  if (!preset) {
    return createTextAnimator();
  }
  return preset.create(duration);
}

// ============================================================================
// RANGE SELECTOR CALCULATION
// ============================================================================

/**
 * Calculate the influence (0-1) for a character at a given index
 * based on the range selector settings and current frame
 */
export function calculateCharacterInfluence(
  charIndex: number,
  totalChars: number,
  rangeSelector: TextRangeSelector,
  frame: number,
): number {
  // Get animated values
  const startValue = getRangeSelectorValue(rangeSelector.start, frame);
  const endValue = getRangeSelectorValue(rangeSelector.end, frame);
  const offsetValue = getRangeSelectorValue(rangeSelector.offset, frame);

  // Apply offset with proper wrapping (100 should stay as 100, not wrap to 0)
  const wrapTo100 = (val: number): number => {
    const mod = ((val % 100) + 100) % 100;
    return mod === 0 && val !== 0 ? 100 : mod;
  };
  const effectiveStart = wrapTo100(startValue + offsetValue);
  const effectiveEnd = wrapTo100(endValue + offsetValue);

  // Calculate character position (0-100)
  const charPosition = (charIndex / Math.max(1, totalChars - 1)) * 100;

  // Determine if range wraps around due to offset
  // Wraparound only happens when:
  // 1. Original range was valid (end >= start)
  // 2. Offset caused the range to cross the 100%/0% boundary
  // If user set start > end naturally (no offset), we normalize instead
  const originalRangeValid = endValue >= startValue;
  const rangeWraps = originalRangeValid && effectiveEnd < effectiveStart;

  let inRange: boolean;
  let positionInRange: number;

  if (rangeWraps) {
    // Wraparound range: affects [effectiveStart, 100] AND [0, effectiveEnd]
    // Example: start=80%, end=30% means characters at 80-100% and 0-30% are affected
    if (charPosition >= effectiveStart) {
      // In upper segment [effectiveStart, 100]
      inRange = true;
      const upperSegmentSize = 100 - effectiveStart;
      const totalRangeSize = upperSegmentSize + effectiveEnd;
      positionInRange =
        totalRangeSize > 0
          ? (charPosition - effectiveStart) / totalRangeSize
          : 0;
    } else if (charPosition <= effectiveEnd) {
      // In lower segment [0, effectiveEnd]
      inRange = true;
      const upperSegmentSize = 100 - effectiveStart;
      const totalRangeSize = upperSegmentSize + effectiveEnd;
      positionInRange =
        totalRangeSize > 0
          ? (upperSegmentSize + charPosition) / totalRangeSize
          : 1;
    } else {
      // In the gap between end and start
      inRange = false;
      positionInRange = 0;
    }
  } else {
    // Normal range (no wraparound)
    const normalizedStart = Math.min(effectiveStart, effectiveEnd);
    const normalizedEnd = Math.max(effectiveStart, effectiveEnd);

    if (charPosition < normalizedStart || charPosition > normalizedEnd) {
      inRange = false;
      positionInRange = 0;
    } else {
      inRange = true;
      const rangeSize = normalizedEnd - normalizedStart;
      positionInRange =
        rangeSize > 0 ? (charPosition - normalizedStart) / rangeSize : 0.5;
    }
  }

  if (!inRange) {
    return 0;
  }

  // Apply shape function
  return applyShape(positionInRange, rangeSelector.shape, rangeSelector.ease);
}

function getRangeSelectorValue(
  prop: AnimatableProperty<number>,
  frame: number,
): number {
  if (!prop.animated || prop.keyframes.length === 0) {
    return prop.value;
  }

  // Simple linear interpolation between keyframes
  const keyframes = prop.keyframes.sort((a, b) => a.frame - b.frame);

  if (frame <= keyframes[0].frame) {
    return keyframes[0].value as number;
  }

  if (frame >= keyframes[keyframes.length - 1].frame) {
    return keyframes[keyframes.length - 1].value as number;
  }

  // Find surrounding keyframes
  for (let i = 0; i < keyframes.length - 1; i++) {
    if (frame >= keyframes[i].frame && frame <= keyframes[i + 1].frame) {
      const t =
        (frame - keyframes[i].frame) /
        (keyframes[i + 1].frame - keyframes[i].frame);
      const v1 = keyframes[i].value as number;
      const v2 = keyframes[i + 1].value as number;
      return v1 + (v2 - v1) * t;
    }
  }

  return prop.value;
}

function applyShape(
  t: number,
  shape: TextRangeSelector["shape"],
  ease: { high: number; low: number },
): number {
  let value: number;

  switch (shape) {
    case "square":
      value = 1;
      break;
    case "ramp_up":
      value = t;
      break;
    case "ramp_down":
      value = 1 - t;
      break;
    case "triangle":
      value = 1 - Math.abs(2 * t - 1);
      break;
    case "round":
      value = Math.sin(t * Math.PI);
      break;
    case "smooth":
      // Smooth step (ease in-out)
      value = t * t * (3 - 2 * t);
      break;
    default:
      value = 1;
  }

  // Apply ease
  const easeRange = (ease.high - ease.low) / 100;
  return ease.low / 100 + value * easeRange;
}

// ============================================================================
// WIGGLY SELECTOR CALCULATION (Tutorial 7)
// ============================================================================

/**
 * Calculate wiggly influence for a character
 * Creates deterministic randomness that changes over time
 */
export function calculateWigglyInfluence(
  charIndex: number,
  _totalChars: number,
  wigglySelector: TextWigglySelector,
  frame: number,
  fps: number = 16,
): number {
  if (!wigglySelector.enabled) return 0;

  const time = frame / fps;
  const rng = new SeededRandom(wigglySelector.randomSeed + charIndex);

  // Calculate base random value for this character
  const baseRandom = rng.next();

  // Calculate temporal variation based on wiggles/second
  const wigglePhase = time * wigglySelector.wigglesPerSecond * Math.PI * 2;

  // Apply correlation - blend between individual and group movement
  const correlationFactor = wigglySelector.correlation / 100;
  const groupPhase = time * wigglySelector.wigglesPerSecond * Math.PI * 2;
  const individualPhase = wigglePhase + baseRandom * Math.PI * 2;

  // Interpolate between individual and group movement
  const phase =
    individualPhase * (1 - correlationFactor) + groupPhase * correlationFactor;

  // Calculate wiggle value (-1 to 1)
  const wiggleValue = Math.sin(phase);

  // Map to min/max amount range
  const range = wigglySelector.maxAmount - wigglySelector.minAmount;
  const amount = wigglySelector.minAmount + ((wiggleValue + 1) / 2) * range;

  return amount / 100; // Normalize to 0-1
}

/**
 * Calculate wiggly offset for position/scale properties
 * Returns {x, y} offsets that can be applied to properties
 */
export function calculateWigglyOffset(
  charIndex: number,
  wigglySelector: TextWigglySelector,
  frame: number,
  fps: number = 16,
): { x: number; y: number } {
  if (!wigglySelector.enabled) return { x: 0, y: 0 };

  const time = frame / fps;
  const rng = new SeededRandom(wigglySelector.randomSeed + charIndex * 1000);

  const baseRandomX = rng.next();
  const baseRandomY = wigglySelector.lockDimensions ? baseRandomX : rng.next();

  const wigglePhase = time * wigglySelector.wigglesPerSecond * Math.PI * 2;

  // Apply correlation
  const correlationFactor = wigglySelector.correlation / 100;
  const groupPhaseX = Math.sin(wigglePhase);
  // When lockDimensions is true, use same group phase for both axes
  const groupPhaseY = wigglySelector.lockDimensions
    ? groupPhaseX
    : Math.cos(wigglePhase);

  const individualPhaseX = Math.sin(wigglePhase + baseRandomX * Math.PI * 2);
  const individualPhaseY = Math.sin(wigglePhase + baseRandomY * Math.PI * 2);

  const x =
    individualPhaseX * (1 - correlationFactor) +
    groupPhaseX * correlationFactor;
  const y =
    individualPhaseY * (1 - correlationFactor) +
    groupPhaseY * correlationFactor;

  const amount =
    (wigglySelector.maxAmount + wigglySelector.minAmount) / 2 / 100;

  return { x: x * amount, y: y * amount };
}

// ============================================================================
// EXPRESSION SELECTOR CALCULATION (Tutorial 7)
// ============================================================================

/**
 * Evaluate expression selector for a character
 * Provides textIndex, textTotal, selectorValue, time, frame variables
 */
export function calculateExpressionInfluence(
  charIndex: number,
  totalChars: number,
  expressionSelector: TextExpressionSelector,
  rangeValue: number,
  frame: number,
  fps: number = 16,
): number {
  if (!expressionSelector.enabled) return rangeValue;

  const time = frame / fps;

  // SECURITY: Validate expression is a string
  if (typeof expressionSelector.amountExpression !== "string") {
    return rangeValue;
  }

  const expr = expressionSelector.amountExpression.trim();

  // SECURITY: Empty expression = passthrough
  if (!expr) {
    return rangeValue;
  }

  // SECURITY: Length limit to prevent payload attacks (10KB max)
  if (expr.length > 10240) {
    console.warn("[TextAnimator] Expression too long (max 10KB)");
    return rangeValue;
  }

  // Evaluate through central sesEvaluator (handles SES sandbox, length limit)
  // NOTE: No DoS protection - expressions CAN hang with infinite loops
  const result = evaluateSimpleExpression(expr, {
    textIndex: charIndex,
    textTotal: totalChars,
    selectorValue: rangeValue * 100, // 0-100 scale for expressions
    time,
    frame,
  });

  // Fail closed: null means evaluation failed
  if (result === null) {
    return rangeValue;
  }

  // Clamp result to 0-100 and normalize to 0-1
  return Math.max(0, Math.min(100, result)) / 100;
}

// ============================================================================
// SELECTOR MODE COMBINATION (Tutorial 7)
// ============================================================================

type SelectorMode =
  | "add"
  | "subtract"
  | "intersect"
  | "min"
  | "max"
  | "difference";

/**
 * Combine two selector values based on mode
 */
export function combineSelectorValues(
  baseValue: number,
  newValue: number,
  mode: SelectorMode,
): number {
  switch (mode) {
    case "add":
      return Math.min(1, baseValue + newValue);
    case "subtract":
      return Math.max(0, baseValue - newValue);
    case "intersect":
      return baseValue * newValue;
    case "min":
      return Math.min(baseValue, newValue);
    case "max":
      return Math.max(baseValue, newValue);
    case "difference":
      return Math.abs(baseValue - newValue);
    default:
      return newValue;
  }
}

// ============================================================================
// COMPREHENSIVE CHARACTER INFLUENCE (Tutorial 7)
// ============================================================================

/**
 * Calculate the complete influence for a character considering all selectors
 * This is the main entry point for per-character animation
 */
export function calculateCompleteCharacterInfluence(
  charIndex: number,
  totalChars: number,
  animator: TextAnimator,
  frame: number,
  fps: number = 16,
): number {
  // Start with range selector
  let influence = calculateCharacterInfluence(
    charIndex,
    totalChars,
    animator.rangeSelector,
    frame,
  );

  // Apply amount modifier
  const amount = animator.rangeSelector.amount ?? 100;
  influence *= amount / 100;

  // Apply smoothness (interpolate towards 0.5 for more smoothing)
  const smoothness = animator.rangeSelector.smoothness ?? 100;
  if (smoothness < 100) {
    const smoothFactor = smoothness / 100;
    influence = influence * smoothFactor + 0.5 * (1 - smoothFactor);
  }

  // Apply Wiggly Selector if enabled
  if (animator.wigglySelector?.enabled) {
    const wigglyInfluence = calculateWigglyInfluence(
      charIndex,
      totalChars,
      animator.wigglySelector,
      frame,
      fps,
    );
    influence = combineSelectorValues(
      influence,
      wigglyInfluence,
      animator.wigglySelector.mode,
    );
  }

  // Apply Expression Selector if enabled
  if (animator.expressionSelector?.enabled) {
    influence = calculateExpressionInfluence(
      charIndex,
      totalChars,
      animator.expressionSelector,
      influence,
      frame,
      fps,
    );
  }

  return Math.max(0, Math.min(1, influence));
}

// ============================================================================
// CREATE SELECTOR HELPERS (Tutorial 7)
// ============================================================================

export function createWigglySelector(
  overrides?: Partial<TextWigglySelector>,
): TextWigglySelector {
  return {
    ...DEFAULT_WIGGLY_SELECTOR,
    ...overrides,
    randomSeed: overrides?.randomSeed ?? Math.floor(Math.random() * 99999),
  };
}

export function createExpressionSelector(
  expression: string = DEFAULT_EXPRESSION_SELECTOR.amountExpression,
  overrides?: Partial<TextExpressionSelector>,
): TextExpressionSelector {
  return {
    ...DEFAULT_EXPRESSION_SELECTOR,
    amountExpression: expression,
    ...overrides,
    enabled: true,
  };
}

// ============================================================================
// EXPRESSION PRESETS (Tutorial 7)
// ============================================================================

export const EXPRESSION_PRESETS = {
  // Wave animation - characters move in sine wave
  wave: "Math.sin(time * 3 + textIndex * 0.5) * 50 + 50",

  // Staggered reveal - each character delays by index
  staggeredReveal:
    "linear(time, textIndex * 0.1, textIndex * 0.1 + 0.3, 0, 100)",

  // Random reveal - characters appear randomly
  randomReveal: "random() * 100 < linear(time, 0, 2, 0, 100) ? 100 : 0",

  // Cascade from center - center characters first
  cascadeCenter:
    "100 - Math.abs(textIndex - textTotal/2) / (textTotal/2) * 100",

  // Bounce effect - uses time for bounce animation
  bounce: "Math.abs(Math.sin(time * 5 + textIndex * 0.3)) * 100",

  // Linear gradient across text
  linearGradient: "textIndex / textTotal * 100",

  // Inverse gradient
  inverseGradient: "(1 - textIndex / textTotal) * 100",

  // Pulse - all characters pulse together
  pulse: "(Math.sin(time * 4) + 1) / 2 * 100",

  // Alternating - even/odd characters
  alternating: "textIndex % 2 === 0 ? 100 : 0",
};

// ============================================================================
// EXPORT PRESETS LIST
// ============================================================================

export const TEXT_ANIMATOR_PRESET_LIST = Object.values(TEXT_ANIMATOR_PRESETS);
