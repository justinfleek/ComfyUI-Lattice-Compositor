/**
 * Text Animator Service
 *
 * Provides After Effects-style text animation with:
 * - Range selectors (character, word, line based)
 * - Per-character property animation
 * - Built-in animation presets
 */

import type {
  TextAnimator,
  TextRangeSelector,
  TextAnimatorProperties,
  TextAnimatorPresetType,
  AnimatableProperty,
} from '@/types/project';

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

function generateId(): string {
  return `animator_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`;
}

function createAnimatableProp<T>(value: T, name: string): AnimatableProperty<T> {
  return {
    id: generateId(),
    name,
    type: typeof value === 'number' ? 'number' : typeof value === 'string' ? 'string' : 'object',
    value,
    animated: false,
    keyframes: [],
  } as AnimatableProperty<T>;
}

// ============================================================================
// DEFAULT VALUES
// ============================================================================

export const DEFAULT_RANGE_SELECTOR: TextRangeSelector = {
  mode: 'percent',
  start: createAnimatableProp(0, 'Start'),
  end: createAnimatableProp(100, 'End'),
  offset: createAnimatableProp(0, 'Offset'),
  basedOn: 'characters',
  shape: 'square',
  randomizeOrder: false,
  randomSeed: 12345,
  ease: { high: 100, low: 0 },
};

export const DEFAULT_ANIMATOR_PROPERTIES: TextAnimatorProperties = {};

// ============================================================================
// CREATE ANIMATOR
// ============================================================================

export function createTextAnimator(name?: string): TextAnimator {
  return {
    id: generateId(),
    name: name || 'Animator 1',
    enabled: true,
    rangeSelector: { ...DEFAULT_RANGE_SELECTOR },
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

export const TEXT_ANIMATOR_PRESETS: Record<TextAnimatorPresetType, TextAnimatorPreset> = {
  typewriter: {
    type: 'typewriter',
    name: 'Typewriter',
    description: 'Characters appear one by one from left to right',
    duration: 60,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Typewriter',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        end: createAnimatableProp(100, 'End'),
        basedOn: 'characters',
        shape: 'square',
      },
      properties: {
        opacity: createAnimatableProp(0, 'Opacity'), // Characters start invisible
      },
    }),
  },

  fade_in_by_character: {
    type: 'fade_in_by_character',
    name: 'Fade In (Characters)',
    description: 'Characters fade in from transparent',
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Fade In',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: 'characters',
        shape: 'ramp_down',
      },
      properties: {
        opacity: createAnimatableProp(0, 'Opacity'),
      },
    }),
  },

  fade_in_by_word: {
    type: 'fade_in_by_word',
    name: 'Fade In (Words)',
    description: 'Words fade in from transparent',
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Fade In Words',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: 'words',
        shape: 'ramp_down',
      },
      properties: {
        opacity: createAnimatableProp(0, 'Opacity'),
      },
    }),
  },

  bounce_in: {
    type: 'bounce_in',
    name: 'Bounce In',
    description: 'Characters bounce in from above',
    duration: 60,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Bounce In',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: 'characters',
        shape: 'ramp_down',
      },
      properties: {
        position: createAnimatableProp({ x: 0, y: -100 }, 'Position'),
        opacity: createAnimatableProp(0, 'Opacity'),
      },
    }),
  },

  wave: {
    type: 'wave',
    name: 'Wave',
    description: 'Characters move up and down in a wave pattern',
    duration: 60,
    create: (_duration: number) => ({
      id: generateId(),
      name: 'Wave',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        offset: createAnimatablePropWithKeyframes(0, 'Offset', [
          { frame: 0, value: 0 },
          { frame: 30, value: 100 },
          { frame: 60, value: 0 },
        ]),
        basedOn: 'characters',
        shape: 'triangle',
      },
      properties: {
        position: createAnimatableProp({ x: 0, y: -20 }, 'Position'),
      },
    }),
  },

  scale_in: {
    type: 'scale_in',
    name: 'Scale In',
    description: 'Characters scale up from zero',
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Scale In',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: 'characters',
        shape: 'ramp_down',
      },
      properties: {
        scale: createAnimatableProp({ x: 0, y: 0 }, 'Scale'),
        opacity: createAnimatableProp(0, 'Opacity'),
      },
    }),
  },

  rotate_in: {
    type: 'rotate_in',
    name: 'Rotate In',
    description: 'Characters rotate into place',
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Rotate In',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: 'characters',
        shape: 'ramp_down',
      },
      properties: {
        rotation: createAnimatableProp(-90, 'Rotation'),
        opacity: createAnimatableProp(0, 'Opacity'),
      },
    }),
  },

  slide_in_left: {
    type: 'slide_in_left',
    name: 'Slide In (Left)',
    description: 'Characters slide in from the left',
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Slide Left',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: 'characters',
        shape: 'ramp_down',
      },
      properties: {
        position: createAnimatableProp({ x: -100, y: 0 }, 'Position'),
        opacity: createAnimatableProp(0, 'Opacity'),
      },
    }),
  },

  slide_in_right: {
    type: 'slide_in_right',
    name: 'Slide In (Right)',
    description: 'Characters slide in from the right',
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Slide Right',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: 'characters',
        shape: 'ramp_down',
      },
      properties: {
        position: createAnimatableProp({ x: 100, y: 0 }, 'Position'),
        opacity: createAnimatableProp(0, 'Opacity'),
      },
    }),
  },

  blur_in: {
    type: 'blur_in',
    name: 'Blur In',
    description: 'Characters unblur as they appear',
    duration: 45,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Blur In',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: 'characters',
        shape: 'ramp_down',
      },
      properties: {
        blur: createAnimatableProp({ x: 20, y: 20 }, 'Blur'),
        opacity: createAnimatableProp(0, 'Opacity'),
      },
    }),
  },

  random_fade: {
    type: 'random_fade',
    name: 'Random Fade',
    description: 'Characters fade in randomly',
    duration: 60,
    create: (duration: number) => ({
      id: generateId(),
      name: 'Random Fade',
      enabled: true,
      rangeSelector: {
        ...DEFAULT_RANGE_SELECTOR,
        start: createAnimatablePropWithKeyframes(100, 'Start', [
          { frame: 0, value: 100 },
          { frame: duration, value: 0 },
        ]),
        basedOn: 'characters',
        shape: 'square',
        randomizeOrder: true,
        randomSeed: Math.floor(Math.random() * 99999),
      },
      properties: {
        opacity: createAnimatableProp(0, 'Opacity'),
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
  keyframes: Array<{ frame: number; value: T }>
): AnimatableProperty<T> {
  return {
    id: generateId(),
    name,
    type: typeof value === 'number' ? 'number' : typeof value === 'string' ? 'string' : 'object',
    value,
    animated: keyframes.length > 0,
    keyframes: keyframes.map(kf => ({
      id: generateId(),
      frame: kf.frame,
      value: kf.value,
      easing: 'ease-out',
    })),
  } as AnimatableProperty<T>;
}

// ============================================================================
// APPLY PRESET
// ============================================================================

export function applyTextAnimatorPreset(
  presetType: TextAnimatorPresetType,
  duration: number = 45
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
  frame: number
): number {
  // Get animated values
  const startValue = getRangeSelectorValue(rangeSelector.start, frame);
  const endValue = getRangeSelectorValue(rangeSelector.end, frame);
  const offsetValue = getRangeSelectorValue(rangeSelector.offset, frame);

  // Apply offset
  const effectiveStart = (startValue + offsetValue) % 100;
  const effectiveEnd = (endValue + offsetValue) % 100;

  // Calculate character position (0-100)
  const charPosition = (charIndex / Math.max(1, totalChars - 1)) * 100;

  // Check if character is in range
  const normalizedStart = Math.min(effectiveStart, effectiveEnd);
  const normalizedEnd = Math.max(effectiveStart, effectiveEnd);

  if (charPosition < normalizedStart || charPosition > normalizedEnd) {
    return 0;
  }

  // Calculate position within range (0-1)
  const rangeSize = normalizedEnd - normalizedStart;
  const positionInRange = rangeSize > 0
    ? (charPosition - normalizedStart) / rangeSize
    : 0.5;

  // Apply shape function
  return applyShape(positionInRange, rangeSelector.shape, rangeSelector.ease);
}

function getRangeSelectorValue(prop: AnimatableProperty<number>, frame: number): number {
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
      const t = (frame - keyframes[i].frame) / (keyframes[i + 1].frame - keyframes[i].frame);
      const v1 = keyframes[i].value as number;
      const v2 = keyframes[i + 1].value as number;
      return v1 + (v2 - v1) * t;
    }
  }

  return prop.value;
}

function applyShape(
  t: number,
  shape: TextRangeSelector['shape'],
  ease: { high: number; low: number }
): number {
  let value: number;

  switch (shape) {
    case 'square':
      value = 1;
      break;
    case 'ramp_up':
      value = t;
      break;
    case 'ramp_down':
      value = 1 - t;
      break;
    case 'triangle':
      value = 1 - Math.abs(2 * t - 1);
      break;
    case 'round':
      value = Math.sin(t * Math.PI);
      break;
    case 'smooth':
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
// EXPORT PRESETS LIST
// ============================================================================

export const TEXT_ANIMATOR_PRESET_LIST = Object.values(TEXT_ANIMATOR_PRESETS);
