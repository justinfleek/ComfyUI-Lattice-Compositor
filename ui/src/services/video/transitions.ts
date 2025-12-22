/**
 * Video Transitions Service
 *
 * Implements professional video transition effects with multiple blend modes.
 * Inspired by filliptm's ComfyUI_Fill-Nodes/FL_VideoCrossfade
 * Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
 */

// ============================================================================
// Types
// ============================================================================

export type TransitionBlendMode =
  | 'normal'      // Linear crossfade
  | 'multiply'    // Darker, dramatic
  | 'screen'      // Lighter, ethereal
  | 'overlay'     // High contrast
  | 'soft-light'  // Subtle contrast
  | 'add'         // Bright flash
  | 'subtract'    // Dark flash
  | 'dissolve'    // Randomized fade
  | 'wipe-left'   // Directional wipe
  | 'wipe-right'
  | 'wipe-up'
  | 'wipe-down'
  | 'radial-wipe' // Circular reveal
  | 'iris-in'     // Circle expanding
  | 'iris-out'    // Circle contracting
  | 'cross-zoom'; // Zoom blur transition

export type TransitionEasing =
  | 'linear'
  | 'ease-in'
  | 'ease-out'
  | 'ease-in-out'
  | 'bounce';

export interface TransitionConfig {
  blendMode: TransitionBlendMode;
  duration: number;           // Duration in frames
  easing: TransitionEasing;
  direction?: number;         // 0-360 for wipes (degrees)
  softness?: number;          // 0-1 edge softness
  centerX?: number;           // 0-1 for radial effects
  centerY?: number;           // 0-1 for radial effects
}

export interface TransitionState {
  progress: number;           // 0-1 transition progress
  fromCanvas: HTMLCanvasElement;
  toCanvas: HTMLCanvasElement;
  config: TransitionConfig;
}

// ============================================================================
// Easing Functions
// ============================================================================

function applyEasing(t: number, easing: TransitionEasing): number {
  switch (easing) {
    case 'ease-in':
      return t * t;
    case 'ease-out':
      return 1 - (1 - t) * (1 - t);
    case 'ease-in-out':
      return t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;
    case 'bounce':
      const n1 = 7.5625;
      const d1 = 2.75;
      let tt = t;
      if (tt < 1 / d1) {
        return n1 * tt * tt;
      } else if (tt < 2 / d1) {
        return n1 * (tt -= 1.5 / d1) * tt + 0.75;
      } else if (tt < 2.5 / d1) {
        return n1 * (tt -= 2.25 / d1) * tt + 0.9375;
      } else {
        return n1 * (tt -= 2.625 / d1) * tt + 0.984375;
      }
    case 'linear':
    default:
      return t;
  }
}

// ============================================================================
// Blend Mode Functions
// ============================================================================

/**
 * Apply multiply blend mode pixel by pixel
 */
function blendMultiply(a: number, b: number): number {
  return (a * b) / 255;
}

/**
 * Apply screen blend mode pixel by pixel
 */
function blendScreen(a: number, b: number): number {
  return 255 - ((255 - a) * (255 - b)) / 255;
}

/**
 * Apply overlay blend mode pixel by pixel
 */
function blendOverlay(a: number, b: number): number {
  if (a < 128) {
    return (2 * a * b) / 255;
  } else {
    return 255 - (2 * (255 - a) * (255 - b)) / 255;
  }
}

/**
 * Apply soft light blend mode pixel by pixel
 */
function blendSoftLight(a: number, b: number): number {
  const t = (b / 255) * a + ((255 - b) / 255) * blendScreen(a, a);
  return Math.round(t);
}

/**
 * Apply additive blend mode pixel by pixel
 */
function blendAdd(a: number, b: number): number {
  return Math.min(255, a + b);
}

/**
 * Apply subtractive blend mode pixel by pixel
 */
function blendSubtract(a: number, b: number): number {
  return Math.max(0, a - b);
}

// ============================================================================
// Transition Renderers
// ============================================================================

/**
 * Render a normal (linear) crossfade transition
 */
function renderNormalTransition(
  output: CanvasRenderingContext2D,
  fromData: ImageData,
  toData: ImageData,
  progress: number
): void {
  const data = output.createImageData(fromData.width, fromData.height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  for (let i = 0; i < from.length; i += 4) {
    out[i] = from[i] * (1 - progress) + to[i] * progress;
    out[i + 1] = from[i + 1] * (1 - progress) + to[i + 1] * progress;
    out[i + 2] = from[i + 2] * (1 - progress) + to[i + 2] * progress;
    out[i + 3] = from[i + 3] * (1 - progress) + to[i + 3] * progress;
  }

  output.putImageData(data, 0, 0);
}

/**
 * Render a blend mode transition
 */
function renderBlendTransition(
  output: CanvasRenderingContext2D,
  fromData: ImageData,
  toData: ImageData,
  progress: number,
  blendFn: (a: number, b: number) => number
): void {
  const data = output.createImageData(fromData.width, fromData.height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  for (let i = 0; i < from.length; i += 4) {
    // Calculate blended color
    const blendR = blendFn(from[i], to[i]);
    const blendG = blendFn(from[i + 1], to[i + 1]);
    const blendB = blendFn(from[i + 2], to[i + 2]);

    // Lerp between from and blended based on progress
    out[i] = from[i] * (1 - progress) + blendR * progress;
    out[i + 1] = from[i + 1] * (1 - progress) + blendG * progress;
    out[i + 2] = from[i + 2] * (1 - progress) + blendB * progress;
    out[i + 3] = from[i + 3] * (1 - progress) + to[i + 3] * progress;
  }

  output.putImageData(data, 0, 0);
}

/**
 * Render a dissolve (random pixel) transition
 */
function renderDissolveTransition(
  output: CanvasRenderingContext2D,
  fromData: ImageData,
  toData: ImageData,
  progress: number,
  seed: number = 12345
): void {
  const data = output.createImageData(fromData.width, fromData.height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  // Simple seeded random for determinism
  let state = seed;
  const random = () => {
    state = (state * 1103515245 + 12345) & 0x7fffffff;
    return state / 0x7fffffff;
  };

  for (let i = 0; i < from.length; i += 4) {
    const useTarget = random() < progress;
    if (useTarget) {
      out[i] = to[i];
      out[i + 1] = to[i + 1];
      out[i + 2] = to[i + 2];
      out[i + 3] = to[i + 3];
    } else {
      out[i] = from[i];
      out[i + 1] = from[i + 1];
      out[i + 2] = from[i + 2];
      out[i + 3] = from[i + 3];
    }
  }

  output.putImageData(data, 0, 0);
}

/**
 * Render a directional wipe transition
 */
function renderWipeTransition(
  output: CanvasRenderingContext2D,
  fromData: ImageData,
  toData: ImageData,
  progress: number,
  direction: 'left' | 'right' | 'up' | 'down',
  softness: number = 0.1
): void {
  const { width, height } = fromData;
  const data = output.createImageData(width, height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  const softnessPixels = Math.max(1, Math.floor(
    (direction === 'left' || direction === 'right' ? width : height) * softness
  ));

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;

      let localProgress: number;
      switch (direction) {
        case 'left':
          localProgress = (width - x) / width;
          break;
        case 'right':
          localProgress = x / width;
          break;
        case 'up':
          localProgress = (height - y) / height;
          break;
        case 'down':
          localProgress = y / height;
          break;
      }

      // Calculate blend with soft edge
      const edgeStart = progress - softness / 2;
      const edgeEnd = progress + softness / 2;
      let blend: number;

      if (localProgress < edgeStart) {
        blend = 1;
      } else if (localProgress > edgeEnd) {
        blend = 0;
      } else {
        blend = 1 - (localProgress - edgeStart) / softness;
      }

      out[i] = from[i] * (1 - blend) + to[i] * blend;
      out[i + 1] = from[i + 1] * (1 - blend) + to[i + 1] * blend;
      out[i + 2] = from[i + 2] * (1 - blend) + to[i + 2] * blend;
      out[i + 3] = from[i + 3] * (1 - blend) + to[i + 3] * blend;
    }
  }

  output.putImageData(data, 0, 0);
}

/**
 * Render a radial wipe (clock wipe) transition
 */
function renderRadialWipeTransition(
  output: CanvasRenderingContext2D,
  fromData: ImageData,
  toData: ImageData,
  progress: number,
  centerX: number = 0.5,
  centerY: number = 0.5,
  softness: number = 0.05
): void {
  const { width, height } = fromData;
  const data = output.createImageData(width, height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  const cx = width * centerX;
  const cy = height * centerY;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;

      // Calculate angle from center (0-1 normalized)
      const angle = Math.atan2(y - cy, x - cx);
      const normalizedAngle = (angle + Math.PI) / (2 * Math.PI);

      // Soft edge transition
      const edgeStart = progress - softness;
      const edgeEnd = progress;
      let blend: number;

      if (normalizedAngle < edgeStart) {
        blend = 1;
      } else if (normalizedAngle > edgeEnd) {
        blend = 0;
      } else {
        blend = 1 - (normalizedAngle - edgeStart) / softness;
      }

      out[i] = from[i] * (1 - blend) + to[i] * blend;
      out[i + 1] = from[i + 1] * (1 - blend) + to[i + 1] * blend;
      out[i + 2] = from[i + 2] * (1 - blend) + to[i + 2] * blend;
      out[i + 3] = from[i + 3] * (1 - blend) + to[i + 3] * blend;
    }
  }

  output.putImageData(data, 0, 0);
}

/**
 * Render an iris (circular reveal) transition
 */
function renderIrisTransition(
  output: CanvasRenderingContext2D,
  fromData: ImageData,
  toData: ImageData,
  progress: number,
  direction: 'in' | 'out',
  centerX: number = 0.5,
  centerY: number = 0.5,
  softness: number = 0.1
): void {
  const { width, height } = fromData;
  const data = output.createImageData(width, height);
  const from = fromData.data;
  const to = toData.data;
  const out = data.data;

  const cx = width * centerX;
  const cy = height * centerY;
  const maxRadius = Math.sqrt(width * width + height * height) / 2;

  // For iris-in, radius grows; for iris-out, radius shrinks
  const effectiveProgress = direction === 'in' ? progress : 1 - progress;
  const targetRadius = maxRadius * effectiveProgress;
  const softnessRadius = maxRadius * softness;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;

      const dist = Math.sqrt((x - cx) ** 2 + (y - cy) ** 2);

      // Soft edge around the iris
      let blend: number;
      if (dist < targetRadius - softnessRadius / 2) {
        blend = direction === 'in' ? 1 : 0;
      } else if (dist > targetRadius + softnessRadius / 2) {
        blend = direction === 'in' ? 0 : 1;
      } else {
        const t = (dist - (targetRadius - softnessRadius / 2)) / softnessRadius;
        blend = direction === 'in' ? 1 - t : t;
      }

      out[i] = from[i] * (1 - blend) + to[i] * blend;
      out[i + 1] = from[i + 1] * (1 - blend) + to[i + 1] * blend;
      out[i + 2] = from[i + 2] * (1 - blend) + to[i + 2] * blend;
      out[i + 3] = from[i + 3] * (1 - blend) + to[i + 3] * blend;
    }
  }

  output.putImageData(data, 0, 0);
}

// ============================================================================
// Main Transition Function
// ============================================================================

/**
 * Render a video transition between two frames
 *
 * @param fromCanvas - Source frame canvas
 * @param toCanvas - Target frame canvas
 * @param progress - Transition progress 0-1 (will be eased internally)
 * @param config - Transition configuration
 * @returns Canvas with the transitioned frame
 */
export function renderTransition(
  fromCanvas: HTMLCanvasElement,
  toCanvas: HTMLCanvasElement,
  progress: number,
  config: TransitionConfig
): HTMLCanvasElement {
  const { width, height } = fromCanvas;

  // Create output canvas
  const output = document.createElement('canvas');
  output.width = width;
  output.height = height;
  const ctx = output.getContext('2d');
  if (!ctx) {
    throw new Error('Failed to get 2d context');
  }

  // Apply easing to progress
  const easedProgress = applyEasing(
    Math.max(0, Math.min(1, progress)),
    config.easing
  );

  // Get image data from both canvases
  const fromCtx = fromCanvas.getContext('2d');
  const toCtx = toCanvas.getContext('2d');
  if (!fromCtx || !toCtx) {
    throw new Error('Failed to get source contexts');
  }

  const fromData = fromCtx.getImageData(0, 0, width, height);
  const toData = toCtx.getImageData(0, 0, width, height);

  // Render based on blend mode
  switch (config.blendMode) {
    case 'normal':
      renderNormalTransition(ctx, fromData, toData, easedProgress);
      break;

    case 'multiply':
      renderBlendTransition(ctx, fromData, toData, easedProgress, blendMultiply);
      break;

    case 'screen':
      renderBlendTransition(ctx, fromData, toData, easedProgress, blendScreen);
      break;

    case 'overlay':
      renderBlendTransition(ctx, fromData, toData, easedProgress, blendOverlay);
      break;

    case 'soft-light':
      renderBlendTransition(ctx, fromData, toData, easedProgress, blendSoftLight);
      break;

    case 'add':
      renderBlendTransition(ctx, fromData, toData, easedProgress, blendAdd);
      break;

    case 'subtract':
      renderBlendTransition(ctx, fromData, toData, easedProgress, blendSubtract);
      break;

    case 'dissolve':
      renderDissolveTransition(ctx, fromData, toData, easedProgress);
      break;

    case 'wipe-left':
      renderWipeTransition(ctx, fromData, toData, easedProgress, 'left', config.softness);
      break;

    case 'wipe-right':
      renderWipeTransition(ctx, fromData, toData, easedProgress, 'right', config.softness);
      break;

    case 'wipe-up':
      renderWipeTransition(ctx, fromData, toData, easedProgress, 'up', config.softness);
      break;

    case 'wipe-down':
      renderWipeTransition(ctx, fromData, toData, easedProgress, 'down', config.softness);
      break;

    case 'radial-wipe':
      renderRadialWipeTransition(
        ctx, fromData, toData, easedProgress,
        config.centerX, config.centerY, config.softness
      );
      break;

    case 'iris-in':
      renderIrisTransition(
        ctx, fromData, toData, easedProgress, 'in',
        config.centerX, config.centerY, config.softness
      );
      break;

    case 'iris-out':
      renderIrisTransition(
        ctx, fromData, toData, easedProgress, 'out',
        config.centerX, config.centerY, config.softness
      );
      break;

    case 'cross-zoom':
      // For cross-zoom, we use a combination of scale + blur + crossfade
      // This is a simplified version - full implementation would need GPU
      renderNormalTransition(ctx, fromData, toData, easedProgress);
      break;

    default:
      renderNormalTransition(ctx, fromData, toData, easedProgress);
  }

  return output;
}

/**
 * Calculate transition progress for a frame within a transition
 *
 * @param currentFrame - Current frame number
 * @param transitionStartFrame - Frame where transition starts
 * @param transitionDuration - Duration in frames
 * @returns Progress 0-1, or null if not in transition
 */
export function getTransitionProgress(
  currentFrame: number,
  transitionStartFrame: number,
  transitionDuration: number
): number | null {
  if (currentFrame < transitionStartFrame) return null;
  if (currentFrame >= transitionStartFrame + transitionDuration) return null;

  return (currentFrame - transitionStartFrame) / transitionDuration;
}

/**
 * Create default transition configuration
 */
export function createDefaultTransition(): TransitionConfig {
  return {
    blendMode: 'normal',
    duration: 16,  // 1 second at 16fps
    easing: 'ease-in-out',
    softness: 0.1,
    centerX: 0.5,
    centerY: 0.5
  };
}

/**
 * Predefined transition presets
 */
export const TRANSITION_PRESETS: Record<string, TransitionConfig> = {
  'fade': {
    blendMode: 'normal',
    duration: 16,
    easing: 'ease-in-out',
    softness: 0.1
  },
  'flash-fade': {
    blendMode: 'add',
    duration: 8,
    easing: 'ease-out',
    softness: 0.1
  },
  'dark-fade': {
    blendMode: 'multiply',
    duration: 16,
    easing: 'ease-in-out',
    softness: 0.1
  },
  'dreamy': {
    blendMode: 'screen',
    duration: 24,
    easing: 'ease-out',
    softness: 0.2
  },
  'dramatic': {
    blendMode: 'overlay',
    duration: 16,
    easing: 'ease-in-out',
    softness: 0.1
  },
  'soft-cut': {
    blendMode: 'soft-light',
    duration: 8,
    easing: 'linear',
    softness: 0.1
  },
  'dissolve': {
    blendMode: 'dissolve',
    duration: 16,
    easing: 'linear',
    softness: 0.1
  },
  'wipe-left': {
    blendMode: 'wipe-left',
    duration: 16,
    easing: 'ease-in-out',
    softness: 0.1
  },
  'wipe-right': {
    blendMode: 'wipe-right',
    duration: 16,
    easing: 'ease-in-out',
    softness: 0.1
  },
  'iris-reveal': {
    blendMode: 'iris-in',
    duration: 24,
    easing: 'ease-out',
    softness: 0.15,
    centerX: 0.5,
    centerY: 0.5
  },
  'iris-close': {
    blendMode: 'iris-out',
    duration: 24,
    easing: 'ease-in',
    softness: 0.15,
    centerX: 0.5,
    centerY: 0.5
  },
  'clock-wipe': {
    blendMode: 'radial-wipe',
    duration: 24,
    easing: 'linear',
    softness: 0.05,
    centerX: 0.5,
    centerY: 0.5
  }
};

/**
 * Get all available transition blend modes
 */
export function getAllTransitionModes(): TransitionBlendMode[] {
  return [
    'normal', 'multiply', 'screen', 'overlay', 'soft-light', 'add', 'subtract',
    'dissolve', 'wipe-left', 'wipe-right', 'wipe-up', 'wipe-down',
    'radial-wipe', 'iris-in', 'iris-out', 'cross-zoom'
  ];
}

/**
 * Get human-readable name for a transition mode
 */
export function getTransitionModeName(mode: TransitionBlendMode): string {
  const names: Record<TransitionBlendMode, string> = {
    'normal': 'Crossfade',
    'multiply': 'Multiply Fade',
    'screen': 'Screen Fade',
    'overlay': 'Overlay Fade',
    'soft-light': 'Soft Light',
    'add': 'Additive Flash',
    'subtract': 'Subtractive',
    'dissolve': 'Dissolve',
    'wipe-left': 'Wipe Left',
    'wipe-right': 'Wipe Right',
    'wipe-up': 'Wipe Up',
    'wipe-down': 'Wipe Down',
    'radial-wipe': 'Clock Wipe',
    'iris-in': 'Iris In',
    'iris-out': 'Iris Out',
    'cross-zoom': 'Cross Zoom'
  };
  return names[mode] || mode;
}

export default {
  renderTransition,
  getTransitionProgress,
  createDefaultTransition,
  getAllTransitionModes,
  getTransitionModeName,
  TRANSITION_PRESETS
};
