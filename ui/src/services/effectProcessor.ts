/**
 * Effect Processor
 *
 * Handles effect parameter evaluation and effect stack processing.
 * Effects are processed top-to-bottom, with each effect's output
 * becoming the input for the next effect.
 */
import type { EffectInstance } from '@/types/effects';
import type { AnimatableProperty } from '@/types/project';
import { interpolateProperty } from './interpolation';
import { renderLogger } from '@/utils/logger';

/**
 * Evaluated effect parameters at a specific frame
 * All animatable values resolved to their concrete values
 */
export interface EvaluatedEffectParams {
  [key: string]: any;
}

/**
 * Result of processing an effect stack
 */
export interface EffectStackResult {
  canvas: HTMLCanvasElement;
  ctx: CanvasRenderingContext2D;
}

/**
 * Effect renderer function signature
 * Takes input canvas/ctx, evaluated params, returns processed canvas
 */
export type EffectRenderer = (
  input: EffectStackResult,
  params: EvaluatedEffectParams
) => EffectStackResult;

/**
 * Registry of effect renderers by effect key
 */
const effectRenderers: Map<string, EffectRenderer> = new Map();

/**
 * Register an effect renderer
 */
export function registerEffectRenderer(effectKey: string, renderer: EffectRenderer): void {
  effectRenderers.set(effectKey, renderer);
}

/**
 * Evaluate all effect parameters at a given frame
 * Resolves AnimatableProperty values to their concrete values
 *
 * @param effect - The effect instance to evaluate
 * @param frame - Current frame number
 * @returns Object with parameter keys mapped to evaluated values
 */
export function evaluateEffectParameters(
  effect: EffectInstance,
  frame: number
): EvaluatedEffectParams {
  const evaluated: EvaluatedEffectParams = {};

  for (const [key, param] of Object.entries(effect.parameters)) {
    // Type assertion since we know it's AnimatableProperty
    const animatableProp = param as AnimatableProperty<any>;
    evaluated[key] = interpolateProperty(animatableProp, frame);
  }

  return evaluated;
}

/**
 * Process a stack of effects on an input canvas
 *
 * Effects are processed in order (top to bottom in the UI).
 * Each effect receives the output of the previous effect.
 * Disabled effects are skipped.
 *
 * @param effects - Array of effect instances
 * @param inputCanvas - Source canvas to process
 * @param frame - Current frame for animation evaluation
 * @returns Processed canvas with all effects applied
 */
export function processEffectStack(
  effects: EffectInstance[],
  inputCanvas: HTMLCanvasElement,
  frame: number
): EffectStackResult {
  // Create a working copy of the input
  const workCanvas = document.createElement('canvas');
  workCanvas.width = inputCanvas.width;
  workCanvas.height = inputCanvas.height;
  const workCtx = workCanvas.getContext('2d')!;
  workCtx.drawImage(inputCanvas, 0, 0);

  let current: EffectStackResult = {
    canvas: workCanvas,
    ctx: workCtx
  };

  // Process each enabled effect in order
  for (const effect of effects) {
    if (!effect.enabled) {
      continue;
    }

    const renderer = effectRenderers.get(effect.effectKey);
    if (!renderer) {
      renderLogger.warn(`No renderer registered for effect: ${effect.effectKey}`);
      continue;
    }

    // Evaluate parameters at current frame
    const params = evaluateEffectParameters(effect, frame);

    // Apply the effect
    try {
      current = renderer(current, params);
    } catch (error) {
      renderLogger.error(`Error applying effect ${effect.name}:`, error);
      // Continue with current state on error
    }
  }

  return current;
}

/**
 * Create a canvas from an ImageData object
 */
export function imageDataToCanvas(imageData: ImageData): HTMLCanvasElement {
  const canvas = document.createElement('canvas');
  canvas.width = imageData.width;
  canvas.height = imageData.height;
  const ctx = canvas.getContext('2d')!;
  ctx.putImageData(imageData, 0, 0);
  return canvas;
}

/**
 * Get ImageData from a canvas
 */
export function canvasToImageData(canvas: HTMLCanvasElement): ImageData {
  const ctx = canvas.getContext('2d')!;
  return ctx.getImageData(0, 0, canvas.width, canvas.height);
}

/**
 * Create a new canvas with the same dimensions
 */
export function createMatchingCanvas(source: HTMLCanvasElement): EffectStackResult {
  const canvas = document.createElement('canvas');
  canvas.width = source.width;
  canvas.height = source.height;
  const ctx = canvas.getContext('2d')!;
  return { canvas, ctx };
}

/**
 * Check if any effects in the stack are enabled
 */
export function hasEnabledEffects(effects: EffectInstance[]): boolean {
  return effects.some(e => e.enabled);
}

/**
 * Get list of registered effect keys
 */
export function getRegisteredEffects(): string[] {
  return Array.from(effectRenderers.keys());
}

export default {
  evaluateEffectParameters,
  processEffectStack,
  registerEffectRenderer,
  imageDataToCanvas,
  canvasToImageData,
  createMatchingCanvas,
  hasEnabledEffects,
  getRegisteredEffects
};
