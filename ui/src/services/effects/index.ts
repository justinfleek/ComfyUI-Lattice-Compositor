/**
 * Effects Registry
 *
 * Centralizes registration of all effect renderers.
 * Import this module to initialize the effect system.
 */
import { registerBlurEffects } from './blurRenderer';
import { registerColorEffects } from './colorRenderer';

/**
 * Initialize all effect renderers
 * Call this once at application startup
 */
export function initializeEffects(): void {
  registerBlurEffects();
  registerColorEffects();
  // Future effects will be registered here:
  // registerDistortEffects();
  // registerGenerateEffects();
}

// Re-export for convenience
export { gaussianBlurRenderer } from './blurRenderer';
export {
  brightnessContrastRenderer,
  hueSaturationRenderer,
  levelsRenderer,
  tintRenderer,
  curvesRenderer,
  glowRenderer,
  dropShadowRenderer,
  createSCurve,
  createLiftCurve
} from './colorRenderer';

// Mask system
export {
  renderMask,
  combineMasks,
  applyTrackMatte,
  applyMasksToLayer
} from './maskRenderer';
