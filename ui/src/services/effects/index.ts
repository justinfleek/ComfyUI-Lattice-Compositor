/**
 * Effects Registry
 *
 * Centralizes registration of all effect renderers.
 * Import this module to initialize the effect system.
 */
import { registerBlurEffects } from './blurRenderer';
import { registerColorEffects } from './colorRenderer';
import { registerDistortEffects } from './distortRenderer';
import { registerGenerateEffects } from './generateRenderer';

/**
 * Initialize all effect renderers
 * Call this once at application startup
 */
export function initializeEffects(): void {
  registerBlurEffects();
  registerColorEffects();
  registerDistortEffects();
  registerGenerateEffects();
}

// Re-export blur effects
export {
  gaussianBlurRenderer,
  directionalBlurRenderer,
  radialBlurRenderer,
  boxBlurRenderer,
  sharpenRenderer
} from './blurRenderer';

// Re-export color effects
export {
  brightnessContrastRenderer,
  hueSaturationRenderer,
  levelsRenderer,
  tintRenderer,
  curvesRenderer,
  glowRenderer,
  dropShadowRenderer,
  colorBalanceRenderer,
  exposureRenderer,
  vibranceRenderer,
  invertRenderer,
  posterizeRenderer,
  thresholdRenderer,
  createSCurve,
  createLiftCurve
} from './colorRenderer';

// Re-export distort effects
export {
  transformRenderer,
  warpRenderer,
  displacementMapRenderer
} from './distortRenderer';

// Re-export generate effects
export {
  fillRenderer,
  gradientRampRenderer,
  fractalNoiseRenderer
} from './generateRenderer';

// Mask system
export {
  renderMask,
  combineMasks,
  applyTrackMatte,
  applyMasksToLayer
} from './maskRenderer';
