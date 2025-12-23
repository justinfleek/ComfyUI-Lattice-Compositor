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
import { registerTimeEffects } from './timeRenderer';
import { registerStylizeEffects } from './stylizeRenderer';
import { registerAudioVisualizerEffects } from './audioVisualizer';
import { registerExpressionControlRenderers } from './expressionControlRenderer';
import { registerCinematicBloomEffects } from './cinematicBloom';

/**
 * Initialize all effect renderers
 * Call this once at application startup
 */
export function initializeEffects(): void {
  registerBlurEffects();
  registerColorEffects();
  registerDistortEffects();
  registerGenerateEffects();
  registerTimeEffects();
  registerStylizeEffects();
  registerAudioVisualizerEffects();
  registerExpressionControlRenderers();
  registerCinematicBloomEffects();
}

// Re-export blur effects
export {
  gaussianBlurRenderer,
  gaussianBlurRendererAsync,
  directionalBlurRenderer,
  radialBlurRenderer,
  boxBlurRenderer,
  sharpenRenderer,
  isWebGLBlurAvailable,
  disposeWebGLBlur
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
  displacementMapRenderer,
  turbulentDisplaceRenderer,
  rippleDistortRenderer
} from './distortRenderer';

// Re-export generate effects
export {
  fillRenderer,
  gradientRampRenderer,
  fractalNoiseRenderer,
  radioWavesRenderer,
  ellipseRenderer,
  clearNoiseTileCache,
  getNoiseTileCacheStats
} from './generateRenderer';

// Re-export time effects
export {
  echoRenderer,
  posterizeTimeRenderer,
  timeDisplacementRenderer,
  clearAllFrameBuffers
} from './timeRenderer';

// Mask system
export {
  renderMask,
  combineMasks,
  applyTrackMatte,
  applyMasksToLayer
} from './maskRenderer';

// Re-export stylize effects
export {
  pixelSortRenderer,
  glitchRenderer,
  vhsRenderer,
  rgbSplitRenderer,
  scanlinesRenderer,
  halftoneRenderer,
  ditherRenderer,
  rippleRenderer,
  embossRenderer,
  findEdgesRenderer,
  mosaicRenderer
} from './stylizeRenderer';

// Matte edge effects (choker, spill suppressor, feathering)
export {
  applyChoker,
  applySpillSuppressor,
  applyEdgeFeather,
  extractAlpha,
  applyAlpha,
  analyzeEdgeQuality,
  createDefaultChokerParams,
  createGreenScreenSpillParams,
  createBlueScreenSpillParams,
  type ChokerParams,
  type SpillSuppressorParams,
  type EdgeFeatherParams,
} from './matteEdge';

// Re-export audio visualizer effects
export {
  renderAudioSpectrum,
  renderAudioWaveform,
  registerAudioVisualizerEffects,
  AUDIO_SPECTRUM_DEFAULTS,
  AUDIO_WAVEFORM_DEFAULTS,
  type AudioSpectrumParams,
  type AudioWaveformParams
} from './audioVisualizer';

// Re-export expression control utilities
export {
  registerExpressionControlRenderers,
  isExpressionControl,
  getControlParameterName
} from './expressionControlRenderer';

// Re-export cinematic bloom effects
export {
  cinematicBloomRenderer,
  glowRenderer as simpleGlowRenderer,
  registerCinematicBloomEffects,
  tonemapACES,
  tonemapReinhard,
  tonemapHable,
  generateInverseSquareKernel,
  generateGaussianKernel,
  generateLensDirt,
  applyChromaticAberration
} from './cinematicBloom';

// Re-export layer style renderers (Photoshop-style effects)
export {
  renderLayerStyles,
  renderDropShadowStyle,
  renderInnerShadowStyle,
  renderOuterGlowStyle,
  renderInnerGlowStyle,
  renderBevelEmbossStyle,
  renderSatinStyle,
  renderColorOverlayStyle,
  renderGradientOverlayStyle,
  renderStrokeStyle,
  // Utility functions
  getValue as getStyleValue,
  createMatchingCanvas as createStyleCanvas,
  rgbaToString,
  angleToOffset,
  applyBlur as applyStyleBlur,
  dilateAlpha,
  erodeAlpha,
  getCompositeOperation
} from './layerStyleRenderer';
