/**
 * Effects Registry
 *
 * Centralizes registration of all effect renderers.
 * Import this module to initialize the effect system.
 */

import { registerAudioVisualizerEffects } from "./audioVisualizer";
import { registerBlurEffects } from "./blurRenderer";
import { registerCinematicBloomEffects } from "./cinematicBloom";
import { registerColorEffects } from "./colorRenderer";
import { registerDistortEffects } from "./distortRenderer";
import { registerExpressionControlRenderers } from "./expressionControlRenderer";
import { registerGenerateEffects } from "./generateRenderer";
import { registerMeshDeformEffect } from "./meshDeformRenderer";
import { registerStylizeEffects } from "./stylizeRenderer";
import { registerTimeEffects } from "./timeRenderer";

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
  registerMeshDeformEffect();
}

// Re-export audio visualizer effects
export {
  AUDIO_SPECTRUM_DEFAULTS,
  AUDIO_WAVEFORM_DEFAULTS,
  type AudioSpectrumParams,
  type AudioWaveformParams,
  registerAudioVisualizerEffects,
  renderAudioSpectrum,
  renderAudioWaveform,
} from "./audioVisualizer";
// Re-export blur effects
export {
  boxBlurRenderer,
  directionalBlurRenderer,
  disposeWebGLBlur,
  gaussianBlurRenderer,
  gaussianBlurRendererAsync,
  isWebGLBlurAvailable,
  radialBlurRenderer,
  sharpenRenderer,
} from "./blurRenderer";
// Re-export cinematic bloom effects
export {
  applyChromaticAberration,
  cinematicBloomRenderer,
  generateGaussianKernel,
  generateInverseSquareKernel,
  generateLensDirt,
  glowRenderer as simpleGlowRenderer,
  registerCinematicBloomEffects,
  tonemapACES,
  tonemapHable,
  tonemapReinhard,
} from "./cinematicBloom";
// Re-export color effects
export {
  brightnessContrastRenderer,
  colorBalanceRenderer,
  createLiftCurve,
  createSCurve,
  curvesRenderer,
  dropShadowRenderer,
  exposureRenderer,
  glowRenderer,
  hueSaturationRenderer,
  invertRenderer,
  levelsRenderer,
  posterizeRenderer,
  thresholdRenderer,
  tintRenderer,
  vibranceRenderer,
} from "./colorRenderer";
// Re-export distort effects
export {
  displacementMapRenderer,
  rippleDistortRenderer,
  transformRenderer,
  turbulentDisplaceRenderer,
  warpRenderer,
} from "./distortRenderer";
// Re-export expression control utilities
export {
  getControlParameterName,
  isExpressionControl,
  registerExpressionControlRenderers,
} from "./expressionControlRenderer";
// Re-export generate effects
export {
  clearNoiseTileCache,
  ellipseRenderer,
  fillRenderer,
  fractalNoiseRenderer,
  getNoiseTileCacheStats,
  gradientRampRenderer,
  radioWavesRenderer,
} from "./generateRenderer";
// Re-export layer style renderers (Photoshop-style effects)
export {
  angleToOffset,
  applyBlur as applyStyleBlur,
  createMatchingCanvas as createStyleCanvas,
  dilateAlpha,
  erodeAlpha,
  getCompositeOperation,
  // Utility functions
  getValue as getStyleValue,
  renderBevelEmbossStyle,
  renderColorOverlayStyle,
  renderDropShadowStyle,
  renderGradientOverlayStyle,
  renderInnerGlowStyle,
  renderInnerShadowStyle,
  renderLayerStyles,
  renderOuterGlowStyle,
  renderSatinStyle,
  renderStrokeStyle,
  rgbaToString,
} from "./layerStyleRenderer";
// Mask system
export {
  applyMasksToLayer,
  applyTrackMatte,
  combineMasks,
  renderMask,
} from "./maskRenderer";
// Matte edge effects (choker, spill suppressor, feathering)
export {
  analyzeEdgeQuality,
  applyAlpha,
  applyChoker,
  applyEdgeFeather,
  applySpillSuppressor,
  type ChokerParams,
  createBlueScreenSpillParams,
  createDefaultChokerParams,
  createGreenScreenSpillParams,
  type EdgeFeatherParams,
  extractAlpha,
  type SpillSuppressorParams,
} from "./matteEdge";
// Re-export mesh deform effect (puppet pin-style deformation)
export {
  clearMeshDeformCaches,
  meshDeformRenderer,
  registerMeshDeformEffect,
} from "./meshDeformRenderer";
// Re-export stylize effects
export {
  ditherRenderer,
  embossRenderer,
  findEdgesRenderer,
  glitchRenderer,
  halftoneRenderer,
  mosaicRenderer,
  pixelSortRenderer,
  rgbSplitRenderer,
  rippleRenderer,
  scanlinesRenderer,
  vhsRenderer,
} from "./stylizeRenderer";
// Re-export time effects
export {
  clearAllFrameBuffers,
  echoRenderer,
  posterizeTimeRenderer,
  timeDisplacementRenderer,
} from "./timeRenderer";
