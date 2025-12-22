/**
 * Video Services
 *
 * Video processing, transitions, effects, and frame interpolation.
 *
 * Attribution:
 * - filliptm's ComfyUI_Fill-Nodes for workflow inspiration
 * - RIFE (Megvii Research) for frame interpolation
 */

export {
  renderTransition,
  getTransitionProgress,
  createDefaultTransition,
  getAllTransitionModes,
  getTransitionModeName,
  TRANSITION_PRESETS,
  type TransitionBlendMode,
  type TransitionEasing,
  type TransitionConfig,
  type TransitionState
} from './transitions';

// Frame Interpolation (RIFE-based)
export {
  // Types
  type RIFEModel,
  type InterpolationFactor,
  type InterpolationModel,
  type PairInterpolationResult,
  type SequenceInterpolationResult,
  type SlowMoResult,
  type InterpolationProgressCallback,

  // API functions
  getInterpolationModels,
  interpolateFramePair,
  interpolateSequence,
  createSlowMotion,

  // Client-side fallback
  blendFrames,
  interpolateFramesClient,

  // Utilities
  base64ToImageData,
  base64ToBlob as interpolationBase64ToBlob,

  // Presets
  INTERPOLATION_PRESETS,
  isInterpolationAvailable
} from './frameInterpolation';
