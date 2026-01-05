/**
 * Video Services
 *
 * Video processing, transitions, effects, and frame interpolation.
 *
 * Attribution:
 * - filliptm's ComfyUI_Fill-Nodes for workflow inspiration
 * - RIFE (Megvii Research) for frame interpolation
 */

// Frame Interpolation (RIFE-based)
export {
  base64ToBlob as interpolationBase64ToBlob,
  // Utilities
  base64ToImageData,
  // Client-side fallback
  blendFrames,
  createSlowMotion,
  // API functions
  getInterpolationModels,
  // Presets
  INTERPOLATION_PRESETS,
  type InterpolationFactor,
  type InterpolationModel,
  type InterpolationProgressCallback,
  interpolateFramePair,
  interpolateFramesClient,
  interpolateSequence,
  isInterpolationAvailable,
  type PairInterpolationResult,
  // Types
  type RIFEModel,
  type SequenceInterpolationResult,
  type SlowMoResult,
} from "./frameInterpolation";
export {
  createDefaultTransition,
  getAllTransitionModes,
  getTransitionModeName,
  getTransitionProgress,
  renderTransition,
  TRANSITION_PRESETS,
  type TransitionBlendMode,
  type TransitionConfig,
  type TransitionEasing,
  type TransitionState,
} from "./transitions";
