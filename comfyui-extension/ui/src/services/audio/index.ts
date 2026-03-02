/**
 * Audio Services
 *
 * Audio processing, stem separation, beat detection, and related services.
 *
 * Attribution:
 * - filliptm's ComfyUI_Fill-Nodes for workflow inspiration
 * - Facebook Research's Demucs for stem separation
 */

// Enhanced Beat Detection
export {
  BEAT_DETECTION_PRESETS,
  type BeatGrid,
  // Main functions
  createEnhancedBeatGrid,
  // Config & Presets
  DEFAULT_BEAT_CONFIG,
  // Types
  type EnhancedBeat,
  type EnhancedBeatConfig,
  generateSubBeats,
  getBeatIntensity,
  getNearestBeat,
  getPulseIntensity,
  isEnhancedBeatDetectionAvailable,
  isOnBeat,
  isOnDownbeat,
} from "./enhancedBeatDetection";
// Stem Separation (Demucs)
export {
  // Utilities
  base64ToBlob,
  createAudioElement,
  type DemucsModel,
  downloadStem,
  // Main functions
  getStemModels,
  isolateStem,
  isStemSeparationAvailable,
  // Presets & availability
  STEM_PRESETS,
  type StemIsolationResult,
  type StemModel,
  type StemProgressCallback,
  type StemSeparationResult,
  // Types
  type StemType,
  separateStems,
  separateStemsForReactivity,
} from "./stemSeparation";
