/**
 * Audio Services
 *
 * Audio processing, stem separation, beat detection, and related services.
 *
 * Attribution:
 * - filliptm's ComfyUI_Fill-Nodes for workflow inspiration
 * - Facebook Research's Demucs for stem separation
 */

// Stem Separation (Demucs)
export {
  // Types
  type StemType,
  type DemucsModel,
  type StemModel,
  type StemSeparationResult,
  type StemIsolationResult,
  type StemProgressCallback,

  // Main functions
  getStemModels,
  separateStems,
  isolateStem,
  separateStemsForReactivity,

  // Utilities
  base64ToBlob,
  downloadStem,
  createAudioElement,

  // Presets & availability
  STEM_PRESETS,
  isStemSeparationAvailable
} from './stemSeparation';

// Enhanced Beat Detection
export {
  // Types
  type EnhancedBeat,
  type BeatGrid,
  type EnhancedBeatConfig,

  // Main functions
  createEnhancedBeatGrid,
  generateSubBeats,
  getNearestBeat,
  isOnBeat,
  isOnDownbeat,
  getBeatIntensity,
  getPulseIntensity,

  // Config & Presets
  DEFAULT_BEAT_CONFIG,
  BEAT_DETECTION_PRESETS,
  isEnhancedBeatDetectionAvailable
} from './enhancedBeatDetection';
