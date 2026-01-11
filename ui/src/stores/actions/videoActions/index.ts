/**
 * Video Actions
 *
 * Video layer creation, metadata handling, and composition resizing.
 * Handles fps mismatch detection and resolution (match/conform).
 *
 * MODULE STRUCTURE:
 * - types.ts: Store interface and result types
 * - createLayer.ts: Video layer creation
 * - fpsResolution.ts: FPS mismatch resolution
 * - updates.ts: Video data updates and composition resize
 */

// Types
export type {
  VideoStore,
  VideoImportSuccess,
  VideoImportFpsMismatch,
  VideoImportFpsUnknown,
  VideoImportError,
  VideoImportResult,
} from "./types";

// Layer creation
export { createVideoLayer, createVideoLayerFromAsset } from "./createLayer";

// FPS resolution
export {
  completeVideoImportWithMatch,
  completeVideoImportWithConform,
  cancelVideoImport,
  completeVideoImportWithUserFps,
} from "./fpsResolution";

// Updates
export {
  updateVideoLayerData,
  onVideoMetadataLoaded,
  resizeComposition,
} from "./updates";
