/**
 * Export Services Index
 * Central export point for all export-related services
 */

// Depth rendering
export {
  renderDepthFrame,
  convertDepthToFormat,
  depthToImageData,
  applyColormap,
  exportDepthSequence,
  generateDepthMetadata,
} from './depthRenderer';

// Camera export formats
export {
  interpolateCameraAtFrame,
  computeViewMatrix,
  computeProjectionMatrix,
  exportToMotionCtrl,
  exportToMotionCtrlSVD,
  mapToWan22FunCamera,
  exportToUni3C,
  exportToCameraCtrl,
  exportCameraMatrices,
  exportCameraForTarget,
} from './cameraExportFormats';

// Re-export camera types from their source
export type { CameraKeyframe } from '@/types/camera';
export type { FullCameraExport as ExportOptions } from '@/types/export';

// Export pipeline
export {
  ExportPipeline,
  exportToComfyUI,
  quickExportDepthSequence,
  quickExportReferenceFrame,
  type ExportPipelineOptions,
  type RenderedFrame,
} from './exportPipeline';

// Video encoder
export {
  WebCodecsVideoEncoder,
  encodeFrameSequence,
  encodeFromGenerator,
  downloadVideo,
  isWebCodecsSupported,
  getSupportedCodecs,
  type VideoEncoderConfig,
  type EncodingProgress,
  type EncodedVideo,
} from './videoEncoder';

// Model export (Light-X, TTM, Wan-Move, ATI, camera-comfyUI)
export {
  // Camera matrix export
  camera3DToMatrix4x4,
  exportCameraTrajectory,
  type CameraMatrix4x4,
  type CameraTrajectoryExport,
  // Wan-Move trajectories
  extractLayerTrajectory,
  extractSplineTrajectories,
  exportWanMoveTrajectories,
  type WanMoveTrajectoryExport,
  type PointTrajectory,
  type ParticleTrajectoryExport,
  // ATI (Any Trajectory Instruction)
  exportATITrajectory,
  calculatePanSpeed,
  type ATITrajectoryInstruction,
  type ATITrajectoryType,
  // TTM (Time-to-Move)
  exportTTMLayer,
  generateMotionMask,
  generateCombinedMotionMask,
  imageDataToBase64,
  type TTMExport,
  type TTMLayerExport,
  type TTMSingleLayerExport,
  // Light-X
  detectMotionStyle,
  type LightXExport,
  type LightXMotionStyle,
  type LightXRelightSource,
  // Unified export
  type ModelTarget,
  type UnifiedExportOptions,
  type UnifiedExportResult,
  // NPY utilities
  createNpyHeader,
  trajectoriesToNpy,
} from '../modelExport';

// Camera export (Uni3C, JSON, AE Script)
export {
  exportCameraJSON,
  importCameraJSON,
  exportToAEScript,
  downloadFile,
  type Uni3CTrack,
  type Uni3CFrame,
} from '../cameraExport';
