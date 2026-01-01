/**
 * Export Services Index
 * Central export point for all export-related services
 */

// Color Management (Phase 6)
export {
  ColorProfileService,
  getColorProfileService,
  initializeColorManagement,
  convertColorSpace,
  linearizeRGB,
  applyGammaRGB,
  parseICCProfile,
  extractICCFromImage,
  COLOR_SPACES,
  colorUtils,
  type ColorSpace,
  type ViewTransform,
  type ColorSettings,
  type ICCProfile,
  type RGB,
  type XYZ,
} from '../colorManagement/ColorProfileService';

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

// Wan-Move generative trajectory generation
export {
  // Basic flow generators
  generateSpiralFlow,
  generateWaveFlow,
  generateExplosionFlow,
  generateVortexFlow,
  generateDataRiverFlow,
  generateMorphFlow,
  generateSwarmFlow,
  generateDataDrivenFlow,
  generateSplineFlow,
  // Strange attractors
  generateLorenzAttractor,
  generateRosslerAttractor,
  generateAizawaAttractor,
  // Shape morphing
  generateShapeMorph,
  // Force fields
  generateForceFieldFlow,
  // Multi-layer composition
  compositeFlowLayers,
  compositeColoredLayers,
  // Color mapping
  addColorToTrajectory,
  addTimeColorToTrajectory,
  sampleGradient,
  COLOR_GRADIENTS,
  // Rendering/preview
  renderTrajectoryFrame,
  renderTrajectorySequence,
  // Export functions
  exportAsJSON as exportWanMoveJSON,
  exportAsNPYData as exportWanMoveNPY,
  exportWanMovePackage,
  // Presets
  FLOW_PRESETS,
  ATTRACTOR_PRESETS,
  SHAPE_PRESETS,
  generateFromPreset as generateFlowPreset,
  // Types
  type WanMoveTrajectory,
  type ColoredTrajectory,
  type GenerativeFlowConfig,
  type GenerativeFlowParams,
  type DataDrivenFlowConfig,
  type AttractorConfig,
  type ShapeTargetConfig,
  type ShapeDefinition,
  type ForcePoint,
  type ForceFieldConfig,
  type FlowLayer,
  type ColorGradient,
  type RenderOptions,
} from './wanMoveExport';

// VACE Control Video Export (shapes following splines)
export {
  PathFollower,
  VACEControlExporter,
  createPathFollower,
  createVACEExportConfig,
  calculateDurationForSpeed,
  calculateSpeed,
  splineLayerToPathFollower,
  type PathFollowerShape,
  type PathFollowerEasing,
  type PathFollowerConfig,
  type PathFollowerState,
  type VACEExportConfig,
  type VACEFrame,
} from './vaceControlExport';

// ControlNet Pose Export
export {
  renderPoseFrame,
  createPoseSequence,
  exportToOpenPoseJSON,
  exportPoseSequence,
  exportPoseForControlNet,
  importFromOpenPoseJSON,
  importPoseSequence,
  createDefaultPoseExportConfig,
  type PoseExportConfig,
  type PoseFrame,
  type PoseSequence,
  type OpenPoseJSON,
  type PoseExportResult,
} from './poseExport';

// Mesh Deform Export (Pin trajectories, overlap depth, motion masks)
export {
  // Pin trajectory export (Wan-Move/ATI)
  exportPinsAsTrajectory,
  exportPinsAsTrajectoryWithMetadata,
  exportPinPositionsPerFrame,
  // Overlap depth export (ControlNet)
  exportOverlapAsDepth,
  depthBufferToImageData,
  exportOverlapDepthSequence,
  // Motion mask export (TTM)
  exportDeformedMeshMask,
  exportDeformedMeshMaskBinary,
  exportMeshMaskSequence,
  // Types
  type DepthFormat,
  type CompositionInfo,
} from './meshDeformExport';
