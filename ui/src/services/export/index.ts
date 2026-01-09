/**
 * Export Services Index
 * Central export point for all export-related services
 */

// Re-export camera types from their source
export type { CameraKeyframe } from "@/types/camera";
export type { FullCameraExport as ExportOptions } from "@/types/export";
// Camera export (Uni3C, JSON, AE Script)
export {
  downloadFile,
  exportCameraJSON,
  exportToAEScript,
  importCameraJSON,
  type Uni3CFrame,
  type Uni3CTrack,
} from "../cameraExport";
// Color Management (Phase 6)
export {
  applyGammaRGB,
  COLOR_SPACES,
  ColorProfileService,
  type ColorSettings,
  type ColorSpace,
  colorUtils,
  convertColorSpace,
  extractICCFromImage,
  getColorProfileService,
  type ICCProfile,
  initializeColorManagement,
  linearizeRGB,
  parseICCProfile,
  type RGB,
  type ViewTransform,
  type XYZ,
} from "../colorManagement/ColorProfileService";
// Model export (Light-X, TTM, Wan-Move, ATI, camera-comfyUI)
export {
  type ATITrajectoryInstruction,
  type ATITrajectoryType,
  type CameraMatrix4x4,
  type CameraTrajectoryExport,
  calculatePanSpeed,
  // Camera matrix export
  camera3DToMatrix4x4,
  // NPY utilities
  createNpyHeader,
  // Light-X
  detectMotionStyle,
  // ATI (Any Trajectory Instruction)
  exportATITrajectory,
  exportCameraTrajectory,
  // TTM (Time-to-Move)
  exportTTMLayer,
  exportWanMoveTrajectories,
  // Wan-Move trajectories
  extractLayerTrajectory,
  extractSplineTrajectories,
  generateCombinedMotionMask,
  generateMotionMask,
  imageDataToBase64,
  type LightXExport,
  type LightXMotionStyle,
  type LightXRelightSource,
  // Unified export
  type ModelTarget,
  type ParticleTrajectoryExport,
  type PointTrajectory,
  type TTMExport,
  type TTMLayerExport,
  type TTMSingleLayerExport,
  trajectoriesToNpy,
  type UnifiedExportOptions,
  type UnifiedExportResult,
  type WanMoveTrajectoryExport,
} from "../modelExport";
// Camera export formats
export {
  computeProjectionMatrix,
  computeViewMatrix,
  exportCameraForTarget,
  exportCameraMatrices,
  exportToCameraCtrl,
  exportToMotionCtrl,
  exportToMotionCtrlSVD,
  exportToUni3C,
  interpolateCameraAtFrame,
  mapToWan22FunCamera,
} from "./cameraExportFormats";
// Depth rendering
export {
  applyColormap,
  convertDepthToFormat,
  depthToImageData,
  exportDepthSequence,
  generateDepthMetadata,
  renderDepthFrame,
} from "./depthRenderer";
// Export pipeline
export {
  ExportPipeline,
  type ExportPipelineOptions,
  exportToComfyUI,
  quickExportDepthSequence,
  quickExportReferenceFrame,
  type RenderedFrame,
} from "./exportPipeline";
// Mesh Deform Export (Pin trajectories, overlap depth, motion masks)
export {
  type CompositionInfo,
  // Types
  type DepthFormat,
  depthBufferToImageData,
  // Motion mask export (TTM)
  exportDeformedMeshMask,
  exportDeformedMeshMaskBinary,
  exportMeshMaskSequence,
  // Overlap depth export (ControlNet)
  exportOverlapAsDepth,
  exportOverlapDepthSequence,
  exportPinPositionsPerFrame,
  // Pin trajectory export (Wan-Move/ATI)
  exportPinsAsTrajectory,
  exportPinsAsTrajectoryWithMetadata,
} from "./meshDeformExport";
// ControlNet Pose Export
export {
  createDefaultPoseExportConfig,
  createPoseSequence,
  exportPoseForControlNet,
  exportPoseSequence,
  exportToOpenPoseJSON,
  importFromOpenPoseJSON,
  importPoseSequence,
  type OpenPoseJSON,
  type PoseExportConfig,
  type PoseExportResult,
  type PoseFrame,
  type PoseSequence,
  renderPoseFrame,
} from "./poseExport";

// VACE Control Video Export (shapes following splines)
export {
  calculateDurationForSpeed,
  calculateSpeed,
  createPathFollower,
  createVACEExportConfig,
  PathFollower,
  type PathFollowerConfig,
  type PathFollowerEasing,
  type PathFollowerShape,
  type PathFollowerState,
  splineLayerToPathFollower,
  VACEControlExporter,
  type VACEExportConfig,
  type VACEFrame,
} from "./vaceControlExport";
// Video encoder
export {
  downloadVideo,
  type EncodedVideo,
  type EncodingProgress,
  encodeFrameSequence,
  encodeFromGenerator,
  getSupportedCodecs,
  isWebCodecsSupported,
  type VideoEncoderConfig,
  WebCodecsVideoEncoder,
} from "./videoEncoder";
// Wan-Move generative trajectory generation
export {
  ATTRACTOR_PRESETS,
  type AttractorConfig,
  // Color mapping
  addColorToTrajectory,
  addTimeColorToTrajectory,
  COLOR_GRADIENTS,
  type ColoredTrajectory,
  type ColorGradient,
  compositeColoredLayers,
  // Multi-layer composition
  compositeFlowLayers,
  type DataDrivenFlowConfig,
  // Export functions
  exportAsJSON as exportWanMoveJSON,
  exportAsNPYData as exportWanMoveNPY,
  exportWanMovePackage,
  // Presets
  FLOW_PRESETS,
  type FlowLayer,
  type ForceFieldConfig,
  type ForcePoint,
  type GenerativeFlowConfig,
  type GenerativeFlowParams,
  generateAizawaAttractor,
  generateDataDrivenFlow,
  generateDataRiverFlow,
  generateExplosionFlow,
  // Force fields
  generateForceFieldFlow,
  generateFromPreset as generateFlowPreset,
  // Strange attractors
  generateLorenzAttractor,
  generateMorphFlow,
  generateRosslerAttractor,
  // Shape morphing
  generateShapeMorph,
  // Basic flow generators
  generateSpiralFlow,
  generateSplineFlow,
  generateSwarmFlow,
  generateVortexFlow,
  generateWaveFlow,
  type RenderOptions,
  // Rendering/preview
  renderTrajectoryFrame,
  renderTrajectorySequence,
  SHAPE_PRESETS,
  type ShapeDefinition,
  type ShapeTargetConfig,
  sampleGradient,
  // Types
  type WanMoveTrajectory,
} from "./wanMoveExport";
