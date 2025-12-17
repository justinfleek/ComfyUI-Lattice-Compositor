/**
 * Services Index
 *
 * Central export point for all service modules.
 * Organized by category for easier discovery.
 */

// ============================================================================
// CORE SERVICES
// ============================================================================

// Interpolation & Animation
export {
  interpolateValue,
  interpolateProperty,
  interpolateVector2,
  interpolateVector3,
  interpolateColor,
  applyEasing,
  EASING_PRESETS,
  type EasingType,
} from './interpolation';

// Expressions
export {
  evaluateExpression,
  createExpressionContext,
  easing,
  motion,
  loop,
  time,
  math,
  type ExpressionContext,
  type Expression,
} from './expressions';

// Easing functions
export {
  linear,
  easeInQuad,
  easeOutQuad,
  easeInOutQuad,
  easeInCubic,
  easeOutCubic,
  easeInOutCubic,
  easeInQuart,
  easeOutQuart,
  easeInOutQuart,
  easeInQuint,
  easeOutQuint,
  easeInOutQuint,
  easeInSine,
  easeOutSine,
  easeInOutSine,
  easeInExpo,
  easeOutExpo,
  easeInOutExpo,
  easeInCirc,
  easeOutCirc,
  easeInOutCirc,
  easeInBack,
  easeOutBack,
  easeInOutBack,
  easeInElastic,
  easeOutElastic,
  easeInOutElastic,
  easeInBounce,
  easeOutBounce,
  easeInOutBounce,
} from './easing';

// ============================================================================
// PARTICLE SYSTEM
// ============================================================================

export {
  ParticleSystem,
  SeededRandom,
  createDefaultEmitterConfig,
  createDefaultSystemConfig,
  createDefaultRenderOptions,
  createDefaultGravityWellConfig,
  createDefaultVortexConfig,
  createDefaultTurbulenceConfig,
  createDefaultSubEmitterConfig,
  createDefaultConnectionConfig,
  createDefaultCollisionConfig,
  createDefaultSpriteConfig,
  createDefaultSplinePathEmission,
  resetIdCounter,
  type Particle,
  type EmitterConfig,
  type GravityWellConfig,
  type VortexConfig,
  type ParticleModulation,
  type ParticleSystemConfig,
  type RenderOptions,
  type TurbulenceConfig,
  type ConnectionConfig,
  type SubEmitterConfig,
  type CollisionConfig,
  type SpriteConfig,
  type SplinePathEmission,
  type EmitterShape,
} from './particleSystem';

// GPU Particle Renderer
export {
  GPUParticleRenderer,
  InstancedParticleRenderer,
  createGPUParticleRenderer,
  createInstancedParticleRenderer,
  type GPUParticleRendererConfig,
  type GPUParticleData,
} from './gpuParticleRenderer';

// ============================================================================
// MOTION BLUR
// ============================================================================

export {
  MotionBlurProcessor,
  applyMotionBlur,
  createDefaultMotionBlurSettings,
  MOTION_BLUR_PRESETS,
  type MotionBlurSettings,
  type MotionBlurType,
  type ObjectTransform,
} from './motionBlur';

// ============================================================================
// EFFECTS
// ============================================================================

export * from './effects';

// Effect processor
export {
  EffectProcessor,
  type ProcessedEffectResult,
} from './effectProcessor';

// ============================================================================
// AUDIO
// ============================================================================

export {
  AudioFeatureExtractor,
  AudioSpectrumAnalyzer,
  type AudioFeatures,
  type BeatInfo,
  type SpectralFeatures,
} from './audioFeatures';

export {
  AudioReactiveMapper,
  createDefaultAudioMapping,
  type AudioMapping,
  type TargetParameter,
  type AudioMappingConfig,
} from './audioReactiveMapping';

export {
  AudioPathAnimator,
  type PathAnimationConfig,
  type PathAnimationState,
} from './audioPathAnimator';

// ============================================================================
// TEXT & PATHS
// ============================================================================

export {
  buildArcLengthLUT,
  getPointAtDistance,
  getTangentAtDistance,
  getCurvatureAtDistance,
  distributePointsEvenly,
  findClosestPointOnCurve,
  type ArcLengthLUT,
} from './arcLength';

export {
  TextOnPathEngine,
  createDefaultTextOnPathConfig,
  type TextOnPathConfig,
  type GlyphPlacement,
  type TextAnimationKeyframe,
} from './textOnPath';

export {
  FontService,
  getGlobalFontService,
  type FontInfo,
  type LoadedFont,
} from './fontService';

// ============================================================================
// SHAPES & OPERATIONS
// ============================================================================

export {
  applyBooleanOperation,
  offsetPath,
  roundCorners,
  simplifyPath,
  pathToPoints,
  pointsToPath,
  type BooleanOperation,
} from './shapeOperations';

export {
  traceImage,
  traceImageToSVG,
  type TraceOptions,
  type TracedPath,
} from './imageTrace';

// ============================================================================
// CAMERA & 3D
// ============================================================================

export {
  createViewMatrix,
  createProjectionMatrix,
  multiplyMatrices,
  invertMatrix,
  transformPoint,
  vec3Add,
  vec3Sub,
  vec3Scale,
  vec3Normalize,
  vec3Cross,
  vec3Dot,
  vec3Length,
  mat4Identity,
  mat4Translate,
  mat4RotateX,
  mat4RotateY,
  mat4RotateZ,
  mat4Scale,
  quaternionFromEuler,
  quaternionToMatrix,
  quaternionSlerp,
  type Vec3,
  type Vec4,
  type Mat4,
  type Quaternion,
} from './math3d';

export {
  exportCameraJSON,
  importCameraJSON,
  exportToAEScript,
  downloadFile,
  type Uni3CTrack,
  type Uni3CFrame,
} from './cameraExport';

export {
  CameraTrajectoryGenerator,
  createTrajectoryFromKeyframes,
  type TrajectoryConfig,
  type TrajectoryPoint,
} from './cameraTrajectory';

export {
  Camera3DVisualization,
  type CameraVisualizationConfig,
} from './camera3DVisualization';

// ============================================================================
// DEPTH & SEGMENTATION
// ============================================================================

export {
  DepthFlowGenerator,
  createDefaultDepthFlowConfig,
  type DepthFlowConfig,
  type DepthFlowResult,
} from './depthflow';

export {
  segmentImage,
  segmentByPoint,
  segmentByBox,
  segmentByMultiplePoints,
  autoSegment,
  applyMaskToImage,
  cropImage,
  extractContour,
  simplifyContour,
  fitBezierToContour,
  segmentationToMask,
  batchSegmentationToMasks,
  refineMask,
  type SegmentationPoint,
  type SegmentationRequest,
  type SegmentationMask,
  type SegmentationResult,
  type ContourOptions,
  type SimplifyOptions,
  type BezierFitOptions,
  type SegmentToMaskOptions,
} from './segmentation';

// ============================================================================
// EXPORT
// ============================================================================

export * from './export';

export {
  camera3DToMatrix4x4,
  exportCameraTrajectory,
  extractLayerTrajectory,
  extractSplineTrajectories,
  exportWanMoveTrajectories,
  exportATITrajectory,
  calculatePanSpeed,
  exportTTMLayer,
  generateMotionMask,
  generateCombinedMotionMask,
  imageDataToBase64,
  detectMotionStyle,
  createNpyHeader,
  trajectoriesToNpy,
  type CameraMatrix4x4,
  type CameraTrajectoryExport,
  type WanMoveTrajectoryExport,
  type PointTrajectory,
  type ParticleTrajectoryExport,
  type ATITrajectoryInstruction,
  type ATITrajectoryType,
  type TTMExport,
  type TTMLayerExport,
  type TTMSingleLayerExport,
  type LightXExport,
  type LightXMotionStyle,
  type LightXRelightSource,
  type ModelTarget,
  type UnifiedExportOptions,
  type UnifiedExportResult,
} from './modelExport';

export {
  MatteExporter,
  type MatteExportConfig,
  type MatteFrame,
} from './matteExporter';

// ============================================================================
// PROJECT & STORAGE
// ============================================================================

export {
  ProjectStorage,
  getProjectStorage,
  type StoredProject,
  type ProjectMetadata,
} from './projectStorage';

// ============================================================================
// PROPERTY DRIVERS
// ============================================================================

export {
  PropertyDriverEngine,
  createDefaultDriverConfig,
  type PropertyDriver,
  type DriverType,
  type DriverConfig,
} from './propertyDriver';

// ============================================================================
// TIMELINE
// ============================================================================

export {
  TimelineSnapService,
  type SnapResult,
  type SnapConfig,
} from './timelineSnap';

// ============================================================================
// GPU & PERFORMANCE
// ============================================================================

export {
  detectGPUTier,
  type GPUTier,
} from './gpuDetection';

export {
  FrameCache,
  getFrameCache,
  initializeFrameCache,
  type CachedFrame,
  type FrameCacheConfig,
  type CacheStats,
} from './frameCache';

export {
  WorkerPool,
  getWorkerPool,
  disposeWorkerPool,
  type WorkerPoolConfig,
} from './workerPool';
