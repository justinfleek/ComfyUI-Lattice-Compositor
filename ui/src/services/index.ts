/**
 * Services Index
 *
 * Central export point for all service modules.
 * AUDITED: All exports verified against actual module exports.
 */

// ============================================================================
// CORE SERVICES
// ============================================================================

// Interpolation & Animation
export {
  interpolateProperty,
  EASING_PRESETS,
  EASING_PRESETS_NORMALIZED,
  createHandlesForPreset,
  applyEasingPreset,
  getBezierCurvePoint,
  getBezierCurvePointNormalized,
  applyEasing,
} from './interpolation';

// Expressions
export {
  evaluateExpression,
  easing,
  motion,
  loop,
  time,
  math,
  type ExpressionContext,
  type Expression,
} from './expressions';

// Easing functions (object-based, not individual functions)
export {
  easings,
  easingNames,
  easingGroups,
  getEasing,
  applyEasing as applyEasingByName,
  interpolateWithEasing,
  type EasingFunction,
  type EasingName,
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
  createDefaultMotionBlurSettings,
  getMotionBlurPreset,
  listMotionBlurPresets,
  MOTION_BLUR_PRESETS,
  type MotionBlurSettings,
  type MotionBlurType,
  type RadialBlurMode,
  type VelocityData,
  type MotionBlurFrame,
} from './motionBlur';

// ============================================================================
// EFFECTS
// ============================================================================

export * from './effects';

// Effect processor (functions, not a class)
export {
  registerEffectRenderer,
  evaluateEffectParameters,
  processEffectStack,
  imageDataToCanvas,
  canvasToImageData,
  createMatchingCanvas,
  hasEnabledEffects,
  getRegisteredEffects,
  type EvaluatedEffectParams,
  type EffectStackResult,
  type EffectRenderer,
} from './effectProcessor';

// ============================================================================
// AUDIO
// ============================================================================

// Audio features (functions, not classes)
export {
  loadAudioFile,
  loadAudioFromUrl,
  analyzeAudio,
  extractAmplitudeEnvelope,
  extractRMSEnergy,
  extractFrequencyBands,
  extractSpectralCentroid,
  detectOnsets,
  extractSpectralFlux,
  extractZeroCrossingRate,
  extractSpectralRolloff,
  extractSpectralFlatness,
  extractChromaFeatures,
  detectBPM,
  getFeatureAtFrame,
  getSmoothedFeature,
  normalizeFeature,
  applyFeatureCurve,
  detectPeaks,
  generatePeakGraph,
  isBeatAtFrame,
  isPeakAtFrame,
  type AudioAnalysis,
  type FrequencyBandRanges,
  type ChromaFeatures,
  type AudioAnalysisConfig,
  type PeakDetectionConfig,
  type PeakData,
} from './audioFeatures';

// Audio reactive mapping
export {
  AudioReactiveMapper,
  createDefaultAudioMapping,
  createIPAdapterSchedule,
  getIPAdapterWeightsAtFrame,
  getFeatureDisplayName,
  getTargetDisplayName,
  getAllFeatures,
  getFeaturesByCategory,
  getAllTargets,
  getTargetsByCategory,
  createSplineControlPointTargets,
  type AudioFeature,
  type TargetParameter,
  type AudioMapping,
  type IPAdapterTransition,
  type WeightSchedule,
} from './audioReactiveMapping';

// Audio path animator
export {
  AudioPathAnimator,
  createDefaultPathAnimatorConfig,
  type PathAnimatorConfig,
  type PathAnimatorState,
  type MovementMode,
} from './audioPathAnimator';

// ============================================================================
// TEXT & PATHS
// ============================================================================

// Arc length (class-based)
export {
  ArcLengthParameterizer,
  MultiSegmentParameterizer,
  pathCommandsToBezier,
  controlPointsToBeziers,
} from './arcLength';

// Text on path
export {
  TextOnPathService,
  createTextOnPathService,
  createDefaultPathConfig,
  type TextOnPathConfig,
  type PathPoint,
  type CharacterPlacement,
} from './textOnPath';

// Font service (singleton instance)
export {
  fontService,
  type FontInfo,
  type FontCategory,
} from './fontService';

// ============================================================================
// SHAPES & OPERATIONS
// ============================================================================

// Shape operations (many individual functions)
export {
  // Point operations
  distance,
  lerpPoint,
  addPoints,
  subtractPoints,
  scalePoint,
  normalize as normalizePoint,
  perpendicular,
  dot,
  cross,
  rotatePoint,
  rotateAround,
  clonePoint,
  cloneVertex,
  clonePath,
  // Bezier operations
  cubicBezierPoint,
  cubicBezierDerivative,
  splitCubicBezier,
  cubicBezierLength,
  getPathLength,
  getPointAtDistance,
  trimPath,
  mergePaths,
  // Path modifications
  offsetPath,
  offsetPathMultiple,
  puckerBloat,
  wigglePath,
  zigZagPath,
  twistPath,
  roundCorners,
  simplifyPath,
  smoothPath,
  applyRepeater,
  transformPath,
  // Shape generators
  generateRectangle,
  generateEllipse,
  generatePolygon,
  generateStar,
  // Bundled export
  ShapeOperations,
} from './shapeOperations';

// Image trace
export {
  traceImage,
  ImageTrace,
  DEFAULT_TRACE_OPTIONS,
  type TraceMode,
  type TraceOptions,
  type TraceResult,
} from './imageTrace';

// ============================================================================
// CAMERA & 3D
// ============================================================================

// Math 3D (corrected names)
export {
  // Vector operations
  vec3,
  addVec3,
  subVec3,
  scaleVec3,
  lengthVec3,
  normalizeVec3,
  crossVec3,
  dotVec3,
  lerpVec3,
  distanceVec3,
  // Matrix operations
  identityMat4,
  multiplyMat4,
  perspectiveMat4,
  orthographicMat4,
  lookAtMat4,
  translateMat4,
  rotateXMat4,
  rotateYMat4,
  rotateZMat4,
  scaleMat4,
  transformPoint,
  transformDirection,
  invertMat4,
  // Quaternion operations
  quatIdentity,
  quatFromEuler,
  quatToEuler,
  slerpQuat,
  // Utility
  focalLengthToFOV,
  fovToFocalLength,
  zoomToFocalLength,
  focalLengthToZoom,
  degToRad,
  radToDeg,
  // Types
  type Vec3,
  type Mat4,
  type Quat,
} from './math3d';

// Camera export
export {
  exportCameraJSON,
  importCameraJSON,
  exportToAEScript,
  downloadFile,
  type Uni3CTrack,
  type Uni3CFrame,
} from './cameraExport';

// Camera trajectory
export {
  sphericalToCartesian,
  cartesianToSpherical,
  getTrajectoryPosition,
  generateTrajectoryKeyframes,
  applyCameraTrajectory,
  createTrajectoryFromPreset,
  getTrajectoryDescription,
  getTrajectoryCategory,
  getTrajectoryTypesByCategory,
  DEFAULT_SPHERICAL,
  DEFAULT_TRAJECTORY,
  TRAJECTORY_PRESETS,
  type SphericalCoords,
  type TrajectoryType,
  type TrajectoryConfig,
  type TrajectoryKeyframes,
} from './cameraTrajectory';

// Camera 3D visualization
export {
  generateCameraBody,
  generateFrustum,
  generateCompositionBounds,
  generatePOILine,
  generateFocalPlane,
  generateCameraVisualization,
  getCameraViewMatrices,
  getOrthoViewMatrices,
  projectToScreen,
  generate3DAxes,
  generateGrid,
  type LineSegment,
  type CameraVisualization,
  type ViewMatrices,
} from './camera3DVisualization';

// ============================================================================
// DEPTH & SEGMENTATION
// ============================================================================

// Depthflow (corrected names - lowercase 'f')
export {
  DepthflowRenderer,
  createDefaultDepthflowConfig,
  createDefaultDOFConfig,
  createDefaultEnhancedConfig,
  createMotionComponent,
  applyEasing as applyDepthflowEasing,
  evaluateMotionComponent,
  evaluateMotionsForParameter,
  evaluateAllMotions,
  applyMotionPreset,
  getMotionPresetNames,
  getMotionPresetDescription,
  createDepthSliceMask,
  createAnimatedDepthSlice,
  createAllDepthSlices,
  cameraToDepthflowParams,
  cameraTrajToDepthflowMotions,
  evaluateCameraSyncedDepthflow,
  MOTION_PRESETS,
  DEFAULT_CAMERA_SYNC_CONFIG,
  type MotionType,
  type MotionParameter,
  type EasingType as DepthflowEasingType,
  type MotionComponent,
  type DOFConfig,
  type DepthflowEnhanced,
  type DepthflowPreset,
  type DepthflowConfig,
  type DepthflowState,
  type DepthSliceConfig,
  type CameraToDepthflowConfig,
  type CameraState,
} from './depthflow';

// Segmentation
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

// Model export
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

// Matte exporter (singleton instance)
export {
  matteExporter,
  type ExportProgress,
  type ProgressCallback,
  type ExportOptions,
  type DimensionValidation,
} from './matteExporter';

// ============================================================================
// PROJECT & STORAGE
// ============================================================================

// Project storage (functions, not a class)
export {
  saveProject,
  loadProject,
  listProjects,
  deleteProject,
  isApiAvailable,
  exportProjectAsFile,
  importProjectFromFile,
  type ProjectInfo,
  type SaveResult,
  type LoadResult,
  type ListResult,
} from './projectStorage';

// ============================================================================
// PROPERTY DRIVERS
// ============================================================================

export {
  PropertyDriverSystem,
  createPropertyDriver,
  createAudioDriver,
  createPropertyLink,
  createGearDriver,
  createAudioLightDriver,
  createAudioColorTempDriver,
  createLightFollowDriver,
  getPropertyPathDisplayName,
  getAllPropertyPaths,
  getLightPropertyPaths,
  getPropertyPathsForLayerType,
  isSplineControlPointPath,
  isLightPropertyPath,
  parseSplineControlPointPath,
  createSplineControlPointPath,
  type PropertyDriver,
  type DriverSourceType,
  type PropertyPath,
  type AudioFeatureType,
  type DriverTransform,
  type PropertyGetter,
  type PropertySetter,
} from './propertyDriver';

// ============================================================================
// TIMELINE
// ============================================================================

export {
  findNearestSnap,
  getBeatFrames,
  getPeakFrames,
  isNearBeat,
  getNearestBeatFrame,
  getSnapColor,
  DEFAULT_SNAP_CONFIG,
  type SnapType,
  type SnapResult,
  type SnapConfig,
  type SnapIndicator,
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

// ============================================================================
// 3D ASSETS & MATERIALS
// ============================================================================

// SVG Extrusion (logo workflow)
export {
  SVGExtrusionService,
  svgExtrusionService,
  createDefaultExtrusionConfig,
  createDefaultMaterialConfig as createDefaultExtrusionMaterialConfig,
  createDefaultSVGMeshParticleConfig,
  type ParsedSVGDocument,
  type ParsedSVGPath,
  type ExtrusionConfig,
  type SVGLayerConfig,
  type ExtrusionMaterialConfig,
  type SVGMeshParticleConfig,
} from './svgExtrusion';

// Mesh Particle Manager (custom mesh particles)
export {
  MeshParticleManager,
  meshParticleManager,
  createDefaultMeshParticleConfig,
  type RegisteredMeshParticle,
  type InstancedMeshParticles,
  type MeshParticleConfig,
  type MeshParticleSource,
} from './meshParticleManager';

// Sprite Sheet Service (animated particle textures)
export {
  SpriteSheetService,
  spriteSheetService,
  createDefaultParticleSpriteConfig,
  type SpriteSheetConfig,
  type SpriteFrame,
  type SpriteAnimation,
  type SpriteSheetMetadata,
  type ParticleSpriteConfig,
} from './spriteSheet';

// Material System (PBR materials and textures)
export {
  MaterialSystem,
  materialSystem,
  type PBRMaterialConfig,
  type EnvironmentConfig,
  type MaterialPreset,
} from './materialSystem';

// WebGPU Compute Particles
export {
  ParticleGPUCompute,
  HybridParticleSystem,
  type GPUParticleConfig,
  type GPUGravityWell,
  type GPUVortex,
  type GPUParticleData,
  type WebGPUCapabilities,
} from './particleGPU';
