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
  evaluateCustomExpression,
  easing,
  motion,
  loop,
  time,
  math,
  audio,
  layer,
  effect,
  vector,
  coords,
  textAnimator,
  // Vector math functions
  vectorAdd,
  vectorSub,
  vectorMul,
  vectorDiv,
  vectorNormalize,
  vectorDot,
  vectorCross,
  vectorLength,
  vectorClamp,
  // Coordinate conversion
  toComp,
  fromComp,
  toWorld,
  fromWorld,
  lookAt,
  orientToPath,
  // Text animator
  createTextAnimatorContext,
  evaluateTextAnimatorExpression,
  // Audio/time expressions
  valueAtTime,
  posterizeTime,
  linearInterp,
  easeInterp,
  // Layer dimension
  sourceRectAtTime,
  // Noise
  noise,
  degreeTrig,
  type ExpressionContext,
  type Expression,
  type LayerTransform,
  type TextAnimatorContext,
  type SourceRect,
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
  processEffectStackAsync,
  imageDataToCanvas,
  canvasToImageData,
  createMatchingCanvas,
  hasEnabledEffects,
  getRegisteredEffects,
  isGPUEffectProcessingAvailable,
  getGPUEffectCapabilities,
  clearEffectCaches,
  getEffectProcessorStats,
  cleanupEffectResources,
  type EvaluatedEffectParams,
  type EffectStackResult,
  type EffectRenderer,
  type GPUProcessingOptions,
} from './effectProcessor';

// GPU Effect Dispatcher
export {
  gpuEffectDispatcher,
  initializeGPUEffects,
  getGPUEffectStats,
  type GPURenderPath,
  type GPUCapabilityInfo,
} from './gpuEffectDispatcher';

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

// Text Shaper (OpenType/Kerning support)
export {
  textShaper,
  loadFontForShaping,
  shapeText,
  shapeTextSync,
  getCharacterWidths,
  isShapingAvailable,
  type ShapedGlyph,
  type ShapedText,
  type TextShapingOptions,
  type FontMetrics,
  type VariableFontAxis,
} from './textShaper';

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

// Bezier Boolean Operations (Paper.js based)
export {
  booleanOperation,
  unite as bezierUnite,
  subtract as bezierSubtract,
  intersect as bezierIntersect,
  exclude as bezierExclude,
  divide as bezierDivide,
  uniteAll as bezierUniteAll,
  intersectAll as bezierIntersectAll,
  simplifyPath as bezierSimplifyPath,
  flattenPath as bezierFlattenPath,
  smoothPath as bezierSmoothPath,
  getPathArea,
  getPathLength as bezierGetPathLength,
  getPointOnPath,
  getTangentOnPath,
  getNormalOnPath,
  pathsIntersect,
  getPathIntersections,
  type BooleanOperation,
  type BooleanOptions,
  type BooleanResult,
} from './bezierBoolean';

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
  // GPUParticleData already exported from gpuParticleRenderer (line 90)
  // WebGPUCapabilities exported from webgpuRenderer (line 982)
} from './particleGPU';

// ============================================================================
// TEXT TO VECTOR
// ============================================================================

export {
  textToVector,
  textLayerToSplines,
  loadFont,
  loadFontFromBuffer,
  registerFontUrl,
  clearFontCache,
  type TextToVectorResult,
  type CharacterVectorGroup,
  type TextToVectorOptions,
} from './textToVector';

// ============================================================================
// SVG EXPORT
// ============================================================================

export {
  SVGExportService,
  svgExportService,
  exportSplineLayerToSVG,
  exportCompositionToSVG,
  controlPointsToPathData,
  type SVGExportOptions,
  type SVGExportResult,
} from './svgExport';

// ============================================================================
// VECTOR LOD
// ============================================================================

export {
  VectorLODService,
  vectorLODService,
  generateLODLevels,
  selectLODLevel,
  simplifyPath as simplifyPathLOD, // Alias to avoid conflict with shapeOperations.simplifyPath
  cullOffScreenPoints,
  DEFAULT_LOD_CONFIG,
  type LODLevel,
  type LODConfig,
  type LODContext,
} from './vectorLOD';

// ============================================================================
// MESH WARP DEFORMATION
// ============================================================================

export {
  MeshWarpDeformationService,
  meshWarpDeformation,
  delaunayTriangulate,
  calculateWeights,
  deformMesh,
  // Backwards compatibility aliases (deprecated)
  PuppetDeformationService,
  puppetDeformation,
} from './meshWarpDeformation';

// ============================================================================
// 3D MESH DEFORMATION (Squash/Stretch, Bounce, 3D Pins)
// ============================================================================

export {
  MeshDeformation3DService,
  meshDeformation3D,
  calculateSquashStretch,
  calculateVelocityAtFrame,
  calculateBounceOffset,
  calculateImpactSquash,
  calculate3DPinWeight,
  deform3DPosition,
  createDefault3DPin,
  applySquashStretchToObject,
  deformGeometryWithPins,
  DEFAULT_SQUASH_STRETCH,
  DEFAULT_BOUNCE,
  type SquashStretchConfig,
  type BounceConfig,
  type Deformation3DPin,
  type Deformation3DResult,
} from './meshDeformation3D';

// ============================================================================
// IMAGE VECTORIZATION
// ============================================================================

export {
  DEFAULT_VTRACE_OPTIONS,
  DEFAULT_STARVECTOR_OPTIONS,
  VectorizeService,
  getVectorizeService,
  normalizeControlPoints,
  mergePaths as mergeVectorPaths, // Alias to avoid conflict with shapeOperations.mergePaths
  filterSmallPaths,
  simplifyPath as simplifyPathVectorize, // Alias to avoid conflict with shapeOperations.simplifyPath
  autoGroupPoints,
  type VectorizeStatus,
  type VectorPath,
  type VectorizeResult,
  type VTraceOptions,
  type StarVectorOptions,
} from './vectorize';

// ============================================================================
// AI GENERATION (Lazy-loaded models)
// ============================================================================

export {
  type AIModelType,
  type ModelStatus,
  type ModelInfo,
  type DepthEstimationOptions,
  type NormalMapOptions,
  type SegmentationOptions,
  type GenerationOptions,
  type InferenceResult,
  type SegmentationResult as AISegmentationResult, // Alias to avoid conflict with segmentation
  aiGeneration,
  estimateDepth,
  generateNormalMap,
  segmentAtPoint,
  getAvailableModels,
  isAIBackendConnected,
} from './aiGeneration';

// ============================================================================
// AUDIO WORKER CLIENT
// ============================================================================

export {
  type AudioAnalysisProgress,
  type AnalyzeOptions,
  analyzeAudioInWorker,
  loadAndAnalyzeAudio,
  cancelAnalysis,
  terminateWorker,
} from './audioWorkerClient';

// ============================================================================
// CAMERA ENHANCEMENTS
// ============================================================================

export {
  type CameraShakeConfig,
  type RackFocusConfig,
  type AutoFocusConfig,
  type MotionBlurEstimate,
  SHAKE_PRESETS,
  DEFAULT_SHAKE_CONFIG,
  DEFAULT_RACK_FOCUS,
  DEFAULT_AUTOFOCUS,
  CameraShake,
  getRackFocusDistance,
  generateRackFocusKeyframes,
  calculateAutoFocusDistance,
  estimateMotionBlur,
  generateMotionBlurKeyframes,
  createCameraShake,
  createRackFocus,
  createAutoFocus,
} from './cameraEnhancements';

// ============================================================================
// LAYER DECOMPOSITION (AI-powered)
// ============================================================================

export {
  type DecompositionModelStatus,
  type DecomposedLayer,
  type DecompositionOptions,
  type DecompositionResult,
  LayerDecompositionService,
  getLayerDecompositionService,
  canvasToDataUrl,
  imageToDataUrl,
  dataUrlToImage,
} from './layerDecomposition';

// ============================================================================
// LAYER EVALUATION CACHE
// ============================================================================

export {
  markLayerDirty,
  markAllLayersDirty,
  getLayerVersion,
  getGlobalVersion,
  getCachedEvaluation,
  setCachedEvaluation,
  clearLayerCache,
  clearEvaluationCache,
  getEvaluationCacheStats,
  evaluateLayerCached,
  evaluateLayersCached,
} from './layerEvaluationCache';

// ============================================================================
// LAZY LOADER (Dynamic module loading)
// ============================================================================

export {
  loadWebGPURenderer,
  loadMatteExporter,
  loadJSZip,
  loadMP4Muxer,
  loadWebMMuxer,
  loadParticleSystem,
  loadMath3D,
  loadCameraTrajectory,
  loadDepthflow,
  preloadCommonModules,
  preloadExportModules,
  clearModuleCache,
  clearAllModuleCache,
  getModuleCacheStats,
} from './lazyLoader';

// ============================================================================
// MASK GENERATOR
// ============================================================================

export {
  type MaskShapeType,
  type MaskGeneratorOptions,
  type AffineTransformParams,
  generateMask,
  maskToImageData,
  maskToCanvas,
  maskToDataURL,
  generateMaskSequence,
} from './maskGenerator';

// ============================================================================
// MEMORY BUDGET (GPU/VRAM tracking)
// ============================================================================

export {
  type MemoryAllocation,
  type MemoryCategory,
  type MemoryWarning,
  type GPUInfo,
  VRAM_ESTIMATES,
  totalUsageMB,
  usageByCategory,
  availableVRAM,
  usagePercent,
  warningLevel,
  allocationList,
  unloadableItems,
  initializeGPUDetection,
  registerAllocation,
  unregisterAllocation,
  updateAllocation,
  getWarning,
  canAllocate,
  freeMemory,
  getMemorySummary,
  memoryState,
} from './memoryBudget';

// ============================================================================
// PATH MORPHING
// ============================================================================

export {
  type MorphConfig,
  type PreparedMorphPaths,
  DEFAULT_MORPH_CONFIG,
  prepareMorphPaths,
  morphPaths,
  morphPathsAuto,
  getCorrespondence,
  isBezierPath,
  PathMorphing,
} from './pathMorphing';

// ============================================================================
// PERSISTENCE SERVICE (IndexedDB storage)
// ============================================================================

export {
  type StoredProject,
  type RecentProject,
  type UserSettings,
  type StoredAsset,
  type AIConversation,
  // Alias to avoid conflict with projectStorage exports
  saveProject as saveProjectIndexedDB,
  getProject as getProjectIndexedDB,
  deleteProject as deleteProjectIndexedDB,
  listProjects as listProjectsIndexedDB,
  saveAsset,
  getAsset,
  getProjectAssets,
  deleteAsset,
  deleteProjectAssets,
  saveAIConversation,
  getAIConversation,
  getProjectAIConversations,
  deleteAIConversation,
  getSettings,
  saveSettings,
  getSetting,
  setSetting,
  getRecentProjects,
  addToRecentProjects,
  removeFromRecentProjects,
  clearRecentProjects,
  getLastProjectId,
  setLastProjectId,
  getStorageEstimate,
  clearAllData,
  exportAllData,
  importData,
  initPersistence,
} from './persistenceService';

// SEGMENT TO MASK exports are already included via ./segmentation re-export (lines 423-446)

// ============================================================================
// TEXT ANIMATOR
// ============================================================================

export {
  type TextAnimatorPreset,
  DEFAULT_RANGE_SELECTOR,
  DEFAULT_ANIMATOR_PROPERTIES,
  TEXT_ANIMATOR_PRESETS,
  TEXT_ANIMATOR_PRESET_LIST,
  createTextAnimator,
  applyTextAnimatorPreset,
  calculateCharacterInfluence,
} from './textAnimator';

// ============================================================================
// WEBGPU RENDERER
// ============================================================================

export {
  type WebGPUCapabilities,
  type BlurParams,
  type ColorCorrectionParams,
  webgpuRenderer,
  getWebGPUStats,
} from './webgpuRenderer';

// ============================================================================
// ONION SKINNING
// ============================================================================

export {
  type OpacityFalloff,
  type OnionSkinConfig,
  type OnionSkinFrame,
  type OnionSkinRenderData,
  DEFAULT_ONION_SKIN_CONFIG,
  ONION_SKIN_PRESETS,
  calculateOpacity,
  parseColor,
  calculateOnionSkinFrames,
  OnionSkinningService,
  compositeOnionSkinFrame,
  onionSkinning,
} from './onionSkinning';

// ============================================================================
// GAUSSIAN SPLATTING (3DGS)
// ============================================================================

export {
  type GaussianPrimitive,
  type GaussianSplatScene,
  type GaussianRenderQuality,
  DEFAULT_QUALITY as DEFAULT_3DGS_QUALITY,
  createGaussianBuffers,
  createGaussianPoints,
  GaussianSplattingService,
  sortGaussiansByDepth,
  reorderBuffers,
  gaussianSplatting,
} from './gaussianSplatting';

// ============================================================================
// VIDEO DECODER (WebCodecs API - Phase 4)
// Frame-accurate video decoding with LRU caching
// ============================================================================

export {
  VideoDecoderService,
  videoDecoderPool,
  isWebCodecsSupported,
  type VideoInfo,
  type VideoFrameInfo,
  type VideoDecoderConfig,
  type VideoDecoderStats,
} from './videoDecoder';

// ============================================================================
// VIDEO TRANSITIONS
// (Inspired by filliptm's ComfyUI_Fill-Nodes)
// Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
// ============================================================================

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
  type TransitionState,
} from './video';

// ============================================================================
// FRAME INTERPOLATION (RIFE)
// (Inspired by filliptm's ComfyUI_Fill-Nodes, powered by RIFE)
// Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
//              https://github.com/megvii-research/ECCV2022-RIFE
// ============================================================================

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
  interpolationBase64ToBlob,

  // Presets
  INTERPOLATION_PRESETS,
  isInterpolationAvailable,
} from './video';

// ============================================================================
// AUDIO STEM SEPARATION
// (Inspired by filliptm's ComfyUI_Fill-Nodes, powered by Facebook's Demucs)
// Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
//              https://github.com/facebookresearch/demucs
// ============================================================================

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
  isStemSeparationAvailable,
} from './audio';

// ============================================================================
// ENHANCED BEAT DETECTION
// (Inspired by filliptm's ComfyUI_Fill-Nodes audio processing)
// Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
// ============================================================================

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
  isEnhancedBeatDetectionAvailable,
} from './audio';

// ============================================================================
// CAMERA TRACKING IMPORT
// ============================================================================

export {
  parseWeylTrackingJSON,
  parseBlenderTrackingJSON,
  parseCOLMAPOutput,
  detectTrackingFormat,
  importCameraTracking,
  exportCameraToTrackingFormat,
} from './cameraTrackingImport';

// ============================================================================
// TRACK POINT SERVICE
// ============================================================================

export {
  useTrackPoints,
  createTrack,
  deleteTrack,
  deleteSelectedTracks,
  setTrackPosition,
  getTrackPosition,
  removeTrackPosition,
  getTrackPositions,
  getPointsAtFrame,
  selectTrack,
  deselectTrack,
  clearSelection,
  setActiveTrack,
  setGroundPlane,
  defineGroundPlaneFromPoints,
  setOrigin3D,
  importTrackPoints2D,
  importTrackPoints3D,
  exportTrackPoints2D,
  clearAllTracks,
  getTrackStats,
  trackPointState,
} from './trackPointService';

// ============================================================================
// RENDER QUEUE (Phase 5 - Background Rendering)
// ============================================================================

export {
  RenderQueueManager,
  getRenderQueueManager,
  initializeRenderQueue,
  type RenderJobStatus,
  type RenderJobConfig,
  type RenderJobProgress,
  type RenderJob,
  type RenderedFrame,
  type RenderQueueStats,
  type RenderQueueConfig,
} from './renderQueue';

// ============================================================================
// COLOR MANAGEMENT (Phase 6 - ICC Profiles & Color Spaces)
// ============================================================================

export {
  ColorProfileService,
  getColorProfileService,
  initializeColorManagement,
  colorUtils,
  COLOR_SPACES,
  sRGBToLinear,
  linearToSRGB,
  linearizeRGB,
  applyGammaRGB,
  convertColorSpace,
  parseICCProfile,
  extractICCFromImage,
  type ColorSpace,
  type ViewTransform,
  type ColorSpaceInfo,
  type ColorSettings,
  type ICCProfile,
  type RGB as ColorRGB,
  type XYZ as ColorXYZ,
} from './colorManagement';

// ============================================================================
// TIMELINE WAVEFORM (Phase 7 - Audio Visualization)
// ============================================================================

export {
  computePeaks,
  generatePeakMipmap,
  createWaveformData,
  getWaveformData,
  clearWaveformCache,
  renderWaveform,
  renderWaveformToImage,
  renderTimelineWaveform,
  type WaveformData,
  type WaveformRenderOptions,
  type WaveformPeakOptions,
  type TimelineWaveformConfig,
} from './timelineWaveform';

// ============================================================================
// PLUGIN SYSTEM (Phase 9 - Extensibility)
// ============================================================================

export {
  PluginManager,
  getPluginManager,
  type PluginType,
  type PluginManifest,
  type PluginPermission,
  type WeylPluginAPI,
  type PluginEvent,
  type PanelDefinition,
  type MenuItemDefinition,
  type ContextMenuDefinition,
  type EffectDefinition,
  type EffectParameter,
  type ExporterDefinition,
  type ToolDefinition,
  type WeylPlugin,
  type LoadedPlugin,
} from './plugins';

// ============================================================================
// PROJECT MIGRATION (Phase 10 - Versioning)
// ============================================================================

export {
  CURRENT_SCHEMA_VERSION,
  MIN_SUPPORTED_VERSION,
  getProjectVersion,
  needsMigration,
  migrateProject,
  validateProject,
  stampProjectVersion,
  getAvailableMigrations,
  getMigrationInfo,
  type VersionedProject,
  type MigrationResult,
  type MigrationFunction,
  type Migration,
} from './projectMigration';

// ============================================================================
// ESSENTIAL GRAPHICS (Tutorial 13 - MOGRTs)
// ============================================================================

export {
  // Template management
  initializeTemplate,
  clearTemplate,
  updateTemplateMetadata,
  // Property exposure
  EXPOSABLE_PROPERTIES,
  getExposableProperties,
  addExposedProperty,
  removeExposedProperty,
  updateExposedProperty,
  reorderExposedProperties,
  // Groups
  addPropertyGroup,
  removePropertyGroup,
  movePropertyToGroup,
  reorderGroups,
  // Comments
  addComment,
  removeComment,
  updateComment,
  // Property access
  getPropertyValue,
  setPropertyValue,
  getEffectControlValue,
  getExpressionControls,
  // MOGRT export
  prepareMOGRTExport,
  exportMOGRT,
  // Validation
  validateTemplate,
  // Utilities
  getOrganizedProperties,
  isExposedProperty,
  isTemplateComment,
  type TemplateValidationResult,
  type OrganizedProperties,
} from './essentialGraphics';

// ============================================================================
// JSON VALIDATION & DATA HARDENING
// ============================================================================

export {
  // Safe JSON operations
  safeJSONParse,
  safeJSONStringify,
  // Schema validation
  validateProject,
  validateComposition,
  validateLayer,
  validateMOGRT,
  validateTemplateConfig,
  // Type guards
  isObject,
  isString,
  isNumber,
  isArray,
  isBoolean,
  // Sanitization
  sanitizeString,
  sanitizeFileName,
  deepCloneSanitized,
  // Data repair
  repairProject,
  type ValidationError,
  type ValidationResult,
} from './jsonValidation';

// ============================================================================
// TEXT MEASUREMENT (Canvas API)
// ============================================================================

export {
  measureText,
  measureMultilineText,
  measureTextLayerRect,
  measureTextWithFont,
  isFontAvailable,
  buildFontString,
  getBaselineOffset,
  getCharacterPositions,
  cleanup as cleanupTextMeasurement,
  type TextMetrics,
  type TextRect,
} from './textMeasurement';

// ============================================================================
// DATA IMPORT (Tutorial 14 - Data-Driven Animation)
// ============================================================================

export {
  // Parsing functions
  parseJSON,
  parseCSV,
  parseTSV,
  parseDataFile,
  // Asset management
  importDataAsset,
  importDataFromFile,
  getDataAsset,
  getAllDataAssets,
  removeDataAsset,
  clearDataAssets,
  reloadDataAsset,
  // Expression support
  createFootageAccessor,
  // Utilities
  extractArrayFromJSON,
  getJSONValue,
  countCSVRows,
  getUniqueColumnValues,
  sumCSVColumn,
  maxCSVColumn,
  minCSVColumn,
} from './dataImport';

// Re-export data asset types
export {
  type DataFileType,
  type DataAsset,
  type JSONDataAsset,
  type CSVDataAsset,
  type FootageDataAccessor,
  type DataParseResult,
  type CSVParseOptions,
  type JSONParseOptions,
  // Type guards
  isJSONAsset,
  isCSVAsset,
  isSupportedDataFile,
  getDataFileType,
} from '@/types/dataAsset';

// ============================================================================
// GLOBAL LIGHT (Layer Styles)
// ============================================================================

export {
  // Factory
  createDefaultGlobalLight,
  // Getters
  getGlobalLight,
  getGlobalLightAngle,
  getGlobalLightAltitude,
  getLightDirection,
  getShadowOffset,
  // Setters
  setGlobalLightAngle,
  setGlobalLightAltitude,
  setGlobalLightDirection,
  setGlobalLightSettings,
  // Animation
  enableGlobalLightAngleAnimation,
  enableGlobalLightAltitudeAnimation,
  // Cleanup
  removeGlobalLight,
  clearGlobalLightCache,
  // Serialization
  serializeGlobalLight,
  deserializeGlobalLight,
  // Constants
  DEFAULT_ANGLE as DEFAULT_GLOBAL_LIGHT_ANGLE,
  DEFAULT_ALTITUDE as DEFAULT_GLOBAL_LIGHT_ALTITUDE,
} from './globalLight';

// ============================================================================
// Export Templates (Tutorial 20)
// ============================================================================

export {
  exportTemplateService,
  type ExportTemplate,
  type ExportTemplateStore,
} from './exportTemplates';

// ============================================================================
// Project Collection (Tutorial 20)
// ============================================================================

export {
  projectCollectionService,
  type CollectionProgress,
  type CollectionOptions,
  type CollectionManifest,
} from './projectCollection';

// ============================================================================
// Roving Keyframes (Tutorial 20)
// ============================================================================

export {
  applyRovingKeyframes,
  wouldRovingChange,
  getEvenlySpacedFrames,
  calculateVelocities,
  type RovingOptions,
  type RovingResult,
} from './rovingKeyframes';

// ============================================================================
// PHYSICS SIMULATION (Feature 05 - Newton Physics)
// ============================================================================

export {
  // Main engine
  PhysicsEngine,
  vec2,
  PhysicsRandom,

  // Joint system
  JointSystem,

  // Ragdoll builder
  RagdollBuilder,
  convertRagdollToPhysics,
  extractRagdollState,
  applyRagdollState,
  HUMANOID_BONES,

  // Factory functions
  createPhysicsEngine,
  createRagdollBuilder,
  createCircleBody,
  createBoxBody,
  createGravityForce,
  createClothConfig,

  // Presets
  HUMANOID_PRESETS,
  MATERIAL_PRESETS,
  DEFAULT_SPACE_CONFIG,

  // Types
  type PhysicsVec2,
  type PhysicsMaterial,
  type CollisionShape,
  type CollisionFilter,
  type BodyType,
  type ShapeType,
  type CollisionResponse,
  type RigidBodyConfig,
  type RigidBodyState,
  type ContactInfo,
  type JointType,
  type JointConfig,
  type PivotJointConfig,
  type SpringJointConfig,
  type DistanceJointConfig,
  type PistonJointConfig,
  type WheelJointConfig,
  type WeldJointConfig,
  type BlobJointConfig,
  type RopeJointConfig,
  type ForceType,
  type ForceField,
  type GravityForce,
  type WindForce,
  type AttractionForce,
  type ExplosionForce,
  type BuoyancyForce,
  type VortexForce,
  type DragForce,
  type VerletParticle,
  type VerletConstraint,
  type SoftBodyConfig,
  type SoftBodyState,
  type ClothConfig,
  type ClothState,
  type RagdollBone,
  type RagdollConfig,
  type RagdollState,
  type HumanoidRagdollPreset,
  type PhysicsSpaceConfig,
  type PhysicsSimulationState,
  type KeyframeExportOptions,
  type ExportedKeyframes,
  type PhysicsLayerData,
  type PhysicsCompositionData,
} from './physics';
