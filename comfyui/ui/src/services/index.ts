/**
 * Services Index
 *
 * ⚠️ DEPRECATED - DO NOT USE ⚠️
 * ==============================
 * 
 * This barrel file is deprecated and will be removed in a future version.
 * 
 * **Why deprecated:**
 * - Not used by any code (0 imports found)
 * - Causes circular dependency issues
 * - Increases bundle size (tree-shaking problems)
 * - Makes imports ambiguous
 * 
 * **Use direct imports instead:**
 * ```typescript
 * // ❌ DEPRECATED - Don't use this:
 * import { loadAudio } from '@/services';
 * 
 * // ✅ CORRECT - Use direct imports:
 * import { loadAudio } from '@/services/audioFeatures';
 * import { interpolateProperty } from '@/services/interpolation';
 * ```
 * 
 * **Migration:**
 * All existing code already uses direct imports. This file exists only for
 * historical reference and will be removed in Phase 7 of the refactor.
 * 
 * @deprecated Use direct imports from specific service modules instead
 * @see docs/MASTER_REFACTOR_PLAN.md Appendix B
 * @see docs/FILES_OVER_800_LINES_AUDIT.md
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // core // services
// ═══════════════════════════════════════════════════════════════════════════

// Easing functions (object-based, not individual functions)
export {
  applyEasing as applyEasingByName,
  type EasingFunction,
  type EasingName,
  easingGroups,
  easingNames,
  easings,
  getEasing,
  interpolateWithEasing,
} from "./easing";

// Expressions
export {
  audio,
  coords,
  // Text animator
  createTextAnimatorContext,
  degreeTrig,
  type Expression,
  type ExpressionContext,
  easeInterp,
  easing,
  effect,
  evaluateCustomExpression,
  evaluateExpression,
  evaluateTextAnimatorExpression,
  fromComp,
  fromWorld,
  type LayerTransform,
  layer,
  linearInterp,
  lookAt,
  loop,
  math,
  motion,
  // Noise
  noise,
  orientToPath,
  posterizeTime,
  type SourceRect,
  // Layer dimension
  sourceRectAtTime,
  type TextAnimatorContext,
  textAnimator,
  time,
  // Coordinate conversion
  toComp,
  toWorld,
  // Audio/time expressions
  valueAtTime,
  vector,
  // Vector math functions
  vectorAdd,
  vectorClamp,
  vectorCross,
  vectorDiv,
  vectorDot,
  vectorLength,
  vectorMul,
  vectorNormalize,
  vectorSub,
} from "./expressions";
// Interpolation & Animation
export {
  applyEasing,
  applyEasingPreset,
  createHandlesForPreset,
  EASING_PRESETS,
  EASING_PRESETS_NORMALIZED,
  getBezierCurvePoint,
  getBezierCurvePointNormalized,
  interpolateProperty,
} from "./interpolation";

// ═══════════════════════════════════════════════════════════════════════════
//                                                       // particle // system
// ═══════════════════════════════════════════════════════════════════════════

// GPU Particle Renderer
export {
  createGPUParticleRenderer,
  createInstancedParticleRenderer,
  type GPUParticleData,
  GPUParticleRenderer,
  type GPUParticleRendererConfig,
  InstancedParticleRenderer,
} from "./gpuParticleRenderer";
export {
  type CollisionConfig,
  type ConnectionConfig,
  createDefaultCollisionConfig,
  createDefaultConnectionConfig,
  createDefaultEmitterConfig,
  createDefaultGravityWellConfig,
  createDefaultRenderOptions,
  createDefaultSplinePathEmission,
  createDefaultSpriteConfig,
  createDefaultSubEmitterConfig,
  createDefaultSystemConfig,
  createDefaultTurbulenceConfig,
  createDefaultVortexConfig,
  type EmitterConfig,
  type EmitterShape,
  type GravityWellConfig,
  type Particle,
  type ParticleModulation,
  ParticleSystem,
  type ParticleSystemConfig,
  type RenderOptions,
  resetIdCounter,
  SeededRandom,
  type SplinePathEmission,
  type SpriteConfig,
  type SubEmitterConfig,
  type TurbulenceConfig,
  type VortexConfig,
} from "./particleSystem";

// ═══════════════════════════════════════════════════════════════════════════
//                                                           // motion // blur
// ═══════════════════════════════════════════════════════════════════════════

export {
  createDefaultMotionBlurSettings,
  getMotionBlurPreset,
  listMotionBlurPresets,
  MOTION_BLUR_PRESETS,
  type MotionBlurFrame,
  MotionBlurProcessor,
  type MotionBlurSettings,
  type MotionBlurType,
  type RadialBlurMode,
  type VelocityData,
} from "./motionBlur";

// ═══════════════════════════════════════════════════════════════════════════
//                                                                  // effects
// ═══════════════════════════════════════════════════════════════════════════

// Effect processor (functions, not a class)
export {
  canvasToImageData,
  cleanupEffectResources,
  clearEffectCaches,
  createMatchingCanvas,
  type EffectRenderer,
  type EffectStackResult,
  type EvaluatedEffectParams,
  evaluateEffectParameters,
  type GPUProcessingOptions,
  getEffectProcessorStats,
  getGPUEffectCapabilities,
  getRegisteredEffects,
  hasEnabledEffects,
  imageDataToCanvas,
  isGPUEffectProcessingAvailable,
  processEffectStack,
  processEffectStackAsync,
  registerEffectRenderer,
} from "./effectProcessor";
export * from "./effects";

// GPU Effect Dispatcher
export {
  type GPUCapabilityInfo,
  type GPURenderPath,
  getGPUEffectStats,
  gpuEffectDispatcher,
  initializeGPUEffects,
} from "./gpuEffectDispatcher";

// ═══════════════════════════════════════════════════════════════════════════
//                                                                    // audio
// ═══════════════════════════════════════════════════════════════════════════

// Audio features (functions, not classes)
export {
  type AudioAnalysis,
  type AudioAnalysisConfig,
  analyzeAudio,
  applyFeatureCurve,
  type ChromaFeatures,
  detectBPM,
  detectOnsets,
  detectPeaks,
  extractAmplitudeEnvelope,
  extractChromaFeatures,
  extractFrequencyBands,
  extractRMSEnergy,
  extractSpectralCentroid,
  extractSpectralFlatness,
  extractSpectralFlux,
  extractSpectralRolloff,
  extractZeroCrossingRate,
  type FrequencyBandRanges,
  generatePeakGraph,
  getFeatureAtFrame,
  getSmoothedFeature,
  isBeatAtFrame,
  isPeakAtFrame,
  loadAudioFile,
  loadAudioFromUrl,
  normalizeFeature,
  type PeakData,
  type PeakDetectionConfig,
} from "./audioFeatures";
// Audio path animator
export {
  AudioPathAnimator,
  createDefaultPathAnimatorConfig,
  type MovementMode,
  type PathAnimatorConfig,
  type PathAnimatorState,
} from "./audioPathAnimator";
// Audio reactive mapping
export {
  type AudioFeature,
  type AudioMapping,
  AudioReactiveMapper,
  createDefaultAudioMapping,
  createIPAdapterSchedule,
  createSplineControlPointTargets,
  getAllFeatures,
  getAllTargets,
  getFeatureDisplayName,
  getFeaturesByCategory,
  getIPAdapterWeightsAtFrame,
  getTargetDisplayName,
  getTargetsByCategory,
  type IPAdapterTransition,
  type TargetParameter,
  type WeightSchedule,
} from "./audioReactiveMapping";

// ═══════════════════════════════════════════════════════════════════════════
// TEXT & PATHS
// ═══════════════════════════════════════════════════════════════════════════

// Arc length (class-based)
export {
  ArcLengthParameterizer,
  controlPointsToBeziers,
  MultiSegmentParameterizer,
  pathCommandsToBezier,
} from "./arcLength";
// Font service (singleton instance)
export {
  type FontCategory,
  type FontInfo,
  fontService,
} from "./fontService";
// Text on path
export {
  type CharacterPlacement,
  createDefaultPathConfig,
  createTextOnPathService,
  type PathPoint,
  type TextOnPathConfig,
  TextOnPathService,
} from "./textOnPath";

// Text Shaper (OpenType/Kerning support)
export {
  type FontMetrics,
  getCharacterWidths,
  isShapingAvailable,
  loadFontForShaping,
  type ShapedGlyph,
  type ShapedText,
  shapeText,
  shapeTextSync,
  type TextShapingOptions,
  textShaper,
  type VariableFontAxis,
} from "./textShaper";

// ═══════════════════════════════════════════════════════════════════════════
// SHAPES & OPERATIONS
// ═══════════════════════════════════════════════════════════════════════════

// Bezier Boolean Operations (Paper.js based)
export {
  type BooleanOperation,
  type BooleanOptions,
  type BooleanResult,
  booleanOperation,
  divide as bezierDivide,
  exclude as bezierExclude,
  flattenPath as bezierFlattenPath,
  getNormalOnPath,
  getPathArea,
  getPathIntersections,
  getPathLength as bezierGetPathLength,
  getPointOnPath,
  getTangentOnPath,
  intersect as bezierIntersect,
  intersectAll as bezierIntersectAll,
  pathsIntersect,
  simplifyPath as bezierSimplifyPath,
  smoothPath as bezierSmoothPath,
  subtract as bezierSubtract,
  unite as bezierUnite,
  uniteAll as bezierUniteAll,
} from "./bezierBoolean";
// Image trace
export {
  DEFAULT_TRACE_OPTIONS,
  ImageTrace,
  type TraceMode,
  type TraceOptions,
  type TraceResult,
  traceImage,
} from "./imageTrace";
// Shape operations (many individual functions)
export {
  addPoints,
  applyRepeater,
  clonePath,
  clonePoint,
  cloneVertex,
  cross,
  cubicBezierDerivative,
  cubicBezierLength,
  // Bezier operations
  cubicBezierPoint,
  // Point operations
  distance,
  dot,
  generateEllipse,
  generatePolygon,
  // Shape generators
  generateRectangle,
  generateStar,
  getPathLength,
  getPointAtDistance,
  lerpPoint,
  mergePaths,
  normalize as normalizePoint,
  // Path modifications
  offsetPath,
  offsetPathMultiple,
  perpendicular,
  puckerBloat,
  rotateAround,
  rotatePoint,
  roundCorners,
  // Bundled export
  ShapeOperations,
  scalePoint,
  simplifyPath,
  smoothPath,
  splitCubicBezier,
  subtractPoints,
  transformPath,
  trimPath,
  twistPath,
  wigglePath,
  zigZagPath,
} from "./shapeOperations";

// ═══════════════════════════════════════════════════════════════════════════
// CAMERA & 3D
// ═══════════════════════════════════════════════════════════════════════════

// Camera 3D visualization
export {
  type CameraVisualization,
  generate3DAxes,
  generateCameraBody,
  generateCameraVisualization,
  generateCompositionBounds,
  generateFocalPlane,
  generateFrustum,
  generateGrid,
  generatePOILine,
  getCameraViewMatrices,
  getOrthoViewMatrices,
  type LineSegment,
  projectToScreen,
  type ViewMatrices,
} from "./camera3DVisualization";

// Camera export
export {
  downloadFile,
  exportCameraJSON,
  exportToAEScript,
  importCameraJSON,
  type Uni3CFrame,
  type Uni3CTrack,
} from "./cameraExport";

// Camera trajectory
export {
  applyCameraTrajectory,
  cartesianToSpherical,
  createTrajectoryFromPreset,
  DEFAULT_SPHERICAL,
  DEFAULT_TRAJECTORY,
  generateTrajectoryKeyframes,
  getTrajectoryCategory,
  getTrajectoryDescription,
  getTrajectoryPosition,
  getTrajectoryTypesByCategory,
  type SphericalCoords,
  sphericalToCartesian,
  TRAJECTORY_PRESETS,
  type TrajectoryConfig,
  type TrajectoryKeyframes,
  type TrajectoryType,
} from "./cameraTrajectory";
// Math 3D (corrected names)
export {
  addVec3,
  crossVec3,
  degToRad,
  distanceVec3,
  dotVec3,
  // Utility
  focalLengthToFOV,
  focalLengthToZoom,
  fovToFocalLength,
  // Matrix operations
  identityMat4,
  invertMat4,
  lengthVec3,
  lerpVec3,
  lookAtMat4,
  type Mat4,
  multiplyMat4,
  normalizeVec3,
  orthographicMat4,
  perspectiveMat4,
  type Quat,
  quatFromEuler,
  // Quaternion operations
  quatIdentity,
  quatToEuler,
  radToDeg,
  rotateXMat4,
  rotateYMat4,
  rotateZMat4,
  scaleMat4,
  scaleVec3,
  slerpQuat,
  subVec3,
  transformDirection,
  transformPoint,
  translateMat4,
  // Types
  type Vec3,
  // Vector operations
  vec3,
  zoomToFocalLength,
} from "./math3d";

// ═══════════════════════════════════════════════════════════════════════════
// DEPTH & SEGMENTATION
// ═══════════════════════════════════════════════════════════════════════════

// Depthflow (corrected names - lowercase 'f')
export {
  applyEasing as applyDepthflowEasing,
  applyMotionPreset,
  type CameraState,
  type CameraToDepthflowConfig,
  cameraToDepthflowParams,
  cameraTrajToDepthflowMotions,
  createAllDepthSlices,
  createAnimatedDepthSlice,
  createDefaultDepthflowConfig,
  createDefaultDOFConfig,
  createDefaultEnhancedConfig,
  createDepthSliceMask,
  createMotionComponent,
  DEFAULT_CAMERA_SYNC_CONFIG,
  type DepthflowConfig,
  type DepthflowEnhanced,
  type DepthflowPreset,
  DepthflowRenderer,
  type DepthflowState,
  type DepthSliceConfig,
  type DOFConfig,
  type EasingType as DepthflowEasingType,
  evaluateAllMotions,
  evaluateCameraSyncedDepthflow,
  evaluateMotionComponent,
  evaluateMotionsForParameter,
  getMotionPresetDescription,
  getMotionPresetNames,
  MOTION_PRESETS,
  type MotionComponent,
  type MotionParameter,
  type MotionType,
} from "./depthflow";

// Segmentation
export {
  applyMaskToImage,
  autoSegment,
  type BezierFitOptions,
  batchSegmentationToMasks,
  type ContourOptions,
  cropImage,
  extractContour,
  fitBezierToContour,
  refineMask,
  type SegmentationMask,
  type SegmentationPoint,
  type SegmentationRequest,
  type SegmentationResult,
  type SegmentToMaskOptions,
  type SimplifyOptions,
  segmentationToMask,
  segmentByBox,
  segmentByMultiplePoints,
  segmentByPoint,
  segmentImage,
  simplifyContour,
} from "./segmentation";

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // export
// ═══════════════════════════════════════════════════════════════════════════

export * from "./export";
// Matte exporter (singleton instance)
export {
  type DimensionValidation,
  type ExportOptions,
  type ExportProgress,
  matteExporter,
  type ProgressCallback,
} from "./matteExporter";
// Model export
export {
  type CameraMatrix4x4,
  type CameraTrajectoryExport,
  camera3DToMatrix4x4,
  convertPointTrajectoriesToWanMove,
  createNpyHeader,
  detectMotionStyle,
  exportCameraTrajectory,
  exportTTMLayer,
  extractLayerTrajectory,
  extractSplineTrajectories,
  generateCombinedMotionMask,
  generateMotionMask,
  imageDataToBase64,
  type LightXExport,
  type LightXMotionStyle,
  type LightXRelightSource,
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
} from "./modelExport";

// ═══════════════════════════════════════════════════════════════════════════
// PROJECT & STORAGE
// ═══════════════════════════════════════════════════════════════════════════

// Project storage (functions, not a class)
export {
  deleteProject,
  exportProjectAsFile,
  importProjectFromFile,
  isApiAvailable,
  type ListResult,
  type LoadResult,
  listProjects,
  loadProject,
  type ProjectInfo,
  type SaveResult,
  saveProject,
} from "./projectStorage";

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // property // drivers
// ═══════════════════════════════════════════════════════════════════════════

export {
  type AudioFeatureType,
  createAudioColorTempDriver,
  createAudioDriver,
  createAudioLightDriver,
  createGearDriver,
  createLightFollowDriver,
  createPropertyDriver,
  createPropertyLink,
  createSplineControlPointPath,
  type DriverSourceType,
  type DriverTransform,
  getAllPropertyPaths,
  getLightPropertyPaths,
  getPropertyPathDisplayName,
  getPropertyPathsForLayerType,
  isLightPropertyPath,
  isSplineControlPointPath,
  type PropertyDriver,
  PropertyDriverSystem,
  type PropertyGetter,
  type PropertyPath,
  type PropertySetter,
  parseSplineControlPointPath,
} from "./propertyDriver";

// ═══════════════════════════════════════════════════════════════════════════
//                                                                 // timeline
// ═══════════════════════════════════════════════════════════════════════════

export {
  DEFAULT_SNAP_CONFIG,
  findNearestSnap,
  getBeatFrames,
  getNearestBeatFrame,
  getPeakFrames,
  getSnapColor,
  isNearBeat,
  type SnapConfig,
  type SnapIndicator,
  type SnapResult,
  type SnapType,
} from "./timelineSnap";

// ═══════════════════════════════════════════════════════════════════════════
// GPU & PERFORMANCE
// ═══════════════════════════════════════════════════════════════════════════

export {
  type CachedFrame,
  type CacheStats,
  FrameCache,
  type FrameCacheConfig,
  getFrameCache,
  initializeFrameCache,
} from "./frameCache";
export {
  detectGPUTier,
  type GPUTier,
} from "./gpuDetection";

export {
  disposeWorkerPool,
  getWorkerPool,
  WorkerPool,
  type WorkerPoolConfig,
} from "./workerPool";

// ═══════════════════════════════════════════════════════════════════════════
// 3D ASSETS & MATERIALS
// ═══════════════════════════════════════════════════════════════════════════

// Material System (PBR materials and textures)
export {
  type EnvironmentConfig,
  type MaterialPreset,
  MaterialSystem,
  materialSystem,
  type PBRMaterialConfig,
} from "./materialSystem";

// Mesh Particle Manager (custom mesh particles)
export {
  createDefaultMeshParticleConfig,
  type InstancedMeshParticles,
  type MeshParticleConfig,
  MeshParticleManager,
  type MeshParticleSource,
  meshParticleManager,
  type RegisteredMeshParticle,
} from "./meshParticleManager";
// WebGPU Compute Particles
export {
  type GPUGravityWell,
  type GPUParticleConfig,
  type GPUVortex,
  HybridParticleSystem,
  ParticleGPUCompute,
  // GPUParticleData already exported from gpuParticleRenderer (line 90)
  // WebGPUCapabilities exported from webgpuRenderer (line 982)
} from "./particleGPU";
// Sprite Sheet Service (animated particle textures)
export {
  createDefaultParticleSpriteConfig,
  type ParticleSpriteConfig,
  type SpriteAnimation,
  type SpriteFrame,
  type SpriteSheetConfig,
  type SpriteSheetMetadata,
  SpriteSheetService,
  spriteSheetService,
} from "./spriteSheet";
// SVG Extrusion (logo workflow)
export {
  createDefaultExtrusionConfig,
  createDefaultMaterialConfig as createDefaultExtrusionMaterialConfig,
  createDefaultSVGMeshParticleConfig,
  type ExtrusionConfig,
  type ExtrusionMaterialConfig,
  type ParsedSVGDocument,
  type ParsedSVGPath,
  SVGExtrusionService,
  type SVGLayerConfig,
  type SVGMeshParticleConfig,
  svgExtrusionService,
} from "./svgExtrusion";

// ═══════════════════════════════════════════════════════════════════════════
//                                                     // text // to // vector
// ═══════════════════════════════════════════════════════════════════════════

export {
  type CharacterVectorGroup,
  clearFontCache,
  loadFont,
  loadFontFromBuffer,
  registerFontUrl,
  type TextToVectorOptions,
  type TextToVectorResult,
  textLayerToSplines,
  textToVector,
} from "./textToVector";

// ═══════════════════════════════════════════════════════════════════════════
//                                                            // svg // export
// ═══════════════════════════════════════════════════════════════════════════

export {
  controlPointsToPathData,
  exportCompositionToSVG,
  exportSplineLayerToSVG,
  type SVGExportOptions,
  type SVGExportResult,
  SVGExportService,
  svgExportService,
} from "./svgExport";

// ═══════════════════════════════════════════════════════════════════════════
//                                                            // vector // lod
// ═══════════════════════════════════════════════════════════════════════════

export {
  cullOffScreenPoints,
  DEFAULT_LOD_CONFIG,
  generateLODLevels,
  type LODConfig,
  type LODContext,
  type LODLevel,
  selectLODLevel,
  simplifyPath as simplifyPathLOD, // Alias to avoid conflict with shapeOperations.simplifyPath
  VectorLODService,
  vectorLODService,
} from "./vectorLOD";

// ═══════════════════════════════════════════════════════════════════════════
//                                              // mesh // warp // deformation
// ═══════════════════════════════════════════════════════════════════════════

export {
  calculateWeights,
  deformMesh,
  delaunayTriangulate,
  MeshWarpDeformationService,
  meshWarpDeformation,
  // Backwards compatibility aliases (deprecated)
  PuppetDeformationService,
  puppetDeformation,
} from "./meshWarpDeformation";

// ═══════════════════════════════════════════════════════════════════════════
// 3D MESH DEFORMATION (Squash/Stretch, Bounce, 3D Pins)
// ═══════════════════════════════════════════════════════════════════════════

export {
  applySquashStretchToObject,
  type BounceConfig,
  calculate3DPinWeight,
  calculateBounceOffset,
  calculateImpactSquash,
  calculateSquashStretch,
  calculateVelocityAtFrame,
  createDefault3DPin,
  DEFAULT_BOUNCE,
  DEFAULT_SQUASH_STRETCH,
  type Deformation3DPin,
  type Deformation3DResult,
  deform3DPosition,
  deformGeometryWithPins,
  MeshDeformation3DService,
  meshDeformation3D,
  type SquashStretchConfig,
} from "./meshDeformation3D";

// ═══════════════════════════════════════════════════════════════════════════
//                                                   // image // vectorization
// ═══════════════════════════════════════════════════════════════════════════

export {
  autoGroupPoints,
  DEFAULT_STARVECTOR_OPTIONS,
  DEFAULT_VTRACE_OPTIONS,
  filterSmallPaths,
  getVectorizeService,
  mergePaths as mergeVectorPaths, // Alias to avoid conflict with shapeOperations.mergePaths
  normalizeControlPoints,
  type StarVectorOptions,
  simplifyPath as simplifyPathVectorize, // Alias to avoid conflict with shapeOperations.simplifyPath
  type VectorizeResult,
  VectorizeService,
  type VectorizeStatus,
  type VectorPath,
  type VTraceOptions,
} from "./vectorize";

// ═══════════════════════════════════════════════════════════════════════════
// AI GENERATION (Lazy-loaded models)
// ═══════════════════════════════════════════════════════════════════════════

export {
  type AIModelType,
  aiGeneration,
  type DepthEstimationOptions,
  estimateDepth,
  type GenerationOptions,
  generateNormalMap,
  getAvailableModels,
  type InferenceResult,
  isAIBackendConnected,
  type ModelInfo,
  type ModelStatus,
  type NormalMapOptions,
  type SegmentationOptions,
  type SegmentationResult as AISegmentationResult, // Alias to avoid conflict with segmentation
  segmentAtPoint,
} from "./aiGeneration";

// ═══════════════════════════════════════════════════════════════════════════
//                                                // audio // worker // client
// ═══════════════════════════════════════════════════════════════════════════

export {
  type AnalyzeOptions,
  type AudioAnalysisProgress,
  analyzeAudioInWorker,
  cancelAnalysis,
  loadAndAnalyzeAudio,
  terminateWorker,
} from "./audioWorkerClient";

// ═══════════════════════════════════════════════════════════════════════════
//                                                   // camera // enhancements
// ═══════════════════════════════════════════════════════════════════════════

export {
  type AutoFocusConfig,
  CameraShake,
  type CameraShakeConfig,
  calculateAutoFocusDistance,
  createAutoFocus,
  createCameraShake,
  createRackFocus,
  DEFAULT_AUTOFOCUS,
  DEFAULT_RACK_FOCUS,
  DEFAULT_SHAKE_CONFIG,
  estimateMotionBlur,
  generateMotionBlurKeyframes,
  generateRackFocusKeyframes,
  getRackFocusDistance,
  type MotionBlurEstimate,
  type RackFocusConfig,
  SHAKE_PRESETS,
} from "./cameraEnhancements";

// ═══════════════════════════════════════════════════════════════════════════
// LAYER DECOMPOSITION (AI-powered)
// ═══════════════════════════════════════════════════════════════════════════

export {
  canvasToDataUrl,
  type DecomposedLayer,
  type DecompositionModelStatus,
  type DecompositionOptions,
  type DecompositionResult,
  dataUrlToImage,
  getLayerDecompositionService,
  imageToDataUrl,
  LayerDecompositionService,
} from "./layerDecomposition";

// ═══════════════════════════════════════════════════════════════════════════
//                                             // layer // evaluation // cache
// ═══════════════════════════════════════════════════════════════════════════

export {
  clearEvaluationCache,
  clearLayerCache,
  evaluateLayerCached,
  evaluateLayersCached,
  getCachedEvaluation,
  getEvaluationCacheStats,
  getGlobalVersion,
  getLayerVersion,
  markAllLayersDirty,
  markLayerDirty,
  setCachedEvaluation,
} from "./layerEvaluationCache";

// ═══════════════════════════════════════════════════════════════════════════
// LAZY LOADER (Dynamic module loading)
// ═══════════════════════════════════════════════════════════════════════════

export {
  clearAllModuleCache,
  clearModuleCache,
  getModuleCacheStats,
  loadCameraTrajectory,
  loadDepthflow,
  loadJSZip,
  loadMath3D,
  loadMatteExporter,
  loadMP4Muxer,
  loadParticleSystem,
  loadWebGPURenderer,
  loadWebMMuxer,
  preloadCommonModules,
  preloadExportModules,
} from "./lazyLoader";

// ═══════════════════════════════════════════════════════════════════════════
//                                                        // mask // generator
// ═══════════════════════════════════════════════════════════════════════════

export {
  type AffineTransformParams,
  generateMask,
  generateMaskSequence,
  type MaskGeneratorOptions,
  type MaskShapeType,
  maskToCanvas,
  maskToDataURL,
  maskToImageData,
} from "./maskGenerator";

// ═══════════════════════════════════════════════════════════════════════════
// MEMORY BUDGET (GPU/VRAM tracking)
// ═══════════════════════════════════════════════════════════════════════════

export {
  allocationList,
  availableVRAM,
  canAllocate,
  freeMemory,
  type GPUInfo,
  getMemorySummary,
  getWarning,
  initializeGPUDetection,
  type MemoryAllocation,
  type MemoryCategory,
  type MemoryWarning,
  memoryState,
  registerAllocation,
  totalUsageMB,
  unloadableItems,
  unregisterAllocation,
  updateAllocation,
  usageByCategory,
  usagePercent,
  VRAM_ESTIMATES,
  warningLevel,
} from "./memoryBudget";

// ═══════════════════════════════════════════════════════════════════════════
//                                                         // path // morphing
// ═══════════════════════════════════════════════════════════════════════════

export {
  DEFAULT_MORPH_CONFIG,
  getCorrespondence,
  isBezierPath,
  type MorphConfig,
  morphPaths,
  morphPathsAuto,
  PathMorphing,
  type PreparedMorphPaths,
  prepareMorphPaths,
} from "./pathMorphing";

// ═══════════════════════════════════════════════════════════════════════════
// PERSISTENCE SERVICE (IndexedDB storage)
// ═══════════════════════════════════════════════════════════════════════════

export {
  type AIConversation,
  addToRecentProjects,
  clearAllData,
  clearRecentProjects,
  deleteAIConversation,
  deleteAsset,
  deleteProject as deleteProjectIndexedDB,
  deleteProjectAssets,
  exportAllData,
  getAIConversation,
  getAsset,
  getLastProjectId,
  getProject as getProjectIndexedDB,
  getProjectAIConversations,
  getProjectAssets,
  getRecentProjects,
  getSetting,
  getSettings,
  getStorageEstimate,
  importData,
  initPersistence,
  listProjects as listProjectsIndexedDB,
  type RecentProject,
  removeFromRecentProjects,
  type StoredAsset,
  type StoredProject,
  saveAIConversation,
  saveAsset,
  // Alias to avoid conflict with projectStorage exports
  saveProject as saveProjectIndexedDB,
  saveSettings,
  setLastProjectId,
  setSetting,
  type UserSettings,
} from "./persistenceService";

// SEGMENT TO MASK exports are already included via ./segmentation re-export (lines 423-446)

// ═══════════════════════════════════════════════════════════════════════════
//                                                         // text // animator
// ═══════════════════════════════════════════════════════════════════════════

export {
  applyTextAnimatorPreset,
  calculateCharacterInfluence,
  createTextAnimator,
  DEFAULT_ANIMATOR_PROPERTIES,
  DEFAULT_RANGE_SELECTOR,
  TEXT_ANIMATOR_PRESET_LIST,
  TEXT_ANIMATOR_PRESETS,
  type TextAnimatorPreset,
} from "./textAnimator";

// ═══════════════════════════════════════════════════════════════════════════
//                                                       // webgpu // renderer
// ═══════════════════════════════════════════════════════════════════════════

export {
  type BlurParams,
  type ColorCorrectionParams,
  getWebGPUStats,
  type WebGPUCapabilities,
  webgpuRenderer,
} from "./webgpuRenderer";

// ═══════════════════════════════════════════════════════════════════════════
// GAUSSIAN SPLATTING (3DGS)
// ═══════════════════════════════════════════════════════════════════════════

export {
  createGaussianBuffers,
  createGaussianPoints,
  DEFAULT_QUALITY as DEFAULT_3DGS_QUALITY,
  type GaussianPrimitive,
  type GaussianRenderQuality,
  type GaussianSplatScene,
  GaussianSplattingService,
  gaussianSplatting,
  reorderBuffers,
  sortGaussiansByDepth,
} from "./gaussianSplatting";

// ═══════════════════════════════════════════════════════════════════════════
// VIDEO DECODER (WebCodecs API - Phase 4)
// Frame-accurate video decoding with LRU caching
// ═══════════════════════════════════════════════════════════════════════════

export {
  type DecoderOptions,
  isWebCodecsSupported,
  VideoDecoderService,
  type VideoFrameInfo,
  type VideoInfo,
  videoDecoderPool,
} from "./videoDecoder";

// ═══════════════════════════════════════════════════════════════════════════
//                                                     // video // transitions
// (Inspired by filliptm's ComfyUI_Fill-Nodes)
// Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
// ═══════════════════════════════════════════════════════════════════════════

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
} from "./video";

// ═══════════════════════════════════════════════════════════════════════════
// FRAME INTERPOLATION (RIFE)
// (Inspired by filliptm's ComfyUI_Fill-Nodes, powered by RIFE)
// Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
//              https://github.com/megvii-research/ECCV2022-RIFE
// ═══════════════════════════════════════════════════════════════════════════

export {
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
  interpolationBase64ToBlob,
  isInterpolationAvailable,
  type PairInterpolationResult,
  // Types
  type RIFEModel,
  type SequenceInterpolationResult,
  type SlowMoResult,
} from "./video";

// ═══════════════════════════════════════════════════════════════════════════
//                                              // audio // stem // separation
// (Inspired by filliptm's ComfyUI_Fill-Nodes, powered by Facebook's Demucs)
// Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
//              https://github.com/facebookresearch/demucs
// ═══════════════════════════════════════════════════════════════════════════

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
} from "./audio";

// ═══════════════════════════════════════════════════════════════════════════
//                                            // enhanced // beat // detection
// (Inspired by filliptm's ComfyUI_Fill-Nodes audio processing)
// Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
// ═══════════════════════════════════════════════════════════════════════════

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
} from "./audio";

// ═══════════════════════════════════════════════════════════════════════════
//                                             // camera // tracking // import
// ═══════════════════════════════════════════════════════════════════════════

export {
  detectTrackingFormat,
  exportCameraToTrackingFormat,
  importCameraTracking,
  parseBlenderTrackingJSON,
  parseCOLMAPOutput,
  parseLatticeTrackingJSON,
} from "./cameraTrackingImport";

// ═══════════════════════════════════════════════════════════════════════════
//                                                // track // point // service
// ═══════════════════════════════════════════════════════════════════════════

export {
  clearAllTracks,
  clearSelection,
  createTrack,
  defineGroundPlaneFromPoints,
  deleteSelectedTracks,
  deleteTrack,
  deselectTrack,
  exportTrackPoints2D,
  getPointsAtFrame,
  getTrackPosition,
  getTrackPositions,
  getTrackStats,
  importTrackPoints2D,
  importTrackPoints3D,
  removeTrackPosition,
  selectTrack,
  setActiveTrack,
  setGroundPlane,
  setOrigin3D,
  setTrackPosition,
  trackPointState,
  useTrackPoints,
} from "./trackPointService";

// ═══════════════════════════════════════════════════════════════════════════
// RENDER QUEUE (Phase 5 - Background Rendering)
// ═══════════════════════════════════════════════════════════════════════════

export {
  getRenderQueueManager,
  initializeRenderQueue,
  type RenderedFrame,
  type RenderJob,
  type RenderJobConfig,
  type RenderJobProgress,
  type RenderJobStatus,
  type RenderQueueConfig,
  RenderQueueManager,
  type RenderQueueStats,
} from "./renderQueue";

// ═══════════════════════════════════════════════════════════════════════════
// COLOR MANAGEMENT (Phase 6 - ICC Profiles & Color Spaces)
// ═══════════════════════════════════════════════════════════════════════════

export {
  applyGammaRGB,
  COLOR_SPACES,
  ColorProfileService,
  type ColorSettings,
  type ColorSpace,
  type ColorSpaceInfo,
  colorUtils,
  convertColorSpace,
  extractICCFromImage,
  getColorProfileService,
  type ICCProfile,
  initializeColorManagement,
  linearizeRGB,
  linearToSRGB,
  parseICCProfile,
  type RGB as ColorRGB,
  sRGBToLinear,
  type ViewTransform,
  type XYZ as ColorXYZ,
} from "./colorManagement";

// ═══════════════════════════════════════════════════════════════════════════
// TIMELINE WAVEFORM (Phase 7 - Audio Visualization)
// ═══════════════════════════════════════════════════════════════════════════

export {
  clearWaveformCache,
  computePeaks,
  createWaveformData,
  generatePeakMipmap,
  getWaveformData,
  renderTimelineWaveform,
  renderWaveform,
  renderWaveformToImage,
  type TimelineWaveformConfig,
  type WaveformData,
  type WaveformPeakOptions,
  type WaveformRenderOptions,
} from "./timelineWaveform";

// ═══════════════════════════════════════════════════════════════════════════
// PLUGIN SYSTEM (Phase 9 - Extensibility)
// ═══════════════════════════════════════════════════════════════════════════

export {
  type ContextMenuDefinition,
  type EffectDefinition,
  type EffectParameter,
  type ExporterDefinition,
  getPluginManager,
  type LatticePlugin,
  type LatticePluginAPI,
  type LoadedPlugin,
  type MenuItemDefinition,
  type PanelDefinition,
  type PluginEvent,
  PluginManager,
  type PluginManifest,
  type PluginPermission,
  type PluginType,
  type ToolDefinition,
} from "./plugins";

// ═══════════════════════════════════════════════════════════════════════════
// PROJECT MIGRATION (Phase 10 - Versioning)
// ═══════════════════════════════════════════════════════════════════════════

export {
  CURRENT_SCHEMA_VERSION,
  getAvailableMigrations,
  getMigrationInfo,
  getProjectVersion,
  MIN_SUPPORTED_VERSION,
  type Migration,
  type MigrationFunction,
  type MigrationResult,
  migrateProject,
  needsMigration,
  stampProjectVersion,
  type VersionedProject,
} from "./projectMigration";

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // template // builder
// ═══════════════════════════════════════════════════════════════════════════

export {
  // Comments
  addComment,
  addExposedProperty,
  // Groups
  addPropertyGroup,
  clearTemplate,
  // Property exposure
  EXPOSABLE_PROPERTIES,
  exportTemplate,
  getEffectControlValue,
  getExposableProperties,
  getExpressionControls,
  // Utilities
  getOrganizedProperties,
  // Property access
  getPropertyValue,
  // Template management
  initializeTemplate,
  isExposedProperty,
  isTemplateComment,
  movePropertyToGroup,
  type OrganizedProperties,
  // Template export
  prepareTemplateExport,
  removeComment,
  removeExposedProperty,
  removePropertyGroup,
  reorderExposedProperties,
  reorderGroups,
  setPropertyValue,
  type TemplateValidationResult,
  updateComment,
  updateExposedProperty,
  updateTemplateMetadata,
  // Validation
  validateTemplate,
} from "./templateBuilder";

// ═══════════════════════════════════════════════════════════════════════════
// JSON VALIDATION & DATA HARDENING
// ═══════════════════════════════════════════════════════════════════════════

export {
  deepCloneSanitized,
  isArray,
  isBoolean,
  isNumber,
  // Type guards
  isObject,
  isString,
  // Safe JSON operations
  safeJSONParse,
  safeJSONStringify,
  sanitizeFileName,
  // Sanitization
  sanitizeString,
} from "./jsonValidation";

// ═══════════════════════════════════════════════════════════════════════════
// TEXT MEASUREMENT (Canvas API)
// ═══════════════════════════════════════════════════════════════════════════

export {
  buildFontString,
  cleanup as cleanupTextMeasurement,
  getBaselineOffset,
  getCharacterPositions,
  isFontAvailable,
  measureMultilineText,
  measureText,
  measureTextLayerRect,
  measureTextWithFont,
  type TextMetrics,
  type TextRect,
} from "./textMeasurement";

// ═══════════════════════════════════════════════════════════════════════════
// DATA IMPORT (Tutorial 14 - Data-Driven Animation)
// ═══════════════════════════════════════════════════════════════════════════

// Re-export data asset types
export {
  type CSVDataAsset,
  type CSVParseOptions,
  type DataAsset,
  type DataFileType,
  type DataParseResult,
  type FootageDataAccessor,
  getDataFileType,
  isCSVAsset,
  // Type guards
  isJSONAsset,
  isSupportedDataFile,
  type JSONDataAsset,
  type JSONParseOptions,
} from "@/types/dataAsset";
export {
  clearDataAssets,
  countCSVRows,
  // Expression support
  createFootageAccessor,
  // Utilities
  extractArrayFromJSON,
  getAllDataAssets,
  getDataAsset,
  getJSONValue,
  getUniqueColumnValues,
  // Asset management
  importDataAsset,
  importDataFromFile,
  maxCSVColumn,
  minCSVColumn,
  parseCSV,
  parseDataFile,
  // Parsing functions
  parseJSON,
  parseTSV,
  reloadDataAsset,
  removeDataAsset,
  sumCSVColumn,
} from "./dataImport";

// ═══════════════════════════════════════════════════════════════════════════
// GLOBAL LIGHT (Layer Styles)
// ═══════════════════════════════════════════════════════════════════════════

export {
  clearGlobalLightCache,
  // Factory
  createDefaultGlobalLight,
  DEFAULT_ALTITUDE as DEFAULT_GLOBAL_LIGHT_ALTITUDE,
  // Constants
  DEFAULT_ANGLE as DEFAULT_GLOBAL_LIGHT_ANGLE,
  deserializeGlobalLight,
  enableGlobalLightAltitudeAnimation,
  // Animation
  enableGlobalLightAngleAnimation,
  // Getters
  getGlobalLight,
  getGlobalLightAltitude,
  getGlobalLightAngle,
  getLightDirection,
  getShadowOffset,
  // Cleanup
  removeGlobalLight,
  // Serialization
  serializeGlobalLight,
  setGlobalLightAltitude,
  // Setters
  setGlobalLightAngle,
  setGlobalLightDirection,
  setGlobalLightSettings,
} from "./globalLight";

// ═══════════════════════════════════════════════════════════════════════════
// Export Templates (Tutorial 20)
// ═══════════════════════════════════════════════════════════════════════════

export {
  type ExportTemplate,
  type ExportTemplateStore,
  exportTemplateService,
} from "./exportTemplates";

// ═══════════════════════════════════════════════════════════════════════════
// Project Collection (Tutorial 20)
// ═══════════════════════════════════════════════════════════════════════════

export {
  type CollectionManifest,
  type CollectionOptions,
  type CollectionProgress,
  projectCollectionService,
} from "./projectCollection";

// ═══════════════════════════════════════════════════════════════════════════
// Roving Keyframes (Tutorial 20)
// ═══════════════════════════════════════════════════════════════════════════

export {
  applyRovingKeyframes,
  calculateVelocities,
  getEvenlySpacedFrames,
  type RovingOptions,
  type RovingResult,
  wouldRovingChange,
} from "./rovingKeyframes";

// ═══════════════════════════════════════════════════════════════════════════
// PHYSICS SIMULATION (Feature 05 - Newton Physics)
// ═══════════════════════════════════════════════════════════════════════════

export {
  type AttractionForce,
  applyRagdollState,
  type BlobJointConfig,
  type BodyType,
  type BuoyancyForce,
  type ClothConfig,
  type ClothState,
  type CollisionFilter,
  type CollisionResponse,
  type CollisionShape,
  type ContactInfo,
  convertRagdollToPhysics,
  createBoxBody,
  createCircleBody,
  createClothConfig,
  createGravityForce,
  // Factory functions
  createPhysicsEngine,
  createRagdollBuilder,
  DEFAULT_SPACE_CONFIG,
  type DistanceJointConfig,
  type DragForce,
  type ExplosionForce,
  type ExportedKeyframes,
  extractRagdollState,
  type ForceField,
  type ForceType,
  type GravityForce,
  HUMANOID_BONES,
  // Presets
  HUMANOID_PRESETS,
  type HumanoidRagdollPreset,
  type JointConfig,
  // Joint system
  JointSystem,
  type JointType,
  type KeyframeExportOptions,
  MATERIAL_PRESETS,
  type PhysicsCompositionData,
  // Main engine
  PhysicsEngine,
  type PhysicsLayerData,
  type PhysicsMaterial,
  PhysicsRandom,
  type PhysicsSimulationState,
  type PhysicsSpaceConfig,
  // Types
  type PhysicsVec2,
  type PistonJointConfig,
  type PivotJointConfig,
  type RagdollBone,
  // Ragdoll builder
  RagdollBuilder,
  type RagdollConfig,
  type RagdollState,
  type RigidBodyConfig,
  type RigidBodyState,
  type RopeJointConfig,
  type ShapeType,
  type SoftBodyConfig,
  type SoftBodyState,
  type SpringJointConfig,
  type VerletConstraint,
  type VerletParticle,
  type VortexForce,
  vec2,
  type WeldJointConfig,
  type WheelJointConfig,
  type WindForce,
} from "./physics";

// ═══════════════════════════════════════════════════════════════════════════
// COLOR & DEPTH REACTIVITY
// (Inspired by RyanOnTheInside's ComfyUI nodes for color/depth-driven animations)
// ═══════════════════════════════════════════════════════════════════════════

export {
  // Region analysis
  analyzeRegion,
  type ColorFeature,
  type ColorReactivityConfig,
  // Types
  type ColorSample,
  calculateBrightness,
  // Motion detection (frame differencing)
  calculateMotion,
  createColorSample,
  type DepthReactivityConfig,
  type DepthSample,
  getFeatureValue,
  // Color reactivity
  getMappedColorValue,
  getMappedDepthValue,
  getMappedMotionValue as getMappedColorMotionValue,
  type MotionDetectionConfig,
  // Color utilities
  rgbToHsv,
  type SampleMode,
  sampleAreaAverage,
  sampleAreaMax,
  sampleAreaMin,
  sampleColorFromImageData,
  // Depth reactivity
  sampleDepth,
  sampleDepthWithGradient,
  // Pixel sampling
  samplePixel,
} from "./colorDepthReactivity";

// ═══════════════════════════════════════════════════════════════════════════
//                                            // motion // based // reactivity
// (Layer velocity, acceleration, proximity-based property modulation)
// ═══════════════════════════════════════════════════════════════════════════

export {
  // Mapping
  applyMotionCurve,
  // Proximity
  calculateProximity,
  // Cache management
  clearMotionCache,
  // Motion state computation
  computeMotionState,
  getMappedMotionValue as getMappedLayerMotionValue,
  getMotionCacheStats,
  getMotionFeatureValue,
  getProximityValue,
  type MotionFeature,
  type MotionReactivityConfig,
  // Types
  type MotionState,
} from "./motionReactivity";
