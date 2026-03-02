/**
 * Lattice Engine - Three.js Based Rendering Engine
 *
 * Export all public APIs for the compositor rendering engine.
 */

export type { EasingFunction } from "./animation/EasingFunctions";
export {
  easingFunctions,
  getEasing,
  getEasingNames,
  hasEasing,
} from "./animation/EasingFunctions";
// Animation
export { KeyframeEvaluator } from "./animation/KeyframeEvaluator";
export { CameraController } from "./core/CameraController";
export { LayerManager } from "./core/LayerManager";
export { RenderPipeline } from "./core/RenderPipeline";
export { ResourceManager } from "./core/ResourceManager";
// Core subsystems
export { SceneManager } from "./core/SceneManager";
// Main engine
export { LatticeEngine } from "./LatticeEngine";
// Layer types
export { BaseLayer } from "./layers/BaseLayer";
export type { CameraGetter, CameraUpdater } from "./layers/CameraLayer";
export { CameraLayer } from "./layers/CameraLayer";
export { ControlLayer } from "./layers/ControlLayer";
export { ImageLayer } from "./layers/ImageLayer";
export type { NestedCompRenderContext } from "./layers/NestedCompLayer";
export { NestedCompLayer } from "./layers/NestedCompLayer";
export { ParticleLayer } from "./layers/ParticleLayer";
export { SolidLayer } from "./layers/SolidLayer";
export { SplineLayer } from "./layers/SplineLayer";
export type {
  AnchorPointGrouping,
  FillStrokeOrder,
  InterCharacterBlending,
} from "./layers/TextLayer";
export { TextLayer } from "./layers/TextLayer";
export type { VideoLayerEvents, VideoMetadata } from "./layers/VideoLayer";
export {
  calculateCompositionFromVideo,
  extractVideoMetadata,
  VideoLayer,
} from "./layers/VideoLayer";
export type {
  AudioBinding,
  AudioFeature,
  EmitterConfig,
  FlockingConfig,
  ForceFieldConfig,
  GPUParticleSystemConfig,
  ModulationCurve,
  ParticleRenderMode,
} from "./particles";
// GPU Particle System - VerifiedGPUParticleSystem is the new system
export {
  VerifiedGPUParticleSystem,
  createDefaultConfig as createDefaultParticleConfig,
  createDefaultEmitter,
  createDefaultForceField,
} from "./particles";
// Types
export type {
  BlurEffectConfig,
  BoundingBox2D,
  BoundingBox3D,
  CameraAnimationProps,
  CameraState,
  CaptureResult,
  CharacterTransform,
  ColorLike,
  DepthCaptureResult,
  EffectConfig,
  EmissionConfig,
  EngineEvent,
  EngineEventHandler,
  EngineEventType,
  EvaluatedTransform,
  ExportFrameOptions,
  ExportSequenceOptions,
  GlowEffectConfig,
  InterpolationFn,
  KeyframeEvaluation,
  LatticeEngineConfig,
  LayerInstance,
  ParticleState,
  PathConfig,
  PathPoint,
  PerformanceConfig,
  PerformanceStats,
  RenderState,
  RenderTargetConfig,
  TextRenderConfig,
  Transform3D,
  Vector2Like,
  Vector3Like,
} from "./types";
// Utilities
export { PerformanceMonitor } from "./utils/PerformanceMonitor";
