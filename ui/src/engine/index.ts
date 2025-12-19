/**
 * Weyl Engine - Three.js Based Rendering Engine
 *
 * Export all public APIs for the compositor rendering engine.
 */

// Main engine
export { WeylEngine } from './WeylEngine';
export type { WeylEngineConfig } from './types';

// Core subsystems
export { SceneManager } from './core/SceneManager';
export { RenderPipeline } from './core/RenderPipeline';
export { CameraController } from './core/CameraController';
export { LayerManager } from './core/LayerManager';
export { ResourceManager } from './core/ResourceManager';

// Layer types
export { BaseLayer } from './layers/BaseLayer';
export { ImageLayer } from './layers/ImageLayer';
export { SolidLayer } from './layers/SolidLayer';
export { ControlLayer } from './layers/ControlLayer';
export { TextLayer } from './layers/TextLayer';
export { SplineLayer } from './layers/SplineLayer';
export { ParticleLayer } from './layers/ParticleLayer';
export { VideoLayer, extractVideoMetadata, calculateCompositionFromVideo } from './layers/VideoLayer';
export { NestedCompLayer } from './layers/NestedCompLayer';
export { CameraLayer } from './layers/CameraLayer';
export type { AnchorPointGrouping, FillStrokeOrder, InterCharacterBlending } from './layers/TextLayer';
export type { VideoMetadata, VideoLayerEvents } from './layers/VideoLayer';
export type { NestedCompRenderContext } from './layers/NestedCompLayer';
export type { CameraGetter, CameraUpdater } from './layers/CameraLayer';

// GPU Particle System
export {
  GPUParticleSystem,
  createDefaultConfig as createDefaultParticleConfig,
  createDefaultEmitter,
  createDefaultForceField,
} from './particles';
export type {
  GPUParticleSystemConfig,
  EmitterConfig,
  ForceFieldConfig,
  AudioFeature,
  AudioBinding,
  FlockingConfig,
  ParticleRenderMode,
  ModulationCurve,
} from './particles';

// Animation
export { KeyframeEvaluator } from './animation/KeyframeEvaluator';
export { easingFunctions, getEasing, getEasingNames, hasEasing } from './animation/EasingFunctions';
export type { EasingFunction } from './animation/EasingFunctions';

// Utilities
export { PerformanceMonitor } from './utils/PerformanceMonitor';

// Types
export type {
  RenderState,
  LayerInstance,
  Transform3D,
  EvaluatedTransform,
  CameraState,
  CameraAnimationProps,
  RenderTargetConfig,
  CaptureResult,
  DepthCaptureResult,
  EffectConfig,
  BlurEffectConfig,
  GlowEffectConfig,
  KeyframeEvaluation,
  InterpolationFn,
  TextRenderConfig,
  CharacterTransform,
  ParticleState,
  EmissionConfig,
  PathPoint,
  PathConfig,
  ExportFrameOptions,
  ExportSequenceOptions,
  PerformanceStats,
  PerformanceConfig,
  EngineEventType,
  EngineEventHandler,
  EngineEvent,
  Vector2Like,
  Vector3Like,
  ColorLike,
  BoundingBox2D,
  BoundingBox3D,
} from './types';
