/**
 * GPU Particle System Module
 *
 * High-performance particle system for Lattice Compositor featuring:
 * - 100k+ particles via WebGL2 instanced rendering
 * - GPU-accelerated physics (CPU fallback available)
 * - Full 3D simulation with mass, drag, forces
 * - Audio/MIDI reactive parameter modulation
 * - Professional emitter shapes and force fields
 */

// Core system
export {
  createDefaultConfig,
  createDefaultEmitter,
  createDefaultForceField,
  GPUParticleSystem,
} from "./GPUParticleSystem";

// Group system
export { ParticleGroupSystem } from "./ParticleGroupSystem";

// Spring/Soft Body system
export { ParticleSpringSystem } from "./ParticleSpringSystem";
export { GPUSpringSystem } from "./GPUSpringSystem";
export type { Spring, SpringConstraint, SpringSystemConfig } from "./ParticleSpringSystem";

// SPH Fluid system
export { ParticleSPHSystem } from "./ParticleSPHSystem";
export { GPUSPHSystem } from "./GPUSPHSystem";
export type { SPHConfig } from "./ParticleSPHSystem";

// Type exports
export type {
  AudioBinding,
  // Audio types
  AudioFeature,
  AvoidanceConfig,
  EmitterConfig,
  // Emitter types
  EmitterShape,
  EmitterShapeConfig,
  // Behavior types
  FlockingConfig,
  ForceFieldConfig,
  // Force field types
  ForceFieldType,
  GPUParticleSystemConfig,
  LifetimeModulation,
  // Modulation types
  ModulationCurve,
  ParticleEvent,
  ParticleEventHandler,
  ParticleEventType,
  // Core types
  ParticleGPUData,
  ParticleLightingConfig,
  // Rendering types
  ParticleRenderMode,
  ParticleShadowConfig,
  ParticleSystemState,
  ParticleTextureConfig,
  PathFollowConfig,
  RenderConfig,
  SubEmitterConfig,
  // Sub-emitter types
  SubEmitterTrigger,
  // Group types
  ParticleGroupConfig,
  MAX_PARTICLE_GROUPS,
} from "./types";
