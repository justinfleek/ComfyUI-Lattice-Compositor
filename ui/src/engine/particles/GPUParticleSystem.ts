/**
 * GPU Particle System - Main Implementation
 *
 * High-performance particle system using:
 * - WebGL2 Transform Feedback for GPU physics
 * - Instanced rendering for 100k+ particles
 * - Double-buffered particle state
 * - Spatial hashing for neighbor queries
 * - Audio-reactive parameter modulation
 *
 * Performance characteristics:
 * - CPU physics: ~10-50k particles at 60fps
 * - GPU physics (Transform Feedback): 100k+ particles at 60fps
 * - Memory: 64 bytes per particle (cache-line aligned)
 */

import * as THREE from 'three';
import type {
  GPUParticleSystemConfig,
  EmitterConfig,
  ForceFieldConfig,
  SubEmitterConfig,
  ParticleSystemState,
  AudioFeature,
  AudioBinding,
  ParticleEvent,
  ParticleEventHandler,
  ModulationCurve,
  FlockingConfig,
} from './types';
import {
  TRANSFORM_FEEDBACK_VERTEX_SHADER,
  TRANSFORM_FEEDBACK_FRAGMENT_SHADER,
  PARTICLE_VERTEX_SHADER,
  PARTICLE_FRAGMENT_SHADER,
} from './particleShaders';

// ============================================================================
// Constants
// ============================================================================

const PARTICLE_STRIDE = 16;  // Floats per particle (64 bytes)
const MAX_FORCE_FIELDS = 16;
const MAX_EMITTERS = 32;
const SPATIAL_CELL_SIZE = 50;  // Pixels

// Transform feedback varyings for GPU physics
const TF_VARYINGS = [
  'tf_position',
  'tf_velocity',
  'tf_life',
  'tf_physical',
  'tf_rotation',
  'tf_color',
];

/**
 * Cached particle state for a specific frame
 * Used for fast scrubbing - restore state instead of replaying from frame 0
 */
interface ParticleFrameCache {
  frame: number;
  version: number; // Cache version when this was created
  particleBuffer: Float32Array; // Copy of particle data
  freeIndices: number[]; // Copy of free indices
  particleCount: number;
  simulationTime: number;
  rngState: number; // RNG state at this frame for determinism
  emitterAccumulators: Map<string, number>; // Emitter accumulator values
}

// Attribute layout for transform feedback
const PARTICLE_ATTRIBUTES = {
  position: { size: 3, offset: 0 },
  velocity: { size: 3, offset: 3 },
  life: { size: 2, offset: 6 },
  physical: { size: 2, offset: 8 },
  rotation: { size: 2, offset: 10 },
  color: { size: 4, offset: 12 },
};

// ============================================================================
// Default Configurations
// ============================================================================

export function createDefaultEmitter(id?: string): EmitterConfig {
  return {
    id: id || `emitter_${Date.now()}`,
    name: 'Emitter',
    enabled: true,
    position: { x: 0.5, y: 0.5, z: 0 },
    rotation: { x: 0, y: 0, z: 0 },
    shape: { type: 'point' },
    emissionRate: 100,
    emissionRateVariance: 0,
    burstCount: 0,
    burstInterval: 0,
    initialSpeed: 200,
    speedVariance: 50,
    inheritEmitterVelocity: 0,
    initialSize: 10,
    sizeVariance: 2,
    initialMass: 1,
    massVariance: 0,
    lifetime: 120,
    lifetimeVariance: 20,
    initialRotation: 0,
    rotationVariance: 360,
    initialAngularVelocity: 0,
    angularVelocityVariance: 0,
    colorStart: [1, 1, 1, 1],
    colorEnd: [1, 1, 1, 0],
    colorVariance: 0,
    emissionDirection: { x: 0, y: -1, z: 0 },
    emissionSpread: 30,
    burstOnBeat: false,
    beatEmissionMultiplier: 5,
  };
}

export function createDefaultForceField(type: ForceFieldConfig['type'], id?: string): ForceFieldConfig {
  const base: ForceFieldConfig = {
    id: id || `force_${Date.now()}`,
    name: type.charAt(0).toUpperCase() + type.slice(1),
    type,
    enabled: true,
    strength: 100,
    position: { x: 0.5, y: 0.5, z: 0 },
    falloffStart: 0,
    falloffEnd: 500,
    falloffType: 'linear',
  };

  switch (type) {
    case 'gravity':
      base.direction = { x: 0, y: 1, z: 0 };
      base.strength = 98;
      break;
    case 'vortex':
      base.vortexAxis = { x: 0, y: 0, z: 1 };
      base.inwardForce = 20;
      break;
    case 'turbulence':
      base.noiseScale = 0.005;
      base.noiseSpeed = 0.5;
      base.noiseOctaves = 3;
      base.noiseLacunarity = 2;
      base.noiseGain = 0.5;
      break;
    case 'drag':
      base.linearDrag = 0.1;
      base.quadraticDrag = 0.01;
      break;
    case 'wind':
      base.windDirection = { x: 1, y: 0, z: 0 };
      base.gustStrength = 50;
      base.gustFrequency = 0.1;
      break;
    case 'lorenz':
      base.lorenzSigma = 10;
      base.lorenzRho = 28;
      base.lorenzBeta = 2.667;
      break;
  }

  return base;
}

export function createDefaultConfig(): GPUParticleSystemConfig {
  return {
    maxParticles: 100000,
    simulationSpace: 'world',
    deltaTimeMode: 'variable',
    fixedDeltaTime: 1 / 60,
    timeScale: 1,
    warmupFrames: 0,
    emitters: [],
    forceFields: [],
    subEmitters: [],
    lifetimeModulation: {},
    render: {
      mode: 'billboard',
      sortByDepth: true,
      depthWrite: false,
      depthTest: true,
      blendMode: 'normal',
      stretchFactor: 1,
      minStretch: 1,
      maxStretch: 4,
      trailLength: 0,
      trailSegments: 8,
      trailWidthStart: 1,
      trailWidthEnd: 0,
      trailFadeMode: 'both',
      texture: {},
      shadow: {
        castShadows: false,
        receiveShadows: false,
        shadowSoftness: 1,
        shadowBias: 0.001,
        aoEnabled: false,
        aoRadius: 10,
        aoIntensity: 0.5,
        aoSamples: 8,
      },
      lighting: {
        receiveLighting: false,
        roughness: 0.5,
        metalness: 0,
        emissiveIntensity: 0,
        subsurfaceScattering: false,
        subsurfaceColor: [1, 0.5, 0.5],
        subsurfaceRadius: 1,
      },
      motionBlur: false,
      motionBlurSamples: 4,
      motionBlurStrength: 0.5,
      lodEnabled: false,
      lodDistances: [100, 500, 1000],
      lodSizeMultipliers: [1, 0.5, 0.25],
    },
    audioBindings: [],
    spatialHashCellSize: SPATIAL_CELL_SIZE,
    updateFrequency: 1,
    cullOffscreen: true,
  };
}

// ============================================================================
// GPU Particle System Class
// ============================================================================

export class GPUParticleSystem {
  private config: GPUParticleSystemConfig;
  private gl: WebGL2RenderingContext | null = null;
  private renderer: THREE.WebGLRenderer | null = null;

  // Double-buffered particle data
  private particleBufferA: Float32Array;
  private particleBufferB: Float32Array;
  private currentBuffer: 'A' | 'B' = 'A';

  // WebGL resources
  private transformFeedbackProgram: WebGLProgram | null = null;
  private renderProgram: WebGLProgram | null = null;
  private vaoA: WebGLVertexArrayObject | null = null;
  private vaoB: WebGLVertexArrayObject | null = null;
  private particleVboA: WebGLBuffer | null = null;
  private particleVboB: WebGLBuffer | null = null;
  private transformFeedbackA: WebGLTransformFeedback | null = null;
  private transformFeedbackB: WebGLTransformFeedback | null = null;

  // Three.js integration
  private particleMesh: THREE.Mesh | null = null;
  private instancedGeometry: THREE.InstancedBufferGeometry | null = null;
  private material: THREE.ShaderMaterial | null = null;

  // Textures for modulation curves
  private sizeOverLifetimeTexture: THREE.DataTexture | null = null;
  private opacityOverLifetimeTexture: THREE.DataTexture | null = null;
  private colorOverLifetimeTexture: THREE.DataTexture | null = null;

  // Emitter state
  private emitters: Map<string, EmitterConfig & { accumulator: number; velocity: THREE.Vector3 }> = new Map();
  private forceFields: Map<string, ForceFieldConfig> = new Map();
  private subEmitters: Map<string, SubEmitterConfig> = new Map();

  // Runtime state
  private state: ParticleSystemState = {
    particleCount: 0,
    activeEmitters: 0,
    simulationTime: 0,
    frameCount: 0,
    updateTimeMs: 0,
    renderTimeMs: 0,
    gpuMemoryBytes: 0,
    currentAudioFeatures: new Map(),
  };

  // Audio reactivity
  private audioFeatures: Map<AudioFeature, number> = new Map();

  // Spatial hash for neighbor queries (flocking)
  private spatialHash: Map<string, number[]> = new Map();

  // Event system
  private eventHandlers: Map<string, Set<ParticleEventHandler>> = new Map();

  // Pool of free particle indices
  private freeIndices: number[] = [];
  private nextParticleIndex = 0;

  // Random number generator with seed
  private rng: () => number;
  private initialRngSeed: number;
  private currentRngState: number; // Tracks RNG state for save/restore

  // ============================================================================
  // FRAME CACHING SYSTEM
  // Caches particle state every N frames for fast scrubbing
  // ============================================================================
  private frameCache: Map<number, ParticleFrameCache> = new Map();
  private cacheInterval: number = 5; // Cache every 5 frames
  private maxCacheSize: number = 200; // Max cached frames (1000 frames / 5 = 200)
  private cacheVersion: number = 0; // Incremented on parameter changes to invalidate cache
  private currentSimulatedFrame: number = -1; // Track which frame we're at

  constructor(config: Partial<GPUParticleSystemConfig> = {}) {
    this.config = { ...createDefaultConfig(), ...config };

    // Initialize buffers
    const bufferSize = this.config.maxParticles * PARTICLE_STRIDE;
    this.particleBufferA = new Float32Array(bufferSize);
    this.particleBufferB = new Float32Array(bufferSize);

    // Initialize free indices
    for (let i = this.config.maxParticles - 1; i >= 0; i--) {
      this.freeIndices.push(i);
    }

    // Initialize RNG with saved seed for deterministic replay
    this.initialRngSeed = this.config.randomSeed ?? Date.now();
    this.currentRngState = this.initialRngSeed;
    this.rng = this.createSeededRandom(this.initialRngSeed);

    // Add configured emitters and force fields
    this.config.emitters.forEach(e => this.addEmitter(e));
    this.config.forceFields.forEach(f => this.addForceField(f));
    this.config.subEmitters.forEach(s => this.addSubEmitter(s));
  }

  // ============================================================================
  // Initialization
  // ============================================================================

  // GPU physics mode flag
  private useGPUPhysics = false;
  private gpuPhysicsInitialized = false;

  // Force field uniform buffer for GPU physics
  private forceFieldBuffer: Float32Array | null = null;
  private forceFieldTexture: THREE.DataTexture | null = null;

  /**
   * Initialize GPU resources. Must be called before simulation.
   */
  initialize(renderer: THREE.WebGLRenderer): void {
    this.renderer = renderer;
    this.gl = renderer.getContext() as WebGL2RenderingContext;

    if (!this.gl) {
      throw new Error('WebGL2 context required for GPU particle system');
    }

    // Create modulation textures
    this.createModulationTextures();

    // Create Three.js mesh for rendering
    this.createParticleMesh();

    // Initialize GPU physics if WebGL2 transform feedback is available
    this.initializeGPUPhysics();

    // Calculate GPU memory usage
    this.state.gpuMemoryBytes = this.config.maxParticles * PARTICLE_STRIDE * 4 * 2;  // Double buffered
  }

  /**
   * Initialize WebGL2 Transform Feedback for GPU-accelerated physics
   * This allows physics simulation to run entirely on the GPU for 100k+ particles
   */
  private initializeGPUPhysics(): void {
    if (!this.gl) return;

    const gl = this.gl;

    // Check for required extensions
    const tfExtension = gl.getExtension('EXT_color_buffer_float');
    if (!tfExtension) {
      console.warn('EXT_color_buffer_float not available, using CPU physics fallback');
      this.useGPUPhysics = false;
      return;
    }

    try {
      // Create transform feedback program
      this.transformFeedbackProgram = this.createTransformFeedbackProgram(gl);

      if (!this.transformFeedbackProgram) {
        console.warn('Failed to create transform feedback program, using CPU physics');
        this.useGPUPhysics = false;
        return;
      }

      // Create double-buffered VAOs and VBOs
      this.particleVboA = gl.createBuffer();
      this.particleVboB = gl.createBuffer();

      if (!this.particleVboA || !this.particleVboB) {
        throw new Error('Failed to create particle VBOs');
      }

      // Initialize VBO A with particle data
      gl.bindBuffer(gl.ARRAY_BUFFER, this.particleVboA);
      gl.bufferData(gl.ARRAY_BUFFER, this.particleBufferA, gl.DYNAMIC_COPY);

      // Initialize VBO B
      gl.bindBuffer(gl.ARRAY_BUFFER, this.particleVboB);
      gl.bufferData(gl.ARRAY_BUFFER, this.particleBufferB, gl.DYNAMIC_COPY);

      // Create VAOs
      this.vaoA = gl.createVertexArray();
      this.vaoB = gl.createVertexArray();

      if (!this.vaoA || !this.vaoB) {
        throw new Error('Failed to create VAOs');
      }

      // Set up VAO A (reads from VBO A)
      this.setupParticleVAO(gl, this.vaoA, this.particleVboA);

      // Set up VAO B (reads from VBO B)
      this.setupParticleVAO(gl, this.vaoB, this.particleVboB);

      // Create transform feedback objects
      this.transformFeedbackA = gl.createTransformFeedback();
      this.transformFeedbackB = gl.createTransformFeedback();

      if (!this.transformFeedbackA || !this.transformFeedbackB) {
        throw new Error('Failed to create transform feedback objects');
      }

      // Bind VBO B as output for transform feedback A
      gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, this.transformFeedbackA);
      gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 0, this.particleVboB);

      // Bind VBO A as output for transform feedback B
      gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, this.transformFeedbackB);
      gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 0, this.particleVboA);

      gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, null);

      // Create force field texture for passing force field data to shader
      this.forceFieldBuffer = new Float32Array(MAX_FORCE_FIELDS * 16); // 16 floats per force field
      this.forceFieldTexture = new THREE.DataTexture(
        this.forceFieldBuffer as unknown as BufferSource,
        MAX_FORCE_FIELDS,
        4, // 4 rows of 4 floats = 16 floats per force field
        THREE.RGBAFormat,
        THREE.FloatType
      );

      this.useGPUPhysics = true;
      this.gpuPhysicsInitialized = true;

      console.log('GPU physics initialized with Transform Feedback');
    } catch (error) {
      console.warn('GPU physics initialization failed:', error);
      this.useGPUPhysics = false;
      this.cleanupGPUPhysics();
    }
  }

  /**
   * Set up vertex attribute pointers for particle VAO
   */
  private setupParticleVAO(gl: WebGL2RenderingContext, vao: WebGLVertexArrayObject, vbo: WebGLBuffer): void {
    gl.bindVertexArray(vao);
    gl.bindBuffer(gl.ARRAY_BUFFER, vbo);

    const stride = PARTICLE_STRIDE * 4; // Bytes per particle

    // Position (3 floats at offset 0)
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 3, gl.FLOAT, false, stride, 0);

    // Velocity (3 floats at offset 12)
    gl.enableVertexAttribArray(1);
    gl.vertexAttribPointer(1, 3, gl.FLOAT, false, stride, 12);

    // Life (2 floats at offset 24: age, lifetime)
    gl.enableVertexAttribArray(2);
    gl.vertexAttribPointer(2, 2, gl.FLOAT, false, stride, 24);

    // Physical (2 floats at offset 32: mass, size)
    gl.enableVertexAttribArray(3);
    gl.vertexAttribPointer(3, 2, gl.FLOAT, false, stride, 32);

    // Rotation (2 floats at offset 40: rotation, angularVelocity)
    gl.enableVertexAttribArray(4);
    gl.vertexAttribPointer(4, 2, gl.FLOAT, false, stride, 40);

    // Color (4 floats at offset 48: RGBA)
    gl.enableVertexAttribArray(5);
    gl.vertexAttribPointer(5, 4, gl.FLOAT, false, stride, 48);

    gl.bindVertexArray(null);
  }

  /**
   * Create the transform feedback shader program for GPU physics
   */
  private createTransformFeedbackProgram(gl: WebGL2RenderingContext): WebGLProgram | null {
    const vsSource = TRANSFORM_FEEDBACK_VERTEX_SHADER;
    const fsSource = TRANSFORM_FEEDBACK_FRAGMENT_SHADER;

    const vs = gl.createShader(gl.VERTEX_SHADER);
    const fs = gl.createShader(gl.FRAGMENT_SHADER);

    if (!vs || !fs) return null;

    gl.shaderSource(vs, vsSource);
    gl.compileShader(vs);

    if (!gl.getShaderParameter(vs, gl.COMPILE_STATUS)) {
      console.error('Transform feedback vertex shader error:', gl.getShaderInfoLog(vs));
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      return null;
    }

    gl.shaderSource(fs, fsSource);
    gl.compileShader(fs);

    if (!gl.getShaderParameter(fs, gl.COMPILE_STATUS)) {
      console.error('Transform feedback fragment shader error:', gl.getShaderInfoLog(fs));
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      return null;
    }

    const program = gl.createProgram();
    if (!program) {
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      return null;
    }

    gl.attachShader(program, vs);
    gl.attachShader(program, fs);

    // Specify transform feedback varyings before linking
    gl.transformFeedbackVaryings(program, TF_VARYINGS, gl.INTERLEAVED_ATTRIBS);

    gl.linkProgram(program);

    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
      console.error('Transform feedback program link error:', gl.getProgramInfoLog(program));
      gl.deleteProgram(program);
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      return null;
    }

    gl.deleteShader(vs);
    gl.deleteShader(fs);

    return program;
  }

  /**
   * Clean up GPU physics resources
   */
  private cleanupGPUPhysics(): void {
    if (!this.gl) return;
    const gl = this.gl;

    if (this.transformFeedbackProgram) {
      gl.deleteProgram(this.transformFeedbackProgram);
      this.transformFeedbackProgram = null;
    }

    if (this.particleVboA) {
      gl.deleteBuffer(this.particleVboA);
      this.particleVboA = null;
    }

    if (this.particleVboB) {
      gl.deleteBuffer(this.particleVboB);
      this.particleVboB = null;
    }

    if (this.vaoA) {
      gl.deleteVertexArray(this.vaoA);
      this.vaoA = null;
    }

    if (this.vaoB) {
      gl.deleteVertexArray(this.vaoB);
      this.vaoB = null;
    }

    if (this.transformFeedbackA) {
      gl.deleteTransformFeedback(this.transformFeedbackA);
      this.transformFeedbackA = null;
    }

    if (this.transformFeedbackB) {
      gl.deleteTransformFeedback(this.transformFeedbackB);
      this.transformFeedbackB = null;
    }

    this.forceFieldTexture?.dispose();
    this.forceFieldTexture = null;
  }

  /**
   * Enable or disable GPU physics
   */
  setGPUPhysicsEnabled(enabled: boolean): void {
    if (enabled && !this.gpuPhysicsInitialized) {
      this.initializeGPUPhysics();
    }
    this.useGPUPhysics = enabled && this.gpuPhysicsInitialized;
  }

  /**
   * Check if GPU physics is currently enabled
   */
  isGPUPhysicsEnabled(): boolean {
    return this.useGPUPhysics;
  }

  /**
   * Create textures for lifetime modulation curves
   */
  private createModulationTextures(): void {
    const resolution = 256;

    // Size over lifetime
    const sizeData = new Float32Array(resolution);
    this.sampleModulationCurve(this.config.lifetimeModulation.sizeOverLifetime, sizeData);
    this.sizeOverLifetimeTexture = new THREE.DataTexture(
      sizeData, resolution, 1, THREE.RedFormat, THREE.FloatType
    );
    this.sizeOverLifetimeTexture.needsUpdate = true;

    // Opacity over lifetime
    const opacityData = new Float32Array(resolution);
    this.sampleModulationCurve(this.config.lifetimeModulation.opacityOverLifetime, opacityData);
    this.opacityOverLifetimeTexture = new THREE.DataTexture(
      opacityData, resolution, 1, THREE.RedFormat, THREE.FloatType
    );
    this.opacityOverLifetimeTexture.needsUpdate = true;

    // Color over lifetime
    const colorStops = this.config.lifetimeModulation.colorOverLifetime || [
      { time: 0, color: [1, 1, 1, 1] },
      { time: 1, color: [1, 1, 1, 1] },
    ];
    const colorData = new Float32Array(resolution * 4);
    for (let i = 0; i < resolution; i++) {
      const t = i / (resolution - 1);
      const color = this.sampleColorGradient(colorStops, t);
      colorData[i * 4] = color[0];
      colorData[i * 4 + 1] = color[1];
      colorData[i * 4 + 2] = color[2];
      colorData[i * 4 + 3] = color[3];
    }
    this.colorOverLifetimeTexture = new THREE.DataTexture(
      colorData, resolution, 1, THREE.RGBAFormat, THREE.FloatType
    );
    this.colorOverLifetimeTexture.needsUpdate = true;
  }

  /**
   * Sample a modulation curve into a float array
   */
  private sampleModulationCurve(curve: ModulationCurve | undefined, output: Float32Array): void {
    const len = output.length;

    if (!curve) {
      output.fill(1);
      return;
    }

    for (let i = 0; i < len; i++) {
      const t = i / (len - 1);
      output[i] = this.evaluateModulationCurve(curve, t);
    }
  }

  /**
   * Evaluate a modulation curve at time t
   */
  private evaluateModulationCurve(curve: ModulationCurve, t: number): number {
    switch (curve.type) {
      case 'constant':
        return curve.value;

      case 'linear':
        return curve.start + (curve.end - curve.start) * t;

      case 'curve': {
        // Find surrounding keyframes
        const points = curve.points;
        if (points.length === 0) return 1;
        if (points.length === 1) return points[0].value;

        let p0 = points[0];
        let p1 = points[points.length - 1];

        for (let i = 0; i < points.length - 1; i++) {
          if (t >= points[i].time && t <= points[i + 1].time) {
            p0 = points[i];
            p1 = points[i + 1];
            break;
          }
        }

        const localT = (t - p0.time) / (p1.time - p0.time);
        // Hermite interpolation
        const t2 = localT * localT;
        const t3 = t2 * localT;
        const h1 = 2 * t3 - 3 * t2 + 1;
        const h2 = -2 * t3 + 3 * t2;
        const h3 = t3 - 2 * t2 + localT;
        const h4 = t3 - t2;

        return h1 * p0.value + h2 * p1.value +
               h3 * (p0.outTangent ?? 0) + h4 * (p1.inTangent ?? 0);
      }

      case 'random':
        return curve.min + this.rng() * (curve.max - curve.min);

      case 'randomCurve': {
        const min = this.evaluateModulationCurve(curve.minCurve, t);
        const max = this.evaluateModulationCurve(curve.maxCurve, t);
        return min + this.rng() * (max - min);
      }

      default:
        return 1;
    }
  }

  /**
   * Sample color gradient at time t
   */
  private sampleColorGradient(
    stops: Array<{ time: number; color: [number, number, number, number] }>,
    t: number
  ): [number, number, number, number] {
    if (stops.length === 0) return [1, 1, 1, 1];
    if (stops.length === 1) return stops[0].color;

    // Find surrounding stops
    let s0 = stops[0];
    let s1 = stops[stops.length - 1];

    for (let i = 0; i < stops.length - 1; i++) {
      if (t >= stops[i].time && t <= stops[i + 1].time) {
        s0 = stops[i];
        s1 = stops[i + 1];
        break;
      }
    }

    const localT = (t - s0.time) / (s1.time - s0.time);

    return [
      s0.color[0] + (s1.color[0] - s0.color[0]) * localT,
      s0.color[1] + (s1.color[1] - s0.color[1]) * localT,
      s0.color[2] + (s1.color[2] - s0.color[2]) * localT,
      s0.color[3] + (s1.color[3] - s0.color[3]) * localT,
    ];
  }

  /**
   * Create the Three.js mesh for particle rendering
   */
  private createParticleMesh(): void {
    // Create quad geometry for billboards
    const quadVertices = new Float32Array([
      -1, -1,  1, -1,  1, 1,
      -1, -1,  1, 1,  -1, 1,
    ]);
    const quadUVs = new Float32Array([
      0, 0,  1, 0,  1, 1,
      0, 0,  1, 1,  0, 1,
    ]);

    this.instancedGeometry = new THREE.InstancedBufferGeometry();
    this.instancedGeometry.setAttribute('position', new THREE.BufferAttribute(quadVertices, 2));
    this.instancedGeometry.setAttribute('uv', new THREE.BufferAttribute(quadUVs, 2));

    // Create instanced attributes from particle buffer
    const positionAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 3), 3
    );
    const velocityAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 3), 3
    );
    const lifeAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 2), 2
    );
    const physicalAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 2), 2
    );
    const rotationAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 2), 2
    );
    const colorAttr = new THREE.InstancedBufferAttribute(
      new Float32Array(this.config.maxParticles * 4), 4
    );

    positionAttr.setUsage(THREE.DynamicDrawUsage);
    velocityAttr.setUsage(THREE.DynamicDrawUsage);
    lifeAttr.setUsage(THREE.DynamicDrawUsage);
    physicalAttr.setUsage(THREE.DynamicDrawUsage);
    rotationAttr.setUsage(THREE.DynamicDrawUsage);
    colorAttr.setUsage(THREE.DynamicDrawUsage);

    this.instancedGeometry.setAttribute('i_position', positionAttr);
    this.instancedGeometry.setAttribute('i_velocity', velocityAttr);
    this.instancedGeometry.setAttribute('i_life', lifeAttr);
    this.instancedGeometry.setAttribute('i_physical', physicalAttr);
    this.instancedGeometry.setAttribute('i_rotation', rotationAttr);
    this.instancedGeometry.setAttribute('i_color', colorAttr);

    // Create shader material
    this.material = new THREE.ShaderMaterial({
      vertexShader: PARTICLE_VERTEX_SHADER,
      fragmentShader: PARTICLE_FRAGMENT_SHADER,
      uniforms: this.createUniforms(),
      transparent: true,
      depthWrite: this.config.render.depthWrite,
      depthTest: this.config.render.depthTest,
      blending: this.getThreeBlending(),
    });

    this.particleMesh = new THREE.Mesh(this.instancedGeometry, this.material);
    this.particleMesh.frustumCulled = false;
  }

  // ============================================================================
  // Emitter Management
  // ============================================================================

  addEmitter(config: EmitterConfig): void {
    this.emitters.set(config.id, {
      ...config,
      accumulator: 0,
      velocity: new THREE.Vector3(),
    });
    this.state.activeEmitters = this.emitters.size;
    this.invalidateCache(); // Emitter changes require re-simulation
  }

  updateEmitter(id: string, updates: Partial<EmitterConfig>): void {
    const emitter = this.emitters.get(id);
    if (emitter) {
      Object.assign(emitter, updates);
      this.invalidateCache(); // Emitter changes require re-simulation
    }
  }

  removeEmitter(id: string): void {
    this.emitters.delete(id);
    this.state.activeEmitters = this.emitters.size;
    this.invalidateCache(); // Emitter changes require re-simulation
  }

  getEmitter(id: string): EmitterConfig | undefined {
    return this.emitters.get(id);
  }

  // ============================================================================
  // Force Field Management
  // ============================================================================

  addForceField(config: ForceFieldConfig): void {
    this.forceFields.set(config.id, config);
    this.invalidateCache(); // Force field changes require re-simulation
  }

  updateForceField(id: string, updates: Partial<ForceFieldConfig>): void {
    const field = this.forceFields.get(id);
    if (field) {
      Object.assign(field, updates);
      this.invalidateCache(); // Force field changes require re-simulation
    }
  }

  removeForceField(id: string): void {
    this.forceFields.delete(id);
    this.invalidateCache(); // Force field changes require re-simulation
  }

  // ============================================================================
  // Sub-Emitter Management
  // ============================================================================

  addSubEmitter(config: SubEmitterConfig): void {
    this.subEmitters.set(config.id, config);
    this.invalidateCache(); // Sub-emitter changes require re-simulation
  }

  removeSubEmitter(id: string): void {
    this.subEmitters.delete(id);
    this.invalidateCache(); // Sub-emitter changes require re-simulation
  }

  // ============================================================================
  // Simulation
  // ============================================================================

  /**
   * Step the particle simulation forward
   */
  step(deltaTime: number): void {
    const startTime = performance.now();

    const dt = this.config.deltaTimeMode === 'fixed'
      ? this.config.fixedDeltaTime
      : deltaTime * this.config.timeScale;

    // 1. Emit new particles
    this.emitParticles(dt);

    // 2. Update physics - GPU or CPU
    if (this.useGPUPhysics && this.gl) {
      this.updatePhysicsGPU(dt);
    } else {
      this.updatePhysics(dt);
    }

    // 3. Handle sub-emitter triggers
    this.processSubEmitters();

    // 4. Update spatial hash for flocking
    if (this.config.flocking?.enabled) {
      this.updateSpatialHash();
      this.applyFlocking(dt);
    }

    // 5. Apply audio modulation
    this.applyAudioModulation();

    // 6. Update instance buffers
    this.updateInstanceBuffers();

    // Update state
    this.state.simulationTime += dt;
    this.state.frameCount++;
    this.state.updateTimeMs = performance.now() - startTime;
  }

  /**
   * Emit particles from all active emitters
   */
  private emitParticles(dt: number): void {
    for (const emitter of this.emitters.values()) {
      if (!emitter.enabled) continue;

      // Get audio-modulated emission rate
      let emissionRate = emitter.emissionRate;
      const audioMod = this.getAudioModulation('emitter', emitter.id, 'emissionRate');
      if (audioMod !== undefined) {
        emissionRate *= audioMod;
      }

      // Check for beat-triggered burst
      if (emitter.burstOnBeat && this.audioFeatures.get('beat') === 1) {
        const burstCount = Math.floor(emitter.burstCount * emitter.beatEmissionMultiplier);
        for (let i = 0; i < burstCount; i++) {
          this.spawnParticle(emitter);
        }
      }

      // Regular emission
      emitter.accumulator += emissionRate * dt;

      while (emitter.accumulator >= 1) {
        this.spawnParticle(emitter);
        emitter.accumulator -= 1;
      }
    }
  }

  /**
   * Spawn a single particle from an emitter
   */
  private spawnParticle(emitter: EmitterConfig & { velocity: THREE.Vector3 }): number {
    if (this.freeIndices.length === 0) {
      // Find oldest particle to recycle
      let oldestIndex = 0;
      let oldestAge = 0;
      const buffer = this.currentBuffer === 'A' ? this.particleBufferA : this.particleBufferB;

      for (let i = 0; i < this.config.maxParticles; i++) {
        const age = buffer[i * PARTICLE_STRIDE + 6];
        if (age > oldestAge) {
          oldestAge = age;
          oldestIndex = i;
        }
      }
      this.freeIndices.push(oldestIndex);
    }

    const index = this.freeIndices.pop()!;
    const buffer = this.currentBuffer === 'A' ? this.particleBufferA : this.particleBufferB;
    const offset = index * PARTICLE_STRIDE;

    // Calculate spawn position based on emitter shape
    const pos = this.getEmitterPosition(emitter);

    // Calculate initial velocity
    const dir = this.getEmissionDirection(emitter);
    const speed = emitter.initialSpeed + (this.rng() - 0.5) * 2 * emitter.speedVariance;

    // Inherit emitter velocity
    const inheritVel = emitter.velocity.clone().multiplyScalar(emitter.inheritEmitterVelocity);

    // Write particle data
    buffer[offset + 0] = pos.x;
    buffer[offset + 1] = pos.y;
    buffer[offset + 2] = pos.z;

    buffer[offset + 3] = dir.x * speed + inheritVel.x;
    buffer[offset + 4] = dir.y * speed + inheritVel.y;
    buffer[offset + 5] = dir.z * speed + inheritVel.z;

    buffer[offset + 6] = 0;  // age
    buffer[offset + 7] = emitter.lifetime + (this.rng() - 0.5) * 2 * emitter.lifetimeVariance;

    buffer[offset + 8] = emitter.initialMass + (this.rng() - 0.5) * 2 * emitter.massVariance;
    buffer[offset + 9] = emitter.initialSize + (this.rng() - 0.5) * 2 * emitter.sizeVariance;

    buffer[offset + 10] = emitter.initialRotation + this.rng() * emitter.rotationVariance;
    buffer[offset + 11] = emitter.initialAngularVelocity + (this.rng() - 0.5) * 2 * emitter.angularVelocityVariance;

    // Interpolate color
    const colorT = this.rng() * emitter.colorVariance;
    buffer[offset + 12] = emitter.colorStart[0] + (emitter.colorEnd[0] - emitter.colorStart[0]) * colorT;
    buffer[offset + 13] = emitter.colorStart[1] + (emitter.colorEnd[1] - emitter.colorStart[1]) * colorT;
    buffer[offset + 14] = emitter.colorStart[2] + (emitter.colorEnd[2] - emitter.colorStart[2]) * colorT;
    buffer[offset + 15] = emitter.colorStart[3];

    this.state.particleCount++;
    this.emit('particleBirth', { index, emitterId: emitter.id });

    return index;
  }

  /**
   * Get spawn position based on emitter shape
   */
  private getEmitterPosition(emitter: EmitterConfig): THREE.Vector3 {
    const shape = emitter.shape;
    const base = new THREE.Vector3(emitter.position.x, emitter.position.y, emitter.position.z);

    switch (shape.type) {
      case 'point':
        return base;

      case 'circle': {
        const angle = this.rng() * Math.PI * 2;
        let radius = shape.radius ?? 50;
        if (!shape.emitFromEdge) {
          radius *= Math.sqrt(this.rng());  // Uniform distribution in circle
        }
        return base.add(new THREE.Vector3(
          Math.cos(angle) * radius,
          Math.sin(angle) * radius,
          0
        ));
      }

      case 'sphere': {
        const theta = this.rng() * Math.PI * 2;
        const phi = Math.acos(2 * this.rng() - 1);
        let radius = shape.radius ?? 50;
        if (!shape.emitFromEdge) {
          radius *= Math.cbrt(this.rng());  // Uniform distribution in sphere
        }
        return base.add(new THREE.Vector3(
          Math.sin(phi) * Math.cos(theta) * radius,
          Math.sin(phi) * Math.sin(theta) * radius,
          Math.cos(phi) * radius
        ));
      }

      case 'box': {
        const size = shape.boxSize ?? { x: 100, y: 100, z: 100 };
        return base.add(new THREE.Vector3(
          (this.rng() - 0.5) * size.x,
          (this.rng() - 0.5) * size.y,
          (this.rng() - 0.5) * size.z
        ));
      }

      case 'line': {
        const start = shape.lineStart ?? { x: -50, y: 0, z: 0 };
        const end = shape.lineEnd ?? { x: 50, y: 0, z: 0 };
        const t = this.rng();
        return base.add(new THREE.Vector3(
          start.x + (end.x - start.x) * t,
          start.y + (end.y - start.y) * t,
          start.z + (end.z - start.z) * t
        ));
      }

      case 'cone': {
        const angle = this.rng() * Math.PI * 2;
        const t = this.rng();
        const radius = t * (shape.coneRadius ?? 50);
        const height = t * (shape.coneLength ?? 100);
        return base.add(new THREE.Vector3(
          Math.cos(angle) * radius,
          height,
          Math.sin(angle) * radius
        ));
      }

      case 'image': {
        // Emit from non-transparent pixels of an image
        if (!shape.imageData) return base;

        const { width, height, data } = shape.imageData;
        const threshold = shape.emissionThreshold ?? 0.1;

        // Try up to 100 times to find a valid pixel
        for (let attempt = 0; attempt < 100; attempt++) {
          const px = Math.floor(this.rng() * width);
          const py = Math.floor(this.rng() * height);
          const idx = (py * width + px) * 4;
          const alpha = data[idx + 3] / 255;

          if (alpha > threshold) {
            // Found a valid pixel - return position in image space
            // Center the emission on the emitter position
            return base.add(new THREE.Vector3(
              px - width / 2,
              -(py - height / 2), // Flip Y for screen coords
              0
            ));
          }
        }
        return base; // Fallback to center
      }

      case 'depthEdge': {
        // Emit from depth discontinuities (silhouette edges)
        if (!shape.depthData || !shape.imageData) return base;

        const { width, height } = shape.imageData;
        const depthData = shape.depthData;
        const threshold = shape.emissionThreshold ?? 0.05; // Depth difference threshold

        // Try up to 100 times to find an edge pixel
        for (let attempt = 0; attempt < 100; attempt++) {
          const px = Math.floor(this.rng() * (width - 2)) + 1;
          const py = Math.floor(this.rng() * (height - 2)) + 1;
          const idx = py * width + px;

          // Sample depth and neighbors
          const d = depthData[idx];
          const dLeft = depthData[idx - 1];
          const dRight = depthData[idx + 1];
          const dUp = depthData[idx - width];
          const dDown = depthData[idx + width];

          // Calculate depth gradient magnitude
          const gradX = Math.abs(dRight - dLeft);
          const gradY = Math.abs(dDown - dUp);
          const gradient = Math.sqrt(gradX * gradX + gradY * gradY);

          if (gradient > threshold) {
            // Found an edge pixel
            // Use depth value for Z position (normalized 0-1, scale to reasonable range)
            const z = d * 500; // Scale depth to world units

            return base.add(new THREE.Vector3(
              px - width / 2,
              -(py - height / 2), // Flip Y for screen coords
              z
            ));
          }
        }
        return base; // Fallback to center
      }

      default:
        return base;
    }
  }

  /**
   * Get emission direction based on emitter settings
   */
  private getEmissionDirection(emitter: EmitterConfig): THREE.Vector3 {
    const baseDir = new THREE.Vector3(
      emitter.emissionDirection.x,
      emitter.emissionDirection.y,
      emitter.emissionDirection.z
    ).normalize();

    if (emitter.emissionSpread <= 0) {
      return baseDir;
    }

    // Apply spread (cone distribution)
    const spreadRad = (emitter.emissionSpread * Math.PI) / 180;
    const theta = this.rng() * Math.PI * 2;
    const phi = Math.acos(1 - this.rng() * (1 - Math.cos(spreadRad)));

    // Create rotation from base direction
    const up = Math.abs(baseDir.y) < 0.99
      ? new THREE.Vector3(0, 1, 0)
      : new THREE.Vector3(1, 0, 0);
    const right = new THREE.Vector3().crossVectors(up, baseDir).normalize();
    const realUp = new THREE.Vector3().crossVectors(baseDir, right);

    return new THREE.Vector3()
      .addScaledVector(baseDir, Math.cos(phi))
      .addScaledVector(right, Math.sin(phi) * Math.cos(theta))
      .addScaledVector(realUp, Math.sin(phi) * Math.sin(theta))
      .normalize();
  }

  /**
   * Update particle physics (CPU implementation)
   */
  private updatePhysics(dt: number): void {
    const buffer = this.currentBuffer === 'A' ? this.particleBufferA : this.particleBufferB;

    for (let i = 0; i < this.config.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;

      const age = buffer[offset + 6];
      const lifetime = buffer[offset + 7];

      // Skip dead particles
      if (lifetime <= 0 || age >= lifetime) continue;

      // Read particle state
      let px = buffer[offset + 0];
      let py = buffer[offset + 1];
      let pz = buffer[offset + 2];
      let vx = buffer[offset + 3];
      let vy = buffer[offset + 4];
      let vz = buffer[offset + 5];
      const mass = buffer[offset + 8];

      // Accumulate forces
      let fx = 0, fy = 0, fz = 0;

      // Apply force fields
      for (const field of this.forceFields.values()) {
        if (!field.enabled) continue;

        const force = this.calculateForceField(field, px, py, pz, vx, vy, vz, mass);
        fx += force.x;
        fy += force.y;
        fz += force.z;
      }

      // Apply acceleration (F = ma)
      const ax = fx / Math.max(mass, 0.1);
      const ay = fy / Math.max(mass, 0.1);
      const az = fz / Math.max(mass, 0.1);

      // Integrate velocity
      vx += ax * dt;
      vy += ay * dt;
      vz += az * dt;

      // Integrate position
      px += vx * dt;
      py += vy * dt;
      pz += vz * dt;

      // Apply lifetime modulation
      const lifeRatio = age / lifetime;
      const sizeMod = this.evaluateModulationCurve(
        this.config.lifetimeModulation.sizeOverLifetime || { type: 'constant', value: 1 },
        lifeRatio
      );
      const opacityMod = this.evaluateModulationCurve(
        this.config.lifetimeModulation.opacityOverLifetime || { type: 'constant', value: 1 },
        lifeRatio
      );

      // Update rotation
      const rotation = buffer[offset + 10] + buffer[offset + 11] * dt;

      // Write updated state
      buffer[offset + 0] = px;
      buffer[offset + 1] = py;
      buffer[offset + 2] = pz;
      buffer[offset + 3] = vx;
      buffer[offset + 4] = vy;
      buffer[offset + 5] = vz;
      buffer[offset + 6] = age + dt;
      buffer[offset + 9] *= sizeMod;
      buffer[offset + 10] = rotation;
      buffer[offset + 15] *= opacityMod;

      // Check if particle died
      if (age + dt >= lifetime) {
        this.freeIndices.push(i);
        this.state.particleCount--;
        this.emit('particleDeath', { index: i });
      }
    }
  }

  /**
   * Update particle physics using GPU Transform Feedback
   * This runs the entire physics simulation on the GPU for maximum performance
   */
  private updatePhysicsGPU(dt: number): void {
    if (!this.gl || !this.transformFeedbackProgram) return;

    const gl = this.gl;

    // Update force field texture data
    this.updateForceFieldTexture();

    // Use transform feedback program
    gl.useProgram(this.transformFeedbackProgram);

    // Set uniforms
    const dtLoc = gl.getUniformLocation(this.transformFeedbackProgram, 'u_deltaTime');
    const timeLoc = gl.getUniformLocation(this.transformFeedbackProgram, 'u_time');
    const ffCountLoc = gl.getUniformLocation(this.transformFeedbackProgram, 'u_forceFieldCount');
    const ffTexLoc = gl.getUniformLocation(this.transformFeedbackProgram, 'u_forceFields');

    gl.uniform1f(dtLoc, dt);
    gl.uniform1f(timeLoc, this.state.simulationTime);
    gl.uniform1i(ffCountLoc, Math.min(this.forceFields.size, MAX_FORCE_FIELDS));

    // Bind force field texture
    if (this.forceFieldTexture) {
      gl.activeTexture(gl.TEXTURE0);
      const textureProps = this.renderer?.properties.get(this.forceFieldTexture) as { __webglTexture?: WebGLTexture } | undefined;
      const tex = textureProps?.__webglTexture;
      if (tex) {
        gl.bindTexture(gl.TEXTURE_2D, tex);
        gl.uniform1i(ffTexLoc, 0);
      }
    }

    // Determine which buffers to use (ping-pong)
    const readVAO = this.currentBuffer === 'A' ? this.vaoA : this.vaoB;
    const writeTF = this.currentBuffer === 'A' ? this.transformFeedbackA : this.transformFeedbackB;
    const writeVBO = this.currentBuffer === 'A' ? this.particleVboB : this.particleVboA;

    // Bind read VAO
    gl.bindVertexArray(readVAO);

    // Disable rasterization (we only need transform feedback output)
    gl.enable(gl.RASTERIZER_DISCARD);

    // Begin transform feedback
    gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, writeTF);
    gl.beginTransformFeedback(gl.POINTS);

    // Draw all particles (one vertex per particle)
    gl.drawArrays(gl.POINTS, 0, this.config.maxParticles);

    // End transform feedback
    gl.endTransformFeedback();
    gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, null);

    // Re-enable rasterization
    gl.disable(gl.RASTERIZER_DISCARD);

    // Unbind VAO
    gl.bindVertexArray(null);

    // Swap buffers for next frame
    this.currentBuffer = this.currentBuffer === 'A' ? 'B' : 'A';

    // Read back particle data for CPU-side operations (death handling, etc.)
    // This is a GPU->CPU transfer and can be expensive, so we do it selectively
    if (this.state.frameCount % 10 === 0) {
      this.readBackParticleData(writeVBO);
    }
  }

  /**
   * Update the force field texture with current force field data
   */
  private updateForceFieldTexture(): void {
    if (!this.forceFieldBuffer || !this.forceFieldTexture) return;

    let fieldIndex = 0;
    for (const field of this.forceFields.values()) {
      if (fieldIndex >= MAX_FORCE_FIELDS) break;
      if (!field.enabled) continue;

      const baseOffset = fieldIndex * 16;

      // Row 0: position.xyz, type
      this.forceFieldBuffer[baseOffset + 0] = field.position.x;
      this.forceFieldBuffer[baseOffset + 1] = field.position.y;
      this.forceFieldBuffer[baseOffset + 2] = field.position.z;
      this.forceFieldBuffer[baseOffset + 3] = this.getForceFieldTypeIndex(field.type);

      // Row 1: strength, falloffStart, falloffEnd, falloffType
      this.forceFieldBuffer[baseOffset + 4] = field.strength;
      this.forceFieldBuffer[baseOffset + 5] = field.falloffStart;
      this.forceFieldBuffer[baseOffset + 6] = field.falloffEnd;
      this.forceFieldBuffer[baseOffset + 7] = this.getFalloffTypeIndex(field.falloffType);

      // Row 2: direction/axis.xyz, extra param (inward force for vortex)
      this.forceFieldBuffer[baseOffset + 8] = field.direction?.x ?? field.vortexAxis?.x ?? field.windDirection?.x ?? 0;
      this.forceFieldBuffer[baseOffset + 9] = field.direction?.y ?? field.vortexAxis?.y ?? field.windDirection?.y ?? 0;
      this.forceFieldBuffer[baseOffset + 10] = field.direction?.z ?? field.vortexAxis?.z ?? field.windDirection?.z ?? 0;
      this.forceFieldBuffer[baseOffset + 11] = field.inwardForce ?? 0;

      // Row 3: extra params (noise scale, speed, linear drag, quad drag, gust strength, gust freq)
      this.forceFieldBuffer[baseOffset + 12] = field.noiseScale ?? field.linearDrag ?? field.gustStrength ?? 0;
      this.forceFieldBuffer[baseOffset + 13] = field.noiseSpeed ?? field.quadraticDrag ?? field.gustFrequency ?? 0;
      this.forceFieldBuffer[baseOffset + 14] = 0;
      this.forceFieldBuffer[baseOffset + 15] = 0;

      fieldIndex++;
    }

    this.forceFieldTexture.needsUpdate = true;
  }

  /**
   * Get numeric index for force field type (for GPU shader)
   */
  private getForceFieldTypeIndex(type: ForceFieldConfig['type']): number {
    switch (type) {
      case 'gravity': return 0;
      case 'point': return 1;
      case 'vortex': return 2;
      case 'turbulence': return 3;
      case 'drag': return 4;
      case 'wind': return 5;
      case 'curl': return 6;
      case 'magnetic': return 7;
      case 'lorenz': return 8;
      default: return 0;
    }
  }

  /**
   * Get numeric index for falloff type (for GPU shader)
   */
  private getFalloffTypeIndex(type: ForceFieldConfig['falloffType']): number {
    switch (type) {
      case 'none': return 0;
      case 'linear': return 1;
      case 'quadratic': return 2;
      case 'exponential': return 3;
      case 'smoothstep': return 4;
      default: return 0;
    }
  }

  /**
   * Read back particle data from GPU to CPU for death handling
   */
  private readBackParticleData(vbo: WebGLBuffer | null): void {
    if (!this.gl || !vbo) return;

    const gl = this.gl;
    const targetBuffer = this.currentBuffer === 'A' ? this.particleBufferA : this.particleBufferB;

    gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
    gl.getBufferSubData(gl.ARRAY_BUFFER, 0, targetBuffer);
    gl.bindBuffer(gl.ARRAY_BUFFER, null);

    // Process deaths
    let activeCount = 0;
    for (let i = 0; i < this.config.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const age = targetBuffer[offset + 6];
      const lifetime = targetBuffer[offset + 7];

      if (lifetime > 0 && age < lifetime) {
        activeCount++;
      } else if (lifetime > 0 && age >= lifetime) {
        // Particle just died
        if (!this.freeIndices.includes(i)) {
          this.freeIndices.push(i);
          this.emit('particleDeath', { index: i });
        }
      }
    }

    this.state.particleCount = activeCount;
  }

  /**
   * Calculate force from a force field
   */
  private calculateForceField(
    field: ForceFieldConfig,
    px: number, py: number, pz: number,
    vx: number, vy: number, vz: number,
    mass: number
  ): THREE.Vector3 {
    const force = new THREE.Vector3();

    // Calculate distance and falloff
    const dx = px - field.position.x;
    const dy = py - field.position.y;
    const dz = pz - field.position.z;
    const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);

    let falloff = 1;
    if (dist > field.falloffStart) {
      const t = Math.min((dist - field.falloffStart) / (field.falloffEnd - field.falloffStart), 1);
      switch (field.falloffType) {
        case 'linear': falloff = 1 - t; break;
        case 'quadratic': falloff = 1 - t * t; break;
        case 'exponential': falloff = Math.exp(-t * 3); break;
        case 'smoothstep': falloff = 1 - (3 * t * t - 2 * t * t * t); break;
      }
    }

    const strength = field.strength * falloff;

    switch (field.type) {
      case 'gravity':
        force.set(
          (field.direction?.x ?? 0) * strength,
          (field.direction?.y ?? 1) * strength,
          (field.direction?.z ?? 0) * strength
        );
        break;

      case 'point':
        if (dist > 0.001) {
          const dir = new THREE.Vector3(-dx, -dy, -dz).normalize();
          force.copy(dir).multiplyScalar(strength / mass);
        }
        break;

      case 'vortex':
        if (dist > 0.001) {
          const axis = new THREE.Vector3(
            field.vortexAxis?.x ?? 0,
            field.vortexAxis?.y ?? 0,
            field.vortexAxis?.z ?? 1
          ).normalize();
          const toParticle = new THREE.Vector3(dx, dy, dz);
          const tangent = new THREE.Vector3().crossVectors(axis, toParticle).normalize();
          const inward = toParticle.normalize().multiplyScalar(-(field.inwardForce ?? 0));
          force.copy(tangent).multiplyScalar(strength).add(inward);
        }
        break;

      case 'turbulence': {
        const scale = field.noiseScale ?? 0.01;
        const speed = field.noiseSpeed ?? 0.5;
        const time = this.state.simulationTime * speed;

        // Simple 3D noise approximation
        const nx = Math.sin(px * scale + time) * Math.cos(py * scale * 1.3) * strength;
        const ny = Math.sin(py * scale + time * 1.1) * Math.cos(pz * scale * 1.2) * strength;
        const nz = Math.sin(pz * scale + time * 0.9) * Math.cos(px * scale * 1.1) * strength;
        force.set(nx, ny, nz);
        break;
      }

      case 'drag': {
        const speed = Math.sqrt(vx * vx + vy * vy + vz * vz);
        if (speed > 0.001) {
          const dragMag = (field.linearDrag ?? 0.1) * speed +
                         (field.quadraticDrag ?? 0.01) * speed * speed;
          force.set(-vx, -vy, -vz).normalize().multiplyScalar(-dragMag * strength);
        }
        break;
      }

      case 'wind': {
        const windDir = new THREE.Vector3(
          field.windDirection?.x ?? 1,
          field.windDirection?.y ?? 0,
          field.windDirection?.z ?? 0
        ).normalize();
        const gust = Math.sin(this.state.simulationTime * (field.gustFrequency ?? 0.5)) *
                    (field.gustStrength ?? 0);
        force.copy(windDir).multiplyScalar(strength + gust);
        break;
      }

      case 'lorenz': {
        const sigma = field.lorenzSigma ?? 10;
        const rho = field.lorenzRho ?? 28;
        const beta = field.lorenzBeta ?? 2.667;
        force.set(
          sigma * (dy - dx),
          dx * (rho - dz) - dy,
          dx * dy - beta * dz
        ).multiplyScalar(strength * 0.01);
        break;
      }
    }

    return force;
  }

  /**
   * Process sub-emitter triggers
   */
  private processSubEmitters(): void {
    // This would check for death events and trigger sub-emitters
    // Simplified for now
  }

  /**
   * Update spatial hash for neighbor queries
   */
  private updateSpatialHash(): void {
    this.spatialHash.clear();
    const buffer = this.currentBuffer === 'A' ? this.particleBufferA : this.particleBufferB;
    const cellSize = this.config.spatialHashCellSize;

    for (let i = 0; i < this.config.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      if (lifetime <= 0) continue;

      const px = buffer[offset + 0];
      const py = buffer[offset + 1];
      const pz = buffer[offset + 2];

      const cellX = Math.floor(px / cellSize);
      const cellY = Math.floor(py / cellSize);
      const cellZ = Math.floor(pz / cellSize);
      const key = `${cellX},${cellY},${cellZ}`;

      if (!this.spatialHash.has(key)) {
        this.spatialHash.set(key, []);
      }
      this.spatialHash.get(key)!.push(i);
    }
  }

  /**
   * Apply flocking behaviors
   */
  private applyFlocking(dt: number): void {
    const config = this.config.flocking;
    if (!config?.enabled) return;

    const buffer = this.currentBuffer === 'A' ? this.particleBufferA : this.particleBufferB;
    const cellSize = this.config.spatialHashCellSize;

    for (let i = 0; i < this.config.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = buffer[offset + 7];
      if (lifetime <= 0) continue;

      const px = buffer[offset + 0];
      const py = buffer[offset + 1];
      const pz = buffer[offset + 2];

      // Find neighbors
      const cellX = Math.floor(px / cellSize);
      const cellY = Math.floor(py / cellSize);
      const cellZ = Math.floor(pz / cellSize);

      const separation = new THREE.Vector3();
      const alignment = new THREE.Vector3();
      const cohesion = new THREE.Vector3();
      let separationCount = 0;
      let alignmentCount = 0;
      let cohesionCount = 0;

      // Check neighboring cells
      for (let cx = cellX - 1; cx <= cellX + 1; cx++) {
        for (let cy = cellY - 1; cy <= cellY + 1; cy++) {
          for (let cz = cellZ - 1; cz <= cellZ + 1; cz++) {
            const neighbors = this.spatialHash.get(`${cx},${cy},${cz}`);
            if (!neighbors) continue;

            for (const j of neighbors) {
              if (j === i) continue;

              const jOffset = j * PARTICLE_STRIDE;
              const jx = buffer[jOffset + 0];
              const jy = buffer[jOffset + 1];
              const jz = buffer[jOffset + 2];

              const dx = px - jx;
              const dy = py - jy;
              const dz = pz - jz;
              const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);

              // Separation
              if (dist < config.separationRadius && dist > 0) {
                separation.add(new THREE.Vector3(dx, dy, dz).divideScalar(dist));
                separationCount++;
              }

              // Alignment
              if (dist < config.alignmentRadius) {
                alignment.add(new THREE.Vector3(
                  buffer[jOffset + 3],
                  buffer[jOffset + 4],
                  buffer[jOffset + 5]
                ));
                alignmentCount++;
              }

              // Cohesion
              if (dist < config.cohesionRadius) {
                cohesion.add(new THREE.Vector3(jx, jy, jz));
                cohesionCount++;
              }
            }
          }
        }
      }

      // Apply forces
      if (separationCount > 0) {
        separation.divideScalar(separationCount).normalize().multiplyScalar(config.separationWeight);
      }
      if (alignmentCount > 0) {
        alignment.divideScalar(alignmentCount).normalize().multiplyScalar(config.alignmentWeight);
      }
      if (cohesionCount > 0) {
        cohesion.divideScalar(cohesionCount);
        cohesion.sub(new THREE.Vector3(px, py, pz)).normalize().multiplyScalar(config.cohesionWeight);
      }

      const steering = separation.add(alignment).add(cohesion);
      if (steering.length() > config.maxForce) {
        steering.normalize().multiplyScalar(config.maxForce);
      }

      buffer[offset + 3] += steering.x * dt;
      buffer[offset + 4] += steering.y * dt;
      buffer[offset + 5] += steering.z * dt;

      // Limit speed
      const speed = Math.sqrt(
        buffer[offset + 3] ** 2 +
        buffer[offset + 4] ** 2 +
        buffer[offset + 5] ** 2
      );
      if (speed > config.maxSpeed) {
        const scale = config.maxSpeed / speed;
        buffer[offset + 3] *= scale;
        buffer[offset + 4] *= scale;
        buffer[offset + 5] *= scale;
      }
    }
  }

  /**
   * Apply audio modulation to parameters
   */
  private applyAudioModulation(): void {
    for (const binding of this.config.audioBindings) {
      const featureValue = this.audioFeatures.get(binding.feature) ?? 0;

      // Apply smoothing
      const smoothed = featureValue;  // Would use exponential smoothing

      // Map to output range
      const t = (smoothed - binding.min) / (binding.max - binding.min);
      let output = binding.outputMin + t * (binding.outputMax - binding.outputMin);

      // Apply curve
      if (binding.curve === 'exponential') {
        output = binding.outputMin + Math.pow(t, 2) * (binding.outputMax - binding.outputMin);
      } else if (binding.curve === 'logarithmic') {
        output = binding.outputMin + Math.sqrt(t) * (binding.outputMax - binding.outputMin);
      }

      // Apply to target
      if (binding.target === 'emitter') {
        const emitter = this.emitters.get(binding.targetId);
        if (emitter) {
          (emitter as any)[binding.parameter] = output;
        }
      } else if (binding.target === 'forceField') {
        const field = this.forceFields.get(binding.targetId);
        if (field) {
          (field as any)[binding.parameter] = output;
        }
      }
    }
  }

  /**
   * Get audio modulation for a specific parameter
   */
  private getAudioModulation(target: string, targetId: string, parameter: string): number | undefined {
    for (const binding of this.config.audioBindings) {
      if (binding.target === target && binding.targetId === targetId && binding.parameter === parameter) {
        const featureValue = this.audioFeatures.get(binding.feature) ?? 0;
        const t = (featureValue - binding.min) / (binding.max - binding.min);
        return binding.outputMin + t * (binding.outputMax - binding.outputMin);
      }
    }
    return undefined;
  }

  /**
   * Update instance buffer attributes for rendering
   */
  private updateInstanceBuffers(): void {
    if (!this.instancedGeometry) return;

    const buffer = this.currentBuffer === 'A' ? this.particleBufferA : this.particleBufferB;

    const posAttr = this.instancedGeometry.getAttribute('i_position') as THREE.InstancedBufferAttribute;
    const velAttr = this.instancedGeometry.getAttribute('i_velocity') as THREE.InstancedBufferAttribute;
    const lifeAttr = this.instancedGeometry.getAttribute('i_life') as THREE.InstancedBufferAttribute;
    const physAttr = this.instancedGeometry.getAttribute('i_physical') as THREE.InstancedBufferAttribute;
    const rotAttr = this.instancedGeometry.getAttribute('i_rotation') as THREE.InstancedBufferAttribute;
    const colAttr = this.instancedGeometry.getAttribute('i_color') as THREE.InstancedBufferAttribute;

    // Copy data from particle buffer to instance attributes
    for (let i = 0; i < this.config.maxParticles; i++) {
      const src = i * PARTICLE_STRIDE;

      posAttr.setXYZ(i, buffer[src + 0], buffer[src + 1], buffer[src + 2]);
      velAttr.setXYZ(i, buffer[src + 3], buffer[src + 4], buffer[src + 5]);
      lifeAttr.setXY(i, buffer[src + 6], buffer[src + 7]);
      physAttr.setXY(i, buffer[src + 8], buffer[src + 9]);
      rotAttr.setXY(i, buffer[src + 10], buffer[src + 11]);
      colAttr.setXYZW(i, buffer[src + 12], buffer[src + 13], buffer[src + 14], buffer[src + 15]);
    }

    posAttr.needsUpdate = true;
    velAttr.needsUpdate = true;
    lifeAttr.needsUpdate = true;
    physAttr.needsUpdate = true;
    rotAttr.needsUpdate = true;
    colAttr.needsUpdate = true;
  }

  // ============================================================================
  // Audio Integration
  // ============================================================================

  /**
   * Set audio feature value
   */
  setAudioFeature(feature: AudioFeature, value: number): void {
    this.audioFeatures.set(feature, value);
    this.state.currentAudioFeatures.set(feature, value);
  }

  /**
   * Trigger beat event
   */
  triggerBeat(): void {
    this.audioFeatures.set('beat', 1);

    // Reset beat flag after frame
    requestAnimationFrame(() => {
      this.audioFeatures.set('beat', 0);
    });
  }

  /**
   * Trigger burst on all beat-enabled emitters
   */
  triggerBurst(emitterId?: string): void {
    if (emitterId) {
      const emitter = this.emitters.get(emitterId);
      if (emitter) {
        for (let i = 0; i < emitter.burstCount; i++) {
          this.spawnParticle(emitter);
        }
      }
    } else {
      for (const emitter of this.emitters.values()) {
        if (emitter.burstOnBeat && emitter.enabled) {
          for (let i = 0; i < emitter.burstCount; i++) {
            this.spawnParticle(emitter);
          }
        }
      }
    }
  }

  // ============================================================================
  // Rendering
  // ============================================================================

  /**
   * Get the Three.js mesh for adding to scene
   */
  getMesh(): THREE.Mesh | null {
    return this.particleMesh;
  }

  /**
   * Create shader uniforms
   */
  private createUniforms(): Record<string, THREE.IUniform> {
    return {
      diffuseMap: { value: null },
      hasDiffuseMap: { value: 0 },
      proceduralShape: { value: 1 },  // Circle by default
    };
  }

  /**
   * Get Three.js blending mode
   */
  private getThreeBlending(): THREE.Blending {
    switch (this.config.render.blendMode) {
      case 'additive': return THREE.AdditiveBlending;
      case 'multiply': return THREE.MultiplyBlending;
      case 'screen': return THREE.CustomBlending;
      default: return THREE.NormalBlending;
    }
  }

  // ============================================================================
  // Event System
  // ============================================================================

  on(event: string, handler: ParticleEventHandler): void {
    if (!this.eventHandlers.has(event)) {
      this.eventHandlers.set(event, new Set());
    }
    this.eventHandlers.get(event)!.add(handler);
  }

  off(event: string, handler: ParticleEventHandler): void {
    this.eventHandlers.get(event)?.delete(handler);
  }

  private emit(type: string, data: Record<string, unknown>): void {
    const event: ParticleEvent = {
      type: type as any,
      timestamp: performance.now(),
      data,
    };
    this.eventHandlers.get(type)?.forEach(handler => handler(event));
  }

  // ============================================================================
  // Utilities
  // ============================================================================

  /**
   * Create seeded random number generator
   * State is tracked externally via currentRngState for save/restore
   */
  private createSeededRandom(seed: number): () => number {
    this.currentRngState = seed;
    return () => {
      this.currentRngState = (this.currentRngState * 1103515245 + 12345) & 0x7fffffff;
      return this.currentRngState / 0x7fffffff;
    };
  }

  /**
   * Get current state
   */
  getState(): ParticleSystemState {
    return { ...this.state };
  }

  /**
   * Get current configuration (emitters and force fields)
   */
  getConfig(): { emitters: EmitterConfig[]; forceFields: ForceFieldConfig[] } {
    // Extract EmitterConfig from the stored emitters (removing runtime-only fields)
    const emitters: EmitterConfig[] = Array.from(this.emitters.values()).map(e => {
      // eslint-disable-next-line @typescript-eslint/no-unused-vars
      const { accumulator, velocity, ...config } = e;
      return config;
    });

    return {
      emitters,
      forceFields: Array.from(this.forceFields.values()),
    };
  }

  // ============================================================================
  // FRAME CACHING METHODS
  // ============================================================================

  /**
   * Cache the current particle state for a specific frame
   * Called automatically every cacheInterval frames during step()
   */
  cacheCurrentState(frame: number): void {
    // Don't cache if we've exceeded max size - remove oldest
    if (this.frameCache.size >= this.maxCacheSize) {
      const oldestFrame = Math.min(...this.frameCache.keys());
      this.frameCache.delete(oldestFrame);
    }

    // Save emitter accumulators
    const emitterAccumulators = new Map<string, number>();
    for (const [id, emitter] of this.emitters) {
      emitterAccumulators.set(id, emitter.accumulator);
    }

    const currentBuffer = this.currentBuffer === 'A' ? this.particleBufferA : this.particleBufferB;

    this.frameCache.set(frame, {
      frame,
      version: this.cacheVersion,
      particleBuffer: new Float32Array(currentBuffer), // Deep copy
      freeIndices: [...this.freeIndices], // Copy array
      particleCount: this.state.particleCount,
      simulationTime: this.state.simulationTime,
      rngState: this.currentRngState,
      emitterAccumulators,
    });
  }

  /**
   * Restore particle state from a cached frame
   * @returns true if restore succeeded, false if cache miss or version mismatch
   */
  restoreFromCache(frame: number): boolean {
    const cached = this.frameCache.get(frame);
    if (!cached || cached.version !== this.cacheVersion) {
      return false;
    }

    // Restore particle buffers
    const targetBuffer = this.currentBuffer === 'A' ? this.particleBufferA : this.particleBufferB;
    targetBuffer.set(cached.particleBuffer);

    // Restore state
    this.freeIndices = [...cached.freeIndices];
    this.state.particleCount = cached.particleCount;
    this.state.simulationTime = cached.simulationTime;
    this.state.frameCount = frame;
    this.currentSimulatedFrame = frame;

    // Restore RNG state - recreate with state
    this.currentRngState = cached.rngState;
    // The rng function will use currentRngState directly

    // Restore emitter accumulators
    for (const [id, accumulator] of cached.emitterAccumulators) {
      const emitter = this.emitters.get(id);
      if (emitter) {
        emitter.accumulator = accumulator;
      }
    }

    // Update instance buffers for rendering
    this.updateInstanceBuffers();

    return true;
  }

  /**
   * Find the nearest cached frame at or before the target frame
   * @returns The nearest cached frame number, or -1 if no cache exists
   */
  findNearestCache(targetFrame: number): number {
    let nearestFrame = -1;
    for (const frame of this.frameCache.keys()) {
      const cached = this.frameCache.get(frame);
      if (cached && cached.version === this.cacheVersion && frame <= targetFrame && frame > nearestFrame) {
        nearestFrame = frame;
      }
    }
    return nearestFrame;
  }

  /**
   * Clear all cached frames
   */
  clearCache(): void {
    this.frameCache.clear();
    this.currentSimulatedFrame = -1;
  }

  /**
   * Invalidate the cache by incrementing version
   * Called when particle parameters change (emitter config, force fields, etc.)
   */
  invalidateCache(): void {
    this.cacheVersion++;
    // Don't clear the map - old entries will be ignored due to version mismatch
    // This is more memory efficient for frequent invalidations
    this.currentSimulatedFrame = -1;
  }

  /**
   * Simulate particles to a specific frame, using cache when available
   * This is the main entry point for timeline scrubbing
   *
   * @param targetFrame The frame number to simulate to
   * @param fps Frames per second for deltaTime calculation
   * @returns The number of simulation steps performed
   */
  simulateToFrame(targetFrame: number, fps: number = 30): number {
    const deltaTime = 1 / fps;

    // If we're already at this frame, nothing to do
    if (this.currentSimulatedFrame === targetFrame) {
      return 0;
    }

    // Check if we can continue from current position (forward scrubbing)
    if (this.currentSimulatedFrame >= 0 &&
        this.currentSimulatedFrame < targetFrame &&
        targetFrame - this.currentSimulatedFrame <= this.cacheInterval * 2) {
      // Just continue stepping forward
      let steps = 0;
      for (let f = this.currentSimulatedFrame + 1; f <= targetFrame; f++) {
        this.step(deltaTime);
        this.currentSimulatedFrame = f;

        // Cache at intervals
        if (f % this.cacheInterval === 0) {
          this.cacheCurrentState(f);
        }
        steps++;
      }
      return steps;
    }

    // Find nearest cached frame before target
    const nearestCache = this.findNearestCache(targetFrame);

    let startFrame = 0;
    if (nearestCache >= 0) {
      // Restore from cache
      if (this.restoreFromCache(nearestCache)) {
        startFrame = nearestCache;
      }
    }

    // If starting from 0, reset first
    if (startFrame === 0) {
      this.reset();
      this.currentSimulatedFrame = 0;
      // Cache frame 0
      this.cacheCurrentState(0);
    }

    // Simulate forward to target frame
    let steps = 0;
    for (let f = startFrame + 1; f <= targetFrame; f++) {
      this.step(deltaTime);
      this.currentSimulatedFrame = f;

      // Cache at intervals
      if (f % this.cacheInterval === 0) {
        this.cacheCurrentState(f);
      }
      steps++;
    }

    return steps;
  }

  /**
   * Get cache statistics for debugging/UI
   */
  getCacheStats(): {
    cachedFrames: number;
    version: number;
    currentFrame: number;
    cacheInterval: number;
    maxCacheSize: number;
  } {
    // Count valid cached frames
    let validCount = 0;
    for (const cached of this.frameCache.values()) {
      if (cached.version === this.cacheVersion) {
        validCount++;
      }
    }

    return {
      cachedFrames: validCount,
      version: this.cacheVersion,
      currentFrame: this.currentSimulatedFrame,
      cacheInterval: this.cacheInterval,
      maxCacheSize: this.maxCacheSize,
    };
  }

  /**
   * Set the cache interval (how often to cache frames)
   */
  setCacheInterval(interval: number): void {
    this.cacheInterval = Math.max(1, interval);
  }

  /**
   * Reset the particle system
   * DETERMINISM: Resets RNG to initial seed for reproducible simulation
   */
  reset(): void {
    this.particleBufferA.fill(0);
    this.particleBufferB.fill(0);
    this.freeIndices = [];
    for (let i = this.config.maxParticles - 1; i >= 0; i--) {
      this.freeIndices.push(i);
    }
    this.state.particleCount = 0;
    this.state.simulationTime = 0;
    this.state.frameCount = 0;
    this.spatialHash.clear();

    // Reset emitter accumulators
    for (const emitter of this.emitters.values()) {
      emitter.accumulator = 0;
    }

    // Reset frame tracking (but don't clear cache - that's done by invalidateCache)
    this.currentSimulatedFrame = -1;

    // Reset RNG to initial seed for deterministic replay
    // This ensures reset() + step(N) always produces same result
    this.rng = this.createSeededRandom(this.config.randomSeed ?? 12345);
  }

  /**
   * Get the current seed
   */
  getSeed(): number {
    return this.config.randomSeed ?? 12345;
  }

  /**
   * Set a new seed and reset the system
   * DETERMINISM: Used to ensure layer-specific reproducible seeds
   */
  setSeed(seed: number): void {
    this.config.randomSeed = seed;
    this.initialRngSeed = seed;
    this.clearCache(); // Seed change invalidates all cached data
    this.reset();
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    // Dispose Three.js resources
    this.instancedGeometry?.dispose();
    this.material?.dispose();
    this.sizeOverLifetimeTexture?.dispose();
    this.opacityOverLifetimeTexture?.dispose();
    this.colorOverLifetimeTexture?.dispose();

    // Dispose GPU physics resources
    this.cleanupGPUPhysics();

    // Clear collections
    this.emitters.clear();
    this.forceFields.clear();
    this.subEmitters.clear();
    this.eventHandlers.clear();
  }
}

export default GPUParticleSystem;
