/**
 * WebGPU Compute Particles
 *
 * GPU-accelerated particle physics using WebGPU compute shaders.
 * Provides massive performance improvements for large particle counts (10k+).
 *
 * Features:
 * - Parallel force computation (gravity, wind, gravity wells, vortices)
 * - GPU-based position/velocity integration
 * - Double-buffered particle data for smooth updates
 * - Automatic fallback to CPU simulation when WebGPU unavailable
 *
 * Architecture:
 * - ParticleData stored in GPU buffers (position, velocity, age, etc.)
 * - Compute shaders run on GPU workgroups (256 particles per workgroup)
 * - Results read back to CPU only for rendering (or kept on GPU for WebGPU rendering)
 */

import { assertDefined } from "@/utils/typeGuards";

// ============================================================================
// TYPES
// ============================================================================

export interface GPUParticleConfig {
  maxParticles: number;
  gravity: number;
  windX: number;
  windY: number;
  friction: number;
  deltaTime: number;
}

export interface GPUGravityWell {
  x: number;
  y: number;
  radius: number;
  strength: number;
  falloff: number; // 0=constant, 1=linear, 2=quadratic
}

export interface GPUVortex {
  x: number;
  y: number;
  radius: number;
  strength: number;
  inwardPull: number;
}

export interface GPUParticleData {
  positions: Float32Array; // [x, y, prevX, prevY] per particle
  velocities: Float32Array; // [vx, vy, 0, 0] per particle
  properties: Float32Array; // [age, lifetime, size, baseSize] per particle
  colors: Float32Array; // [r, g, b, a] per particle
  count: number;
}

export interface WebGPUCapabilities {
  available: boolean;
  adapter: GPUAdapter | null;
  device: GPUDevice | null;
  maxWorkgroupSize: number;
  maxBufferSize: number;
}

// ============================================================================
// WEBGPU COMPUTE SHADERS
// ============================================================================

const PARTICLE_UPDATE_SHADER = /* wgsl */ `
// Uniform buffer for simulation config
struct SimConfig {
  gravity: f32,
  windX: f32,
  windY: f32,
  friction: f32,
  deltaTime: f32,
  particleCount: u32,
  gravityWellCount: u32,
  vortexCount: u32,
}

// Gravity well data
struct GravityWell {
  x: f32,
  y: f32,
  radius: f32,
  strength: f32,
  falloff: f32,
  _pad1: f32,
  _pad2: f32,
  _pad3: f32,
}

// Vortex data
struct Vortex {
  x: f32,
  y: f32,
  radius: f32,
  strength: f32,
  inwardPull: f32,
  _pad1: f32,
  _pad2: f32,
  _pad3: f32,
}

@group(0) @binding(0) var<uniform> config: SimConfig;
@group(0) @binding(1) var<storage, read_write> positions: array<vec4<f32>>;
@group(0) @binding(2) var<storage, read_write> velocities: array<vec4<f32>>;
@group(0) @binding(3) var<storage, read_write> properties: array<vec4<f32>>;
@group(0) @binding(4) var<storage, read> gravityWells: array<GravityWell>;
@group(0) @binding(5) var<storage, read> vortices: array<Vortex>;

@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let idx = global_id.x;
  if (idx >= config.particleCount) {
    return;
  }

  // Load particle data
  var pos = positions[idx];
  var vel = velocities[idx];
  var props = properties[idx];

  let x = pos.x;
  let y = pos.y;
  var vx = vel.x;
  var vy = vel.y;
  let age = props.x;
  let lifetime = props.y;

  // Skip dead particles
  if (age > lifetime) {
    return;
  }

  // Store previous position
  pos.z = x;
  pos.w = y;

  // Apply gravity
  vy += config.gravity * 0.001 * config.deltaTime;

  // Apply wind
  vx += config.windX * config.deltaTime;
  vy += config.windY * config.deltaTime;

  // Apply gravity wells
  for (var i = 0u; i < config.gravityWellCount; i++) {
    let well = gravityWells[i];
    let dx = well.x - x;
    let dy = well.y - y;
    let dist = sqrt(dx * dx + dy * dy);

    if (dist < well.radius && dist > 0.001) {
      var force = well.strength * 0.0001;

      // Apply falloff
      if (well.falloff == 1.0) {
        // Linear
        force *= 1.0 - (dist / well.radius);
      } else if (well.falloff == 2.0) {
        // Quadratic
        let t = 1.0 - (dist / well.radius);
        force *= t * t;
      }
      // falloff == 0.0 is constant (no modification)

      // Normalize and apply
      let nx = dx / dist;
      let ny = dy / dist;
      vx += nx * force * config.deltaTime;
      vy += ny * force * config.deltaTime;
    }
  }

  // Apply vortices
  for (var i = 0u; i < config.vortexCount; i++) {
    let vortex = vortices[i];
    let dx = vortex.x - x;
    let dy = vortex.y - y;
    let dist = sqrt(dx * dx + dy * dy);

    if (dist < vortex.radius && dist > 0.001) {
      let influence = 1.0 - (dist / vortex.radius);
      let strength = vortex.strength * 0.0001 * influence;

      // Perpendicular (tangential) force
      let nx = dx / dist;
      let ny = dy / dist;
      let perpX = -ny;
      let perpY = nx;

      vx += perpX * strength * config.deltaTime;
      vy += perpY * strength * config.deltaTime;

      // Inward pull
      let inward = vortex.inwardPull * 0.0001 * influence;
      vx += nx * inward * config.deltaTime;
      vy += ny * inward * config.deltaTime;
    }
  }

  // Apply friction
  let frictionFactor = 1.0 - config.friction;
  vx *= frictionFactor;
  vy *= frictionFactor;

  // Update position
  pos.x = x + vx * config.deltaTime;
  pos.y = y + vy * config.deltaTime;

  // Update velocity
  vel.x = vx;
  vel.y = vy;

  // Increment age
  props.x = age + config.deltaTime;

  // Write back
  positions[idx] = pos;
  velocities[idx] = vel;
  properties[idx] = props;
}
`;

const PARTICLE_SIZE_MODULATION_SHADER = /* wgsl */ `
struct ModConfig {
  particleCount: u32,
  sizeOverLifeEnabled: u32,
  sizeStart: f32,
  sizeEnd: f32,
  easingType: u32,  // 0=linear, 1=easeIn, 2=easeOut, 3=easeInOut
  _pad1: f32,
  _pad2: f32,
  _pad3: f32,
}

@group(0) @binding(0) var<uniform> config: ModConfig;
@group(0) @binding(1) var<storage, read_write> properties: array<vec4<f32>>;

fn easeInQuad(t: f32) -> f32 {
  return t * t;
}

fn easeOutQuad(t: f32) -> f32 {
  return t * (2.0 - t);
}

fn easeInOutQuad(t: f32) -> f32 {
  if (t < 0.5) {
    return 2.0 * t * t;
  }
  return -1.0 + (4.0 - 2.0 * t) * t;
}

@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) global_id: vec3<u32>) {
  let idx = global_id.x;
  if (idx >= config.particleCount) {
    return;
  }

  var props = properties[idx];
  let age = props.x;
  let lifetime = props.y;
  let baseSize = props.w;

  if (age > lifetime) {
    return;
  }

  if (config.sizeOverLifeEnabled == 1u) {
    var t = clamp(age / lifetime, 0.0, 1.0);

    // Apply easing
    if (config.easingType == 1u) {
      t = easeInQuad(t);
    } else if (config.easingType == 2u) {
      t = easeOutQuad(t);
    } else if (config.easingType == 3u) {
      t = easeInOutQuad(t);
    }

    let sizeMult = mix(config.sizeStart, config.sizeEnd, t);
    props.z = baseSize * sizeMult;
  }

  properties[idx] = props;
}
`;

// ============================================================================
// WEBGPU PARTICLE COMPUTE ENGINE
// ============================================================================

export class ParticleGPUCompute {
  private device: GPUDevice | null = null;
  private adapter: GPUAdapter | null = null;

  // Pipelines
  private updatePipeline: GPUComputePipeline | null = null;
  private modulationPipeline: GPUComputePipeline | null = null;

  // Buffers
  private positionBuffer: GPUBuffer | null = null;
  private velocityBuffer: GPUBuffer | null = null;
  private propertiesBuffer: GPUBuffer | null = null;
  private colorBuffer: GPUBuffer | null = null;
  private configBuffer: GPUBuffer | null = null;
  private gravityWellBuffer: GPUBuffer | null = null;
  private vortexBuffer: GPUBuffer | null = null;
  private modulationConfigBuffer: GPUBuffer | null = null;

  // Staging buffers for readback
  private stagingPositionBuffer: GPUBuffer | null = null;
  private stagingVelocityBuffer: GPUBuffer | null = null;
  private stagingPropertiesBuffer: GPUBuffer | null = null;
  private stagingColorBuffer: GPUBuffer | null = null;

  // Bind groups
  private updateBindGroup: GPUBindGroup | null = null;
  private modulationBindGroup: GPUBindGroup | null = null;

  // Config
  private maxParticles: number = 0;
  private initialized: boolean = false;

  // Static capability check
  private static _capabilities: WebGPUCapabilities | null = null;

  // ============================================================================
  // STATIC METHODS
  // ============================================================================

  /**
   * Check WebGPU availability and capabilities
   */
  static async checkCapabilities(): Promise<WebGPUCapabilities> {
    if (ParticleGPUCompute._capabilities) {
      return ParticleGPUCompute._capabilities;
    }

    if (!navigator.gpu) {
      ParticleGPUCompute._capabilities = {
        available: false,
        adapter: null,
        device: null,
        maxWorkgroupSize: 0,
        maxBufferSize: 0,
      };
      return ParticleGPUCompute._capabilities;
    }

    try {
      const adapter = await navigator.gpu.requestAdapter({
        powerPreference: "high-performance",
      });

      if (!adapter) {
        ParticleGPUCompute._capabilities = {
          available: false,
          adapter: null,
          device: null,
          maxWorkgroupSize: 0,
          maxBufferSize: 0,
        };
        return ParticleGPUCompute._capabilities;
      }

      const device = await adapter.requestDevice({
        requiredLimits: {
          maxStorageBufferBindingSize:
            adapter.limits.maxStorageBufferBindingSize,
          maxComputeWorkgroupSizeX: 256,
        },
      });

      ParticleGPUCompute._capabilities = {
        available: true,
        adapter,
        device,
        maxWorkgroupSize: device.limits.maxComputeWorkgroupSizeX,
        maxBufferSize: device.limits.maxStorageBufferBindingSize,
      };

      return ParticleGPUCompute._capabilities;
    } catch (error) {
      console.warn("WebGPU initialization failed:", error);
      ParticleGPUCompute._capabilities = {
        available: false,
        adapter: null,
        device: null,
        maxWorkgroupSize: 0,
        maxBufferSize: 0,
      };
      return ParticleGPUCompute._capabilities;
    }
  }

  /**
   * Check if WebGPU compute is available
   */
  static async isAvailable(): Promise<boolean> {
    const caps = await ParticleGPUCompute.checkCapabilities();
    return caps.available;
  }

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Initialize the GPU compute engine
   */
  async initialize(maxParticles: number): Promise<boolean> {
    const caps = await ParticleGPUCompute.checkCapabilities();

    if (!caps.available || !caps.device) {
      console.warn("WebGPU not available, using CPU fallback");
      return false;
    }

    this.device = caps.device;
    this.adapter = caps.adapter;
    // Validate maxParticles to prevent buffer allocation errors
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.min(Math.floor(maxParticles), 1_000_000)
      : 10000;

    try {
      // Create compute pipelines
      await this.createPipelines();

      // Create buffers
      this.createBuffers();

      this.initialized = true;
      console.log(
        `WebGPU Particle Compute initialized for ${maxParticles} particles`,
      );
      return true;
    } catch (error) {
      console.error("Failed to initialize WebGPU compute:", error);
      this.dispose();
      return false;
    }
  }

  /**
   * Create compute shader pipelines
   */
  private async createPipelines(): Promise<void> {
    if (!this.device) return;

    // Update pipeline
    const updateShaderModule = this.device.createShaderModule({
      label: "Particle Update Shader",
      code: PARTICLE_UPDATE_SHADER,
    });

    this.updatePipeline = this.device.createComputePipeline({
      label: "Particle Update Pipeline",
      layout: "auto",
      compute: {
        module: updateShaderModule,
        entryPoint: "main",
      },
    });

    // Modulation pipeline
    const modulationShaderModule = this.device.createShaderModule({
      label: "Particle Modulation Shader",
      code: PARTICLE_SIZE_MODULATION_SHADER,
    });

    this.modulationPipeline = this.device.createComputePipeline({
      label: "Particle Modulation Pipeline",
      layout: "auto",
      compute: {
        module: modulationShaderModule,
        entryPoint: "main",
      },
    });
  }

  /**
   * Create GPU buffers for particle data
   */
  private createBuffers(): void {
    if (!this.device) return;

    const particleCount = this.maxParticles;

    // Position buffer: [x, y, prevX, prevY] per particle
    this.positionBuffer = this.device.createBuffer({
      label: "Particle Positions",
      size: particleCount * 4 * 4, // 4 floats * 4 bytes
      usage:
        GPUBufferUsage.STORAGE |
        GPUBufferUsage.COPY_DST |
        GPUBufferUsage.COPY_SRC,
    });

    // Velocity buffer: [vx, vy, 0, 0] per particle
    this.velocityBuffer = this.device.createBuffer({
      label: "Particle Velocities",
      size: particleCount * 4 * 4,
      usage:
        GPUBufferUsage.STORAGE |
        GPUBufferUsage.COPY_DST |
        GPUBufferUsage.COPY_SRC,
    });

    // Properties buffer: [age, lifetime, size, baseSize] per particle
    this.propertiesBuffer = this.device.createBuffer({
      label: "Particle Properties",
      size: particleCount * 4 * 4,
      usage:
        GPUBufferUsage.STORAGE |
        GPUBufferUsage.COPY_DST |
        GPUBufferUsage.COPY_SRC,
    });

    // Color buffer: [r, g, b, a] per particle
    this.colorBuffer = this.device.createBuffer({
      label: "Particle Colors",
      size: particleCount * 4 * 4,
      usage:
        GPUBufferUsage.STORAGE |
        GPUBufferUsage.COPY_DST |
        GPUBufferUsage.COPY_SRC,
    });

    // Config uniform buffer (must be 16-byte aligned)
    this.configBuffer = this.device.createBuffer({
      label: "Simulation Config",
      size: 32, // 8 values * 4 bytes, aligned to 16
      usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST,
    });

    // Gravity wells buffer (16 max)
    this.gravityWellBuffer = this.device.createBuffer({
      label: "Gravity Wells",
      size: 16 * 8 * 4, // 16 wells * 8 floats * 4 bytes
      usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
    });

    // Vortex buffer (16 max)
    this.vortexBuffer = this.device.createBuffer({
      label: "Vortices",
      size: 16 * 8 * 4, // 16 vortices * 8 floats * 4 bytes
      usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
    });

    // Modulation config buffer
    this.modulationConfigBuffer = this.device.createBuffer({
      label: "Modulation Config",
      size: 32, // 8 values * 4 bytes
      usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST,
    });

    // Staging buffers for readback
    this.stagingPositionBuffer = this.device.createBuffer({
      label: "Staging Positions",
      size: particleCount * 4 * 4,
      usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST,
    });

    this.stagingVelocityBuffer = this.device.createBuffer({
      label: "Staging Velocities",
      size: particleCount * 4 * 4,
      usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST,
    });

    this.stagingPropertiesBuffer = this.device.createBuffer({
      label: "Staging Properties",
      size: particleCount * 4 * 4,
      usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST,
    });

    this.stagingColorBuffer = this.device.createBuffer({
      label: "Staging Colors",
      size: particleCount * 4 * 4,
      usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST,
    });
  }

  // ============================================================================
  // DATA UPLOAD
  // ============================================================================

  /**
   * Upload particle data to GPU
   */
  uploadParticles(data: GPUParticleData): void {
    if (!this.device || !this.initialized) return;

    // Type proof: All buffers must exist after initialization
    assertDefined(this.positionBuffer, "positionBuffer must exist after initialization");
    assertDefined(this.velocityBuffer, "velocityBuffer must exist after initialization");
    assertDefined(this.propertiesBuffer, "propertiesBuffer must exist after initialization");
    assertDefined(this.colorBuffer, "colorBuffer must exist after initialization");

    // Cast Float32Array to BufferSource for WebGPU compatibility
    this.device.queue.writeBuffer(
      this.positionBuffer,
      0,
      data.positions as BufferSource,
    );
    this.device.queue.writeBuffer(
      this.velocityBuffer,
      0,
      data.velocities as BufferSource,
    );
    this.device.queue.writeBuffer(
      this.propertiesBuffer,
      0,
      data.properties as BufferSource,
    );
    this.device.queue.writeBuffer(
      this.colorBuffer,
      0,
      data.colors as BufferSource,
    );
  }

  /**
   * Upload simulation config to GPU
   */
  uploadConfig(
    config: GPUParticleConfig,
    gravityWells: GPUGravityWell[],
    vortices: GPUVortex[],
  ): void {
    if (!this.device || !this.initialized) return;

    // Config buffer
    const configData = new Float32Array([
      config.gravity,
      config.windX,
      config.windY,
      config.friction,
      config.deltaTime,
      0,
      0,
      0, // Padding for alignment
    ]);
    // Pack counts as uint32
    const configView = new DataView(configData.buffer);
    configView.setUint32(20, config.maxParticles, true);
    configView.setUint32(24, gravityWells.length, true);
    configView.setUint32(28, vortices.length, true);

    // Type proof: All buffers must exist after initialization
    assertDefined(this.configBuffer, "configBuffer must exist after initialization");
    assertDefined(this.gravityWellBuffer, "gravityWellBuffer must exist after initialization");
    assertDefined(this.vortexBuffer, "vortexBuffer must exist after initialization");

    this.device.queue.writeBuffer(this.configBuffer, 0, configData);

    // Gravity wells
    const wellData = new Float32Array(16 * 8);
    gravityWells.forEach((well, i) => {
      if (i >= 16) return;
      const offset = i * 8;
      wellData[offset + 0] = well.x;
      wellData[offset + 1] = well.y;
      wellData[offset + 2] = well.radius;
      wellData[offset + 3] = well.strength;
      wellData[offset + 4] = well.falloff;
    });
    this.device.queue.writeBuffer(this.gravityWellBuffer, 0, wellData);

    // Vortices
    const vortexData = new Float32Array(16 * 8);
    vortices.forEach((vortex, i) => {
      if (i >= 16) return;
      const offset = i * 8;
      vortexData[offset + 0] = vortex.x;
      vortexData[offset + 1] = vortex.y;
      vortexData[offset + 2] = vortex.radius;
      vortexData[offset + 3] = vortex.strength;
      vortexData[offset + 4] = vortex.inwardPull;
    });
    this.device.queue.writeBuffer(this.vortexBuffer, 0, vortexData);
  }

  // ============================================================================
  // COMPUTE DISPATCH
  // ============================================================================

  /**
   * Run the particle update compute shader
   */
  dispatchUpdate(particleCount: number): void {
    if (!this.device || !this.initialized || !this.updatePipeline) return;

    // Create bind group if needed
    if (!this.updateBindGroup) {
      // Type proof: All buffers must exist after initialization
      assertDefined(this.configBuffer, "configBuffer must exist after initialization");
      assertDefined(this.positionBuffer, "positionBuffer must exist after initialization");
      assertDefined(this.velocityBuffer, "velocityBuffer must exist after initialization");
      assertDefined(this.propertiesBuffer, "propertiesBuffer must exist after initialization");
      assertDefined(this.gravityWellBuffer, "gravityWellBuffer must exist after initialization");
      assertDefined(this.vortexBuffer, "vortexBuffer must exist after initialization");

      this.updateBindGroup = this.device.createBindGroup({
        label: "Update Bind Group",
        layout: this.updatePipeline.getBindGroupLayout(0),
        entries: [
          { binding: 0, resource: { buffer: this.configBuffer } },
          { binding: 1, resource: { buffer: this.positionBuffer } },
          { binding: 2, resource: { buffer: this.velocityBuffer } },
          { binding: 3, resource: { buffer: this.propertiesBuffer } },
          { binding: 4, resource: { buffer: this.gravityWellBuffer } },
          { binding: 5, resource: { buffer: this.vortexBuffer } },
        ],
      });
    }

    const commandEncoder = this.device.createCommandEncoder();
    const passEncoder = commandEncoder.beginComputePass();

    passEncoder.setPipeline(this.updatePipeline);
    passEncoder.setBindGroup(0, this.updateBindGroup);

    // Dispatch workgroups (256 particles per workgroup)
    const workgroupCount = Math.ceil(particleCount / 256);
    passEncoder.dispatchWorkgroups(workgroupCount);

    passEncoder.end();
    this.device.queue.submit([commandEncoder.finish()]);
  }

  /**
   * Run the size modulation compute shader
   */
  dispatchModulation(
    particleCount: number,
    sizeOverLifeEnabled: boolean,
    sizeStart: number,
    sizeEnd: number,
    easingType: number,
  ): void {
    if (!this.device || !this.initialized || !this.modulationPipeline) return;

    // Upload modulation config
    const modConfig = new Uint32Array([
      particleCount,
      sizeOverLifeEnabled ? 1 : 0,
      0,
      0, // Will be replaced with floats
    ]);
    const modConfigView = new DataView(modConfig.buffer);
    modConfigView.setFloat32(8, sizeStart, true);
    modConfigView.setFloat32(12, sizeEnd, true);
    modConfigView.setUint32(16, easingType, true);

    // Type proof: Buffers must exist after initialization
    assertDefined(this.modulationConfigBuffer, "modulationConfigBuffer must exist after initialization");
    assertDefined(this.propertiesBuffer, "propertiesBuffer must exist after initialization");

    this.device.queue.writeBuffer(this.modulationConfigBuffer, 0, modConfig);

    // Create bind group if needed
    if (!this.modulationBindGroup) {
      this.modulationBindGroup = this.device.createBindGroup({
        label: "Modulation Bind Group",
        layout: this.modulationPipeline.getBindGroupLayout(0),
        entries: [
          { binding: 0, resource: { buffer: this.modulationConfigBuffer } },
          { binding: 1, resource: { buffer: this.propertiesBuffer } },
        ],
      });
    }

    const commandEncoder = this.device.createCommandEncoder();
    const passEncoder = commandEncoder.beginComputePass();

    passEncoder.setPipeline(this.modulationPipeline);
    passEncoder.setBindGroup(0, this.modulationBindGroup);

    const workgroupCount = Math.ceil(particleCount / 256);
    passEncoder.dispatchWorkgroups(workgroupCount);

    passEncoder.end();
    this.device.queue.submit([commandEncoder.finish()]);
  }

  // ============================================================================
  // DATA READBACK
  // ============================================================================

  /**
   * Read particle data back from GPU
   * Note: This is async and can be slow - prefer keeping data on GPU when possible
   */
  async readbackParticles(particleCount: number): Promise<GPUParticleData> {
    if (!this.device || !this.initialized) {
      return {
        positions: new Float32Array(0),
        velocities: new Float32Array(0),
        properties: new Float32Array(0),
        colors: new Float32Array(0),
        count: 0,
      };
    }

    const byteSize = particleCount * 4 * 4;

    // Type proof: All buffers must exist after initialization
    assertDefined(this.positionBuffer, "positionBuffer must exist after initialization");
    assertDefined(this.velocityBuffer, "velocityBuffer must exist after initialization");
    assertDefined(this.propertiesBuffer, "propertiesBuffer must exist after initialization");
    assertDefined(this.colorBuffer, "colorBuffer must exist after initialization");
    assertDefined(this.stagingPositionBuffer, "stagingPositionBuffer must exist after initialization");
    assertDefined(this.stagingVelocityBuffer, "stagingVelocityBuffer must exist after initialization");
    assertDefined(this.stagingPropertiesBuffer, "stagingPropertiesBuffer must exist after initialization");
    assertDefined(this.stagingColorBuffer, "stagingColorBuffer must exist after initialization");

    // Copy to staging buffers
    const commandEncoder = this.device.createCommandEncoder();
    commandEncoder.copyBufferToBuffer(
      this.positionBuffer,
      0,
      this.stagingPositionBuffer,
      0,
      byteSize,
    );
    commandEncoder.copyBufferToBuffer(
      this.velocityBuffer,
      0,
      this.stagingVelocityBuffer,
      0,
      byteSize,
    );
    commandEncoder.copyBufferToBuffer(
      this.propertiesBuffer,
      0,
      this.stagingPropertiesBuffer,
      0,
      byteSize,
    );
    commandEncoder.copyBufferToBuffer(
      this.colorBuffer,
      0,
      this.stagingColorBuffer,
      0,
      byteSize,
    );
    this.device.queue.submit([commandEncoder.finish()]);

    // Map and read staging buffers
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingPositionBuffer === "object" && this.stagingPositionBuffer !== null && "mapAsync" in this.stagingPositionBuffer && typeof this.stagingPositionBuffer.mapAsync === "function") {
      await this.stagingPositionBuffer.mapAsync(GPUMapMode.READ);
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingVelocityBuffer === "object" && this.stagingVelocityBuffer !== null && "mapAsync" in this.stagingVelocityBuffer && typeof this.stagingVelocityBuffer.mapAsync === "function") {
      await this.stagingVelocityBuffer.mapAsync(GPUMapMode.READ);
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingPropertiesBuffer === "object" && this.stagingPropertiesBuffer !== null && "mapAsync" in this.stagingPropertiesBuffer && typeof this.stagingPropertiesBuffer.mapAsync === "function") {
      await this.stagingPropertiesBuffer.mapAsync(GPUMapMode.READ);
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingColorBuffer === "object" && this.stagingColorBuffer !== null && "mapAsync" in this.stagingColorBuffer && typeof this.stagingColorBuffer.mapAsync === "function") {
      await this.stagingColorBuffer.mapAsync(GPUMapMode.READ);
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/null checks
    // Pattern match: getMappedRange() ∈ ArrayBuffer | undefined → ArrayBuffer | []
    let positions: Float32Array;
    if (typeof this.stagingPositionBuffer === "object" && this.stagingPositionBuffer !== null && "getMappedRange" in this.stagingPositionBuffer && typeof this.stagingPositionBuffer.getMappedRange === "function") {
      const posRange = this.stagingPositionBuffer.getMappedRange();
      positions = Array.isArray(posRange) ? new Float32Array(posRange.slice(0)) : new Float32Array(0);
    } else {
      positions = new Float32Array(0);
    }
    
    let velocities: Float32Array;
    if (typeof this.stagingVelocityBuffer === "object" && this.stagingVelocityBuffer !== null && "getMappedRange" in this.stagingVelocityBuffer && typeof this.stagingVelocityBuffer.getMappedRange === "function") {
      const velRange = this.stagingVelocityBuffer.getMappedRange();
      velocities = Array.isArray(velRange) ? new Float32Array(velRange.slice(0)) : new Float32Array(0);
    } else {
      velocities = new Float32Array(0);
    }
    
    let properties: Float32Array;
    if (typeof this.stagingPropertiesBuffer === "object" && this.stagingPropertiesBuffer !== null && "getMappedRange" in this.stagingPropertiesBuffer && typeof this.stagingPropertiesBuffer.getMappedRange === "function") {
      const propRange = this.stagingPropertiesBuffer.getMappedRange();
      properties = Array.isArray(propRange) ? new Float32Array(propRange.slice(0)) : new Float32Array(0);
    } else {
      properties = new Float32Array(0);
    }
    
    let colors: Float32Array;
    if (typeof this.stagingColorBuffer === "object" && this.stagingColorBuffer !== null && "getMappedRange" in this.stagingColorBuffer && typeof this.stagingColorBuffer.getMappedRange === "function") {
      const colorRange = this.stagingColorBuffer.getMappedRange();
      colors = Array.isArray(colorRange) ? new Float32Array(colorRange.slice(0)) : new Float32Array(0);
    } else {
      colors = new Float32Array(0);
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingPositionBuffer === "object" && this.stagingPositionBuffer !== null && "unmap" in this.stagingPositionBuffer && typeof this.stagingPositionBuffer.unmap === "function") {
      this.stagingPositionBuffer.unmap();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingVelocityBuffer === "object" && this.stagingVelocityBuffer !== null && "unmap" in this.stagingVelocityBuffer && typeof this.stagingVelocityBuffer.unmap === "function") {
      this.stagingVelocityBuffer.unmap();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingPropertiesBuffer === "object" && this.stagingPropertiesBuffer !== null && "unmap" in this.stagingPropertiesBuffer && typeof this.stagingPropertiesBuffer.unmap === "function") {
      this.stagingPropertiesBuffer.unmap();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingColorBuffer === "object" && this.stagingColorBuffer !== null && "unmap" in this.stagingColorBuffer && typeof this.stagingColorBuffer.unmap === "function") {
      this.stagingColorBuffer.unmap();
    }

    return {
      positions,
      velocities,
      properties,
      colors,
      count: particleCount,
    };
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  /**
   * Dispose GPU resources
   */
  dispose(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.positionBuffer === "object" && this.positionBuffer !== null && "destroy" in this.positionBuffer && typeof this.positionBuffer.destroy === "function") {
      this.positionBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.velocityBuffer === "object" && this.velocityBuffer !== null && "destroy" in this.velocityBuffer && typeof this.velocityBuffer.destroy === "function") {
      this.velocityBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.propertiesBuffer === "object" && this.propertiesBuffer !== null && "destroy" in this.propertiesBuffer && typeof this.propertiesBuffer.destroy === "function") {
      this.propertiesBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.colorBuffer === "object" && this.colorBuffer !== null && "destroy" in this.colorBuffer && typeof this.colorBuffer.destroy === "function") {
      this.colorBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.configBuffer === "object" && this.configBuffer !== null && "destroy" in this.configBuffer && typeof this.configBuffer.destroy === "function") {
      this.configBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.gravityWellBuffer === "object" && this.gravityWellBuffer !== null && "destroy" in this.gravityWellBuffer && typeof this.gravityWellBuffer.destroy === "function") {
      this.gravityWellBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.vortexBuffer === "object" && this.vortexBuffer !== null && "destroy" in this.vortexBuffer && typeof this.vortexBuffer.destroy === "function") {
      this.vortexBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.modulationConfigBuffer === "object" && this.modulationConfigBuffer !== null && "destroy" in this.modulationConfigBuffer && typeof this.modulationConfigBuffer.destroy === "function") {
      this.modulationConfigBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingPositionBuffer === "object" && this.stagingPositionBuffer !== null && "destroy" in this.stagingPositionBuffer && typeof this.stagingPositionBuffer.destroy === "function") {
      this.stagingPositionBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingVelocityBuffer === "object" && this.stagingVelocityBuffer !== null && "destroy" in this.stagingVelocityBuffer && typeof this.stagingVelocityBuffer.destroy === "function") {
      this.stagingVelocityBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingPropertiesBuffer === "object" && this.stagingPropertiesBuffer !== null && "destroy" in this.stagingPropertiesBuffer && typeof this.stagingPropertiesBuffer.destroy === "function") {
      this.stagingPropertiesBuffer.destroy();
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.stagingColorBuffer === "object" && this.stagingColorBuffer !== null && "destroy" in this.stagingColorBuffer && typeof this.stagingColorBuffer.destroy === "function") {
      this.stagingColorBuffer.destroy();
    }

    this.positionBuffer = null;
    this.velocityBuffer = null;
    this.propertiesBuffer = null;
    this.colorBuffer = null;
    this.configBuffer = null;
    this.gravityWellBuffer = null;
    this.vortexBuffer = null;
    this.modulationConfigBuffer = null;
    this.stagingPositionBuffer = null;
    this.stagingVelocityBuffer = null;
    this.stagingPropertiesBuffer = null;
    this.stagingColorBuffer = null;

    this.updateBindGroup = null;
    this.modulationBindGroup = null;
    this.updatePipeline = null;
    this.modulationPipeline = null;

    this.device = null;
    this.adapter = null;
    this.initialized = false;
  }

  /**
   * Check if engine is initialized
   */
  isInitialized(): boolean {
    return this.initialized;
  }

  /**
   * Get max particles this instance supports
   */
  getMaxParticles(): number {
    return this.maxParticles;
  }
}

// ============================================================================
// HYBRID CPU/GPU PARTICLE SYSTEM
// ============================================================================

/**
 * Hybrid particle system that uses GPU compute when available
 * with automatic fallback to CPU simulation
 */
export class HybridParticleSystem {
  private gpu: ParticleGPUCompute | null = null;
  private useGPU: boolean = false;
  private particleCount: number = 0;
  private maxParticles: number;

  // CPU-side particle data (always maintained for compatibility)
  private positions: Float32Array;
  private velocities: Float32Array;
  private properties: Float32Array;
  private colors: Float32Array;

  constructor(maxParticles: number) {
    // Validate maxParticles to prevent Float32Array allocation errors
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.min(Math.floor(maxParticles), 1_000_000)
      : 10000;
    // Allocate CPU arrays
    this.positions = new Float32Array(this.maxParticles * 4);
    this.velocities = new Float32Array(this.maxParticles * 4);
    this.properties = new Float32Array(this.maxParticles * 4);
    this.colors = new Float32Array(this.maxParticles * 4);
  }

  /**
   * Initialize with GPU acceleration if available
   */
  async initialize(): Promise<boolean> {
    const gpuAvailable = await ParticleGPUCompute.isAvailable();

    if (gpuAvailable) {
      this.gpu = new ParticleGPUCompute();
      this.useGPU = await this.gpu.initialize(this.maxParticles);

      if (this.useGPU) {
        console.log("Hybrid particle system: GPU mode enabled");
        return true;
      }
    }

    console.log("Hybrid particle system: CPU mode (WebGPU not available)");
    return false;
  }

  /**
   * Check if GPU acceleration is active
   */
  isGPUEnabled(): boolean {
    return this.useGPU;
  }

  /**
   * Upload particles to GPU (if enabled)
   */
  uploadToGPU(): void {
    if (!this.useGPU || !this.gpu) return;

    this.gpu.uploadParticles({
      positions: this.positions,
      velocities: this.velocities,
      properties: this.properties,
      colors: this.colors,
      count: this.particleCount,
    });
  }

  /**
   * Run simulation step
   */
  async step(
    config: GPUParticleConfig,
    gravityWells: GPUGravityWell[],
    vortices: GPUVortex[],
  ): Promise<void> {
    if (this.useGPU && this.gpu) {
      // GPU path
      this.gpu.uploadConfig(config, gravityWells, vortices);
      this.gpu.dispatchUpdate(this.particleCount);

      // Optionally read back (only if needed for rendering on CPU)
      // const data = await this.gpu.readbackParticles(this.particleCount);
      // ... copy to CPU arrays
    } else {
      // CPU path - basic simulation
      this.stepCPU(config, gravityWells, vortices);
    }
  }

  /**
   * CPU fallback simulation
   */
  private stepCPU(
    config: GPUParticleConfig,
    gravityWells: GPUGravityWell[],
    vortices: GPUVortex[],
  ): void {
    const dt = config.deltaTime;
    const friction = 1 - config.friction;

    for (let i = 0; i < this.particleCount; i++) {
      const pi = i * 4;

      // Load
      let x = this.positions[pi];
      let y = this.positions[pi + 1];
      let vx = this.velocities[pi];
      let vy = this.velocities[pi + 1];
      const age = this.properties[pi];
      const lifetime = this.properties[pi + 1];

      // Skip dead particles
      if (age > lifetime) continue;

      // Store previous position
      this.positions[pi + 2] = x;
      this.positions[pi + 3] = y;

      // Gravity
      vy += config.gravity * 0.001 * dt;

      // Wind
      vx += config.windX * dt;
      vy += config.windY * dt;

      // Gravity wells
      for (const well of gravityWells) {
        const dx = well.x - x;
        const dy = well.y - y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < well.radius && dist > 0.001) {
          let force = well.strength * 0.0001;

          if (well.falloff === 1) {
            force *= 1 - dist / well.radius;
          } else if (well.falloff === 2) {
            const t = 1 - dist / well.radius;
            force *= t * t;
          }

          const nx = dx / dist;
          const ny = dy / dist;
          vx += nx * force * dt;
          vy += ny * force * dt;
        }
      }

      // Vortices
      for (const vortex of vortices) {
        const dx = vortex.x - x;
        const dy = vortex.y - y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < vortex.radius && dist > 0.001) {
          const influence = 1 - dist / vortex.radius;
          const strength = vortex.strength * 0.0001 * influence;

          const nx = dx / dist;
          const ny = dy / dist;
          vx += -ny * strength * dt;
          vy += nx * strength * dt;

          const inward = vortex.inwardPull * 0.0001 * influence;
          vx += nx * inward * dt;
          vy += ny * inward * dt;
        }
      }

      // Friction
      vx *= friction;
      vy *= friction;

      // Update position
      x += vx * dt;
      y += vy * dt;

      // Store
      this.positions[pi] = x;
      this.positions[pi + 1] = y;
      this.velocities[pi] = vx;
      this.velocities[pi + 1] = vy;
      this.properties[pi] = age + dt;
    }
  }

  /**
   * Get particle positions for rendering
   */
  getPositions(): Float32Array {
    return this.positions;
  }

  /**
   * Get particle velocities
   */
  getVelocities(): Float32Array {
    return this.velocities;
  }

  /**
   * Get particle properties (age, lifetime, size, baseSize)
   */
  getProperties(): Float32Array {
    return this.properties;
  }

  /**
   * Get particle colors
   */
  getColors(): Float32Array {
    return this.colors;
  }

  /**
   * Set particle count
   */
  setParticleCount(count: number): void {
    this.particleCount = Math.min(count, this.maxParticles);
  }

  /**
   * Get current particle count
   */
  getParticleCount(): number {
    return this.particleCount;
  }

  /**
   * Add a particle
   */
  addParticle(
    x: number,
    y: number,
    vx: number,
    vy: number,
    lifetime: number,
    size: number,
    r: number,
    g: number,
    b: number,
    a: number,
  ): boolean {
    if (this.particleCount >= this.maxParticles) return false;

    const i = this.particleCount;
    const pi = i * 4;

    this.positions[pi] = x;
    this.positions[pi + 1] = y;
    this.positions[pi + 2] = x; // prevX
    this.positions[pi + 3] = y; // prevY

    this.velocities[pi] = vx;
    this.velocities[pi + 1] = vy;
    this.velocities[pi + 2] = 0;
    this.velocities[pi + 3] = 0;

    this.properties[pi] = 0; // age
    this.properties[pi + 1] = lifetime;
    this.properties[pi + 2] = size;
    this.properties[pi + 3] = size; // baseSize

    this.colors[pi] = r;
    this.colors[pi + 1] = g;
    this.colors[pi + 2] = b;
    this.colors[pi + 3] = a;

    this.particleCount++;
    return true;
  }

  /**
   * Remove dead particles (compact arrays)
   */
  removeDeadParticles(): number {
    let writeIndex = 0;

    for (let i = 0; i < this.particleCount; i++) {
      const pi = i * 4;
      const age = this.properties[pi];
      const lifetime = this.properties[pi + 1];

      if (age <= lifetime) {
        if (writeIndex !== i) {
          // Copy particle data
          const wi = writeIndex * 4;
          this.positions[wi] = this.positions[pi];
          this.positions[wi + 1] = this.positions[pi + 1];
          this.positions[wi + 2] = this.positions[pi + 2];
          this.positions[wi + 3] = this.positions[pi + 3];

          this.velocities[wi] = this.velocities[pi];
          this.velocities[wi + 1] = this.velocities[pi + 1];
          this.velocities[wi + 2] = this.velocities[pi + 2];
          this.velocities[wi + 3] = this.velocities[pi + 3];

          this.properties[wi] = this.properties[pi];
          this.properties[wi + 1] = this.properties[pi + 1];
          this.properties[wi + 2] = this.properties[pi + 2];
          this.properties[wi + 3] = this.properties[pi + 3];

          this.colors[wi] = this.colors[pi];
          this.colors[wi + 1] = this.colors[pi + 1];
          this.colors[wi + 2] = this.colors[pi + 2];
          this.colors[wi + 3] = this.colors[pi + 3];
        }
        writeIndex++;
      }
    }

    const removed = this.particleCount - writeIndex;
    this.particleCount = writeIndex;
    return removed;
  }

  /**
   * Dispose resources
   */
  dispose(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (typeof this.gpu === "object" && this.gpu !== null && "dispose" in this.gpu && typeof this.gpu.dispose === "function") {
      this.gpu.dispose();
    }
    this.gpu = null;
    this.useGPU = false;
  }
}

// ============================================================================
// PREFERENCES INTEGRATION
// ============================================================================

/**
 * Helper to get particle preferences from store
 * Import in components that need to check preferences
 */
export function getParticlePreferences() {
  // Dynamic import to avoid circular dependencies
  // Components should use the store directly via useParticlePreferencesStore()
  return {
    shouldUseGPU: async (): Promise<boolean> => {
      // Check WebGPU availability
      if (typeof navigator !== "undefined" && "gpu" in navigator) {
        try {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
          const adapter = (typeof navigator.gpu === "object" && navigator.gpu !== null && "requestAdapter" in navigator.gpu && typeof navigator.gpu.requestAdapter === "function")
            ? await navigator.gpu.requestAdapter()
            : null;
          return !!adapter;
        } catch {
          return false;
        }
      }
      return false;
    },

    shouldUseGPUCompute: async (): Promise<boolean> => {
      // GPU compute is only for physics, rendering can still use WebGL2
      const hasGPU = await getParticlePreferences().shouldUseGPU();
      return hasGPU;
    },
  };
}

/**
 * Particle system factory - creates the appropriate system based on preferences
 */
export async function createParticleSystem(
  maxParticles: number,
  options: {
    forceBackend?: "webgpu" | "webgl2" | "cpu";
    enableGPUCompute?: boolean;
  } = {},
): Promise<{
  system: HybridParticleSystem;
  backend: "webgpu" | "webgl2" | "cpu";
  gpuComputeEnabled: boolean;
}> {
  const system = new HybridParticleSystem(maxParticles);

  // Check if we should force a specific backend
  if (options.forceBackend === "cpu") {
    return {
      system,
      backend: "cpu",
      gpuComputeEnabled: false,
    };
  }

  // Try GPU initialization
  const gpuEnabled = await system.initialize();

  if (gpuEnabled) {
    return {
      system,
      backend: "webgpu",
      gpuComputeEnabled: options.enableGPUCompute !== false,
    };
  }

  // Fall back to CPU with WebGL2 rendering
  return {
    system,
    backend: "cpu",
    gpuComputeEnabled: false,
  };
}

// ============================================================================
// EXPORTS
// ============================================================================

export default ParticleGPUCompute;
