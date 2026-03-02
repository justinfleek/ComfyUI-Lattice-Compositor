/**
 * GPU-Accelerated Spring/Soft Body System
 *
 * Uses WebGPU compute shaders for high-performance spring simulation.
 * Implements Position-Based Dynamics with Verlet integration.
 */

import { PARTICLE_STRIDE } from "./types";
import type { Spring, SpringSystemConfig } from "./ParticleSpringSystem";
import { ParticleSpringSystem } from "./ParticleSpringSystem";

// Import shader source
import springComputeShader from "./shaders/springCompute.wgsl?raw";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

interface Pin {
  particleIndex: number;
  active: boolean;
  position: { x: number; y: number; z: number };
}

interface GPUSpringBuffers {
  particles: GPUBuffer;
  prevPositions: GPUBuffer;
  springs: GPUBuffer;
  pins: GPUBuffer;
  params: GPUBuffer;
  staging: GPUBuffer;
}

interface GPUSpringPipelines {
  verletIntegrate: GPUComputePipeline;
  solveConstraints: GPUComputePipeline;
  applyPins: GPUComputePipeline;
  eulerForces: GPUComputePipeline;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                   // gpu // spring // system
// ════════════════════════════════════════════════════════════════════════════

export class GPUSpringSystem {
  private device: GPUDevice | null = null;
  private buffers: GPUSpringBuffers | null = null;
  private pipelines: GPUSpringPipelines | null = null;
  private bindGroup: GPUBindGroup | null = null;
  private bindGroupLayout: GPUBindGroupLayout | null = null;

  private maxParticles: number;
  private maxSprings: number;
  private maxPins: number;
  private config: SpringSystemConfig;
  private initialized = false;

  // Spring data (managed on CPU, uploaded to GPU)
  private springs: Spring[] = [];
  private pins: Pin[] = [];

  //                                                                       // cpu
  private cpuFallback: ParticleSpringSystem;

  constructor(
    maxParticles: number,
    maxSprings: number = 100000,
    maxPins: number = 1000,
    config: Partial<SpringSystemConfig> = {}
  ) {
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.min(Math.floor(maxParticles), 1_000_000)
      : 10000;

    this.maxSprings = Number.isFinite(maxSprings) && maxSprings > 0
      ? Math.min(Math.floor(maxSprings), 1_000_000)
      : 100000;

    this.maxPins = Number.isFinite(maxPins) && maxPins > 0
      ? Math.min(Math.floor(maxPins), 10000)
      : 1000;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const globalStiffness = (typeof config.globalStiffness === "number" && Number.isFinite(config.globalStiffness) && config.globalStiffness > 0) ? config.globalStiffness : 100;
    const globalDamping = (typeof config.globalDamping === "number" && Number.isFinite(config.globalDamping) && config.globalDamping >= 0) ? config.globalDamping : 5;
    const solverIterations = (typeof config.solverIterations === "number" && Number.isFinite(config.solverIterations) && config.solverIterations >= 1) ? config.solverIterations : 4;
    const useVerlet = (typeof config.useVerlet === "boolean") ? config.useVerlet : true;
    const enableBreaking = (typeof config.enableBreaking === "boolean") ? config.enableBreaking : false;
    const gravity = (config.gravity !== null && config.gravity !== undefined && typeof config.gravity === "object") ? config.gravity : { x: 0, y: -980, z: 0 };
    this.config = {
      globalStiffness,
      globalDamping,
      solverIterations,
      useVerlet,
      enableBreaking,
      gravity,
    };

    // Create CPU fallback
    this.cpuFallback = new ParticleSpringSystem(maxParticles, config);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // initialization
  // ════════════════════════════════════════════════════════════════════════════

  async initialize(device?: GPUDevice): Promise<boolean> {
    if (!device) {
      if (!navigator.gpu) {
        console.warn("GPUSpringSystem: WebGPU not available, using CPU fallback");
        return false;
      }

      try {
        const adapter = await navigator.gpu.requestAdapter();
        if (!adapter) {
          console.warn("GPUSpringSystem: No GPU adapter, using CPU fallback");
          return false;
        }

        device = await adapter.requestDevice();
      } catch (e) {
        console.warn("GPUSpringSystem: Failed to get GPU device, using CPU fallback", e);
        return false;
      }
    }

    this.device = device;

    try {
      await this.createPipelines();
      this.createBuffers();
      this.createBindGroup();
      this.initialized = true;
      return true;
    } catch (e) {
      console.warn("GPUSpringSystem: Failed to create GPU resources, using CPU fallback", e);
      this.device = null;
      return false;
    }
  }

  private async createPipelines(): Promise<void> {
    if (!this.device) return;

    const shaderModule = this.device.createShaderModule({
      label: "Spring Compute Shader",
      code: springComputeShader,
    });

    this.bindGroupLayout = this.device.createBindGroupLayout({
      label: "Spring Bind Group Layout",
      entries: [
        { binding: 0, visibility: GPUShaderStage.COMPUTE, buffer: { type: "storage" } },
        { binding: 1, visibility: GPUShaderStage.COMPUTE, buffer: { type: "storage" } },
        { binding: 2, visibility: GPUShaderStage.COMPUTE, buffer: { type: "storage" } },
        { binding: 3, visibility: GPUShaderStage.COMPUTE, buffer: { type: "read-only-storage" } },
        { binding: 4, visibility: GPUShaderStage.COMPUTE, buffer: { type: "uniform" } },
      ],
    });

    const pipelineLayout = this.device.createPipelineLayout({
      label: "Spring Pipeline Layout",
      bindGroupLayouts: [this.bindGroupLayout],
    });

    this.pipelines = {
      verletIntegrate: this.device.createComputePipeline({
        label: "Verlet Integrate Pipeline",
        layout: pipelineLayout,
        compute: { module: shaderModule, entryPoint: "verletIntegrate" },
      }),
      solveConstraints: this.device.createComputePipeline({
        label: "Solve Constraints Pipeline",
        layout: pipelineLayout,
        compute: { module: shaderModule, entryPoint: "solveSpringConstraints" },
      }),
      applyPins: this.device.createComputePipeline({
        label: "Apply Pins Pipeline",
        layout: pipelineLayout,
        compute: { module: shaderModule, entryPoint: "applyPins" },
      }),
      eulerForces: this.device.createComputePipeline({
        label: "Euler Forces Pipeline",
        layout: pipelineLayout,
        compute: { module: shaderModule, entryPoint: "eulerSpringForces" },
      }),
    };
  }

  private createBuffers(): void {
    if (!this.device) return;

    const particleBufferSize = this.maxParticles * PARTICLE_STRIDE * 4;
    const prevPositionsSize = this.maxParticles * 3 * 4;
    const springsSize = this.maxSprings * 8 * 4; // 8 floats per spring
    const pinsSize = this.maxPins * 6 * 4; // 6 floats per pin
    const paramsSize = 64;

    this.buffers = {
      particles: this.device.createBuffer({
        label: "Spring Particles",
        size: particleBufferSize,
        usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST | GPUBufferUsage.COPY_SRC,
      }),
      prevPositions: this.device.createBuffer({
        label: "Previous Positions",
        size: prevPositionsSize,
        usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
      }),
      springs: this.device.createBuffer({
        label: "Springs",
        size: springsSize,
        usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
      }),
      pins: this.device.createBuffer({
        label: "Pins",
        size: pinsSize,
        usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
      }),
      params: this.device.createBuffer({
        label: "Spring Params",
        size: paramsSize,
        usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST,
      }),
      staging: this.device.createBuffer({
        label: "Spring Staging",
        size: particleBufferSize,
        usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST,
      }),
    };
  }

  private createBindGroup(): void {
    if (!this.device || !this.buffers || !this.bindGroupLayout) return;

    this.bindGroup = this.device.createBindGroup({
      label: "Spring Bind Group",
      layout: this.bindGroupLayout,
      entries: [
        { binding: 0, resource: { buffer: this.buffers.particles } },
        { binding: 1, resource: { buffer: this.buffers.prevPositions } },
        { binding: 2, resource: { buffer: this.buffers.springs } },
        { binding: 3, resource: { buffer: this.buffers.pins } },
        { binding: 4, resource: { buffer: this.buffers.params } },
      ],
    });
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // spring // management
  // ════════════════════════════════════════════════════════════════════════════

  addSpring(
    particleA: number,
    particleB: number,
    restLength: number,
    stiffness?: number,
    damping?: number,
    breakThreshold?: number
  ): void {
    if (this.springs.length >= this.maxSprings) {
      console.warn("GPUSpringSystem: Max springs reached");
      return;
    }

    if (particleA < 0 || particleA >= this.maxParticles ||
        particleB < 0 || particleB >= this.maxParticles ||
        particleA === particleB) {
      return;
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const springStiffness = (stiffness !== null && stiffness !== undefined && typeof stiffness === "number" && Number.isFinite(stiffness) && stiffness > 0) ? stiffness : this.config.globalStiffness;
    const springDamping = (damping !== null && damping !== undefined && typeof damping === "number" && Number.isFinite(damping) && damping >= 0) ? damping : this.config.globalDamping;
    const springBreakThreshold = (breakThreshold !== null && breakThreshold !== undefined && typeof breakThreshold === "number" && Number.isFinite(breakThreshold) && breakThreshold >= 0) ? breakThreshold : 0;
    this.springs.push({
      particleA,
      particleB,
      restLength: Math.max(0.001, restLength),
      stiffness: springStiffness,
      damping: springDamping,
      breakThreshold: springBreakThreshold,
      active: true,
    });

    // Also add to CPU fallback for consistency
    this.cpuFallback.addSpring(particleA, particleB, restLength, stiffness, damping, breakThreshold);
  }

  createClothGrid(
    startIndex: number,
    width: number,
    height: number,
    spacing: number,
    stiffness?: number
  ): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const k = (stiffness !== null && stiffness !== undefined && typeof stiffness === "number" && Number.isFinite(stiffness) && stiffness > 0) ? stiffness : this.config.globalStiffness;
    const diagLength = spacing * Math.SQRT2;

    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = startIndex + y * width + x;

        // Structural springs
        if (x < width - 1) this.addSpring(idx, idx + 1, spacing, k);
        if (y < height - 1) this.addSpring(idx, idx + width, spacing, k);

        // Shear springs
        if (x < width - 1 && y < height - 1) {
          this.addSpring(idx, idx + width + 1, diagLength, k * 0.5);
          this.addSpring(idx + 1, idx + width, diagLength, k * 0.5);
        }

        // Bend springs
        if (x < width - 2) this.addSpring(idx, idx + 2, spacing * 2, k * 0.25);
        if (y < height - 2) this.addSpring(idx, idx + width * 2, spacing * 2, k * 0.25);
      }
    }
  }

  createChain(particleIndices: number[], spacing: number, stiffness?: number): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const k = (stiffness !== null && stiffness !== undefined && typeof stiffness === "number" && Number.isFinite(stiffness) && stiffness > 0) ? stiffness : this.config.globalStiffness;
    for (let i = 0; i < particleIndices.length - 1; i++) {
      this.addSpring(particleIndices[i], particleIndices[i + 1], spacing, k);
    }
  }

  createSoftBody(
    startIndex: number,
    width: number,
    height: number,
    depth: number,
    spacing: number,
    stiffness?: number
  ): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const k = (stiffness !== null && stiffness !== undefined && typeof stiffness === "number" && Number.isFinite(stiffness) && stiffness > 0) ? stiffness : this.config.globalStiffness;

    const getIdx = (x: number, y: number, z: number) =>
      startIndex + z * width * height + y * width + x;

    for (let z = 0; z < depth; z++) {
      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          const idx = getIdx(x, y, z);

          if (x < width - 1) this.addSpring(idx, getIdx(x + 1, y, z), spacing, k);
          if (y < height - 1) this.addSpring(idx, getIdx(x, y + 1, z), spacing, k);
          if (z < depth - 1) this.addSpring(idx, getIdx(x, y, z + 1), spacing, k);

          if (x < width - 1 && y < height - 1) {
            this.addSpring(idx, getIdx(x + 1, y + 1, z), spacing * Math.SQRT2, k * 0.5);
          }
          if (y < height - 1 && z < depth - 1) {
            this.addSpring(idx, getIdx(x, y + 1, z + 1), spacing * Math.SQRT2, k * 0.5);
          }
          if (x < width - 1 && z < depth - 1) {
            this.addSpring(idx, getIdx(x + 1, y, z + 1), spacing * Math.SQRT2, k * 0.5);
          }
        }
      }
    }
  }

  clearSprings(): void {
    this.springs = [];
    this.cpuFallback.clearSprings();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                         // pin // management
  // ════════════════════════════════════════════════════════════════════════════

  pinParticle(particleIndex: number, position: { x: number; y: number; z: number }): void {
    if (this.pins.length >= this.maxPins) {
      console.warn("GPUSpringSystem: Max pins reached");
      return;
    }

    // Remove existing pin for this particle
    this.pins = this.pins.filter(p => p.particleIndex !== particleIndex);

    this.pins.push({
      particleIndex,
      active: true,
      position: { ...position },
    });

    this.cpuFallback.pinParticle(particleIndex);
  }

  unpinParticle(particleIndex: number): void {
    this.pins = this.pins.filter(p => p.particleIndex !== particleIndex);
    this.cpuFallback.unpinParticle(particleIndex);
  }

  updatePinPosition(particleIndex: number, position: { x: number; y: number; z: number }): void {
    const pin = this.pins.find(p => p.particleIndex === particleIndex);
    if (pin) {
      pin.position = { ...position };
    }
  }

  clearPins(): void {
    this.pins = [];
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                // simulation
  // ════════════════════════════════════════════════════════════════════════════

  private uploadSprings(): void {
    if (!this.device || !this.buffers) return;

    const springData = new Float32Array(this.maxSprings * 8);

    for (let i = 0; i < this.springs.length; i++) {
      const s = this.springs[i];
      const offset = i * 8;

      // Pack as: particleA, particleB, restLength, stiffness, damping, breakThreshold, active, padding
      const view = new DataView(springData.buffer);
      view.setUint32(offset * 4, s.particleA, true);
      view.setUint32((offset + 1) * 4, s.particleB, true);
      springData[offset + 2] = s.restLength;
      springData[offset + 3] = s.stiffness;
      springData[offset + 4] = s.damping;
      springData[offset + 5] = s.breakThreshold;
      view.setUint32((offset + 6) * 4, s.active ? 1 : 0, true);
      springData[offset + 7] = 0; // padding
    }

    this.device.queue.writeBuffer(this.buffers.springs, 0, springData);
  }

  private uploadPins(): void {
    if (!this.device || !this.buffers) return;

    const pinData = new Float32Array(this.maxPins * 6);

    for (let i = 0; i < this.pins.length; i++) {
      const p = this.pins[i];
      const offset = i * 6;

      const view = new DataView(pinData.buffer);
      view.setUint32(offset * 4, p.particleIndex, true);
      view.setUint32((offset + 1) * 4, p.active ? 1 : 0, true);
      pinData[offset + 2] = p.position.x;
      pinData[offset + 3] = p.position.y;
      pinData[offset + 4] = p.position.z;
      pinData[offset + 5] = 0; // padding
    }

    this.device.queue.writeBuffer(this.buffers.pins, 0, pinData);
  }

  private updateParams(dt: number): void {
    if (!this.device || !this.buffers) return;

    const params = new Float32Array(16);
    params[0] = this.config.gravity.x;
    params[1] = this.config.gravity.y;
    params[2] = this.config.gravity.z;
    params[3] = dt;

    const view = new DataView(params.buffer);
    view.setUint32(4 * 4, this.maxParticles, true);
    view.setUint32(5 * 4, this.springs.length, true);
    view.setUint32(6 * 4, this.pins.length, true);
    view.setUint32(7 * 4, this.config.solverIterations, true);

    params[8] = this.config.globalStiffness;
    params[9] = this.config.globalDamping;

    this.device.queue.writeBuffer(this.buffers.params, 0, params);
  }

  private initializePrevPositions(particleBuffer: Float32Array): void {
    if (!this.device || !this.buffers) return;

    const prevPositions = new Float32Array(this.maxParticles * 3);
    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      prevPositions[i * 3 + 0] = particleBuffer[offset + 0];
      prevPositions[i * 3 + 1] = particleBuffer[offset + 1];
      prevPositions[i * 3 + 2] = particleBuffer[offset + 2];
    }

    this.device.queue.writeBuffer(this.buffers.prevPositions, 0, prevPositions);
  }

  private prevPositionsInitialized = false;

  async update(particleBuffer: Float32Array, dt: number): Promise<void> {
    // Use CPU fallback if GPU not available
    if (!this.initialized || !this.device || !this.buffers || !this.pipelines || !this.bindGroup) {
      this.cpuFallback.update(particleBuffer, dt);
      return;
    }

    const safeDt = Number.isFinite(dt) && dt > 0 ? Math.min(dt, 0.1) : 0.016;

    // Initialize previous positions on first update
    if (!this.prevPositionsInitialized) {
      this.initializePrevPositions(particleBuffer);
      this.prevPositionsInitialized = true;
    }

    // Upload data
    this.device.queue.writeBuffer(
      this.buffers.particles,
      0,
      particleBuffer.buffer,
      particleBuffer.byteOffset,
      particleBuffer.byteLength
    );
    this.uploadSprings();
    this.uploadPins();
    this.updateParams(safeDt);

    const encoder = this.device.createCommandEncoder();

    const particleWorkgroups = Math.ceil(this.maxParticles / 256);
    const springWorkgroups = Math.ceil(this.springs.length / 256);
    const pinWorkgroups = Math.ceil(this.pins.length / 256);

    if (this.config.useVerlet) {
      // Verlet integration
      const verletPass = encoder.beginComputePass();
      verletPass.setPipeline(this.pipelines.verletIntegrate);
      verletPass.setBindGroup(0, this.bindGroup);
      verletPass.dispatchWorkgroups(particleWorkgroups);
      verletPass.end();

      // Constraint solving (multiple iterations)
      for (let iter = 0; iter < this.config.solverIterations; iter++) {
        const constraintPass = encoder.beginComputePass();
        constraintPass.setPipeline(this.pipelines.solveConstraints);
        constraintPass.setBindGroup(0, this.bindGroup);
        constraintPass.dispatchWorkgroups(springWorkgroups);
        constraintPass.end();
      }
    } else {
      // Euler integration with spring forces
      const eulerPass = encoder.beginComputePass();
      eulerPass.setPipeline(this.pipelines.eulerForces);
      eulerPass.setBindGroup(0, this.bindGroup);
      eulerPass.dispatchWorkgroups(springWorkgroups);
      eulerPass.end();
    }

    // Apply pins
    if (this.pins.length > 0) {
      const pinPass = encoder.beginComputePass();
      pinPass.setPipeline(this.pipelines.applyPins);
      pinPass.setBindGroup(0, this.bindGroup);
      pinPass.dispatchWorkgroups(pinWorkgroups);
      pinPass.end();
    }

    this.device.queue.submit([encoder.finish()]);

    // Read back results
    await this.readBackParticles(particleBuffer);
  }

  private async readBackParticles(particleBuffer: Float32Array): Promise<void> {
    if (!this.device || !this.buffers) return;

    const encoder = this.device.createCommandEncoder();
    encoder.copyBufferToBuffer(
      this.buffers.particles,
      0,
      this.buffers.staging,
      0,
      particleBuffer.byteLength
    );
    this.device.queue.submit([encoder.finish()]);

    await this.buffers.staging.mapAsync(GPUMapMode.READ);
    const data = new Float32Array(this.buffers.staging.getMappedRange());
    particleBuffer.set(data);
    this.buffers.staging.unmap();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // accessors
  // ════════════════════════════════════════════════════════════════════════════

  getSpringCount(): number {
    return this.springs.filter(s => s.active).length;
  }

  getPinCount(): number {
    return this.pins.filter(p => p.active).length;
  }

  updateConfig(config: Partial<SpringSystemConfig>): void {
    Object.assign(this.config, config);
    this.cpuFallback.updateConfig(config);
  }

  getConfig(): SpringSystemConfig {
    return { ...this.config };
  }

  isGPUAvailable(): boolean {
    return this.initialized && this.device !== null;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // cleanup
  // ════════════════════════════════════════════════════════════════════════════

  dispose(): void {
    if (this.buffers) {
      this.buffers.particles.destroy();
      this.buffers.prevPositions.destroy();
      this.buffers.springs.destroy();
      this.buffers.pins.destroy();
      this.buffers.params.destroy();
      this.buffers.staging.destroy();
    }
    this.buffers = null;
    this.pipelines = null;
    this.bindGroup = null;
    this.device = null;
    this.initialized = false;
  }
}
