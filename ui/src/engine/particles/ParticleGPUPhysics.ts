/**
 * Particle GPU Physics
 *
 * Handles GPU-accelerated particle physics using:
 * - WebGPU compute shaders (preferred, 10-100x faster)
 * - WebGL2 Transform Feedback (fallback)
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import * as THREE from "three";
import {
  getFalloffTypeIndex,
  getForceFieldTypeIndex,
} from "./ParticleForceCalculator";
import {
  TRANSFORM_FEEDBACK_FRAGMENT_SHADER,
  TRANSFORM_FEEDBACK_VERTEX_SHADER,
} from "./particleShaders";
import { type ForceFieldConfig, PARTICLE_STRIDE } from "./types";
import {
  isWebGPUAvailable,
  WebGPUParticleCompute,
  type WebGPUParticleConfig,
} from "./webgpuParticleCompute";

// ============================================================================
// CONSTANTS
// ============================================================================

export const MAX_FORCE_FIELDS = 16;

const TF_VARYINGS = [
  "tf_position",
  "tf_velocity",
  "tf_life",
  "tf_physical",
  "tf_rotation",
  "tf_color",
];

// ============================================================================
// TYPES
// ============================================================================

export interface GPUPhysicsConfig {
  maxParticles: number;
  bounds?: {
    min: [number, number, number];
    max: [number, number, number];
  };
  damping?: number;
  noiseScale?: number;
  noiseSpeed?: number;
}

export interface GPUPhysicsState {
  simulationTime: number;
  frameCount: number;
}

export type DeathCallback = (index: number) => void;

// ============================================================================
// PARTICLE GPU PHYSICS CLASS
// ============================================================================

export class ParticleGPUPhysics {
  private readonly config: GPUPhysicsConfig;
  private gl: WebGL2RenderingContext | null = null;
  private renderer: THREE.WebGLRenderer | null = null;

  // Transform Feedback resources
  private transformFeedbackProgram: WebGLProgram | null = null;
  private particleVboA: WebGLBuffer | null = null;
  private particleVboB: WebGLBuffer | null = null;
  private vaoA: WebGLVertexArrayObject | null = null;
  private vaoB: WebGLVertexArrayObject | null = null;
  private transformFeedbackA: WebGLTransformFeedback | null = null;
  private transformFeedbackB: WebGLTransformFeedback | null = null;

  // Force field texture
  private forceFieldBuffer: Float32Array | null = null;
  private forceFieldTexture: THREE.DataTexture | null = null;

  // State flags
  private gpuPhysicsInitialized = false;
  private useGPUPhysics = false;

  // WebGPU resources
  private webgpuCompute: WebGPUParticleCompute | null = null;
  private useWebGPU = false;
  private webgpuInitialized = false;
  private webgpuReadbackPending = false;

  // Buffer swap state
  private currentBuffer: "A" | "B" = "A";

  constructor(config: GPUPhysicsConfig) {
    // Validate maxParticles to prevent WebGL errors
    const safeMaxParticles = Number.isFinite(config.maxParticles) && config.maxParticles > 0
      ? Math.min(Math.floor(config.maxParticles), 10_000_000)  // Cap at 10M
      : 10000;  // Sensible default
    
    this.config = {
      maxParticles: safeMaxParticles,
      bounds: config.bounds ?? {
        min: [-10000, -10000, -10000],
        max: [10000, 10000, 10000],
      },
      damping: config.damping ?? 0.99,
      noiseScale: config.noiseScale ?? 0.005,
      noiseSpeed: config.noiseSpeed ?? 0.5,
    };
  }

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Initialize GPU physics with renderer
   */
  async initialize(
    renderer: THREE.WebGLRenderer,
    particleBufferA: Float32Array,
    particleBufferB: Float32Array,
  ): Promise<void> {
    this.renderer = renderer;
    this.gl = renderer.getContext() as WebGL2RenderingContext;

    // Try WebGPU first, then fall back to Transform Feedback
    const webgpuReady = await this.initializeWebGPU();
    if (!webgpuReady) {
      this.initializeTransformFeedback(particleBufferA, particleBufferB);
    }
  }

  /**
   * Initialize WebGPU compute shaders
   */
  private async initializeWebGPU(): Promise<boolean> {
    try {
      const available = await isWebGPUAvailable();
      if (!available) {
        console.log(
          "WebGPU not available, will use Transform Feedback fallback",
        );
        return false;
      }

      const webgpuConfig: WebGPUParticleConfig = {
        maxParticles: this.config.maxParticles,
        bounds: this.config.bounds!,
        damping: this.config.damping!,
        noiseScale: this.config.noiseScale!,
        noiseSpeed: this.config.noiseSpeed!,
      };

      this.webgpuCompute = new WebGPUParticleCompute(webgpuConfig);
      await this.webgpuCompute.initialize();

      this.useWebGPU = true;
      this.webgpuInitialized = true;
      this.useGPUPhysics = false; // Disable Transform Feedback

      console.log("WebGPU compute shaders initialized for particle physics");
      return true;
    } catch (error) {
      console.warn("WebGPU initialization failed:", error);
      this.useWebGPU = false;
      return false;
    }
  }

  /**
   * Initialize WebGL2 Transform Feedback
   */
  private initializeTransformFeedback(
    particleBufferA: Float32Array,
    particleBufferB: Float32Array,
  ): void {
    if (!this.gl) return;

    const gl = this.gl;

    // Check for required extensions
    const tfExtension = gl.getExtension("EXT_color_buffer_float");
    if (!tfExtension) {
      console.warn(
        "EXT_color_buffer_float not available, using CPU physics fallback",
      );
      this.useGPUPhysics = false;
      return;
    }

    try {
      // Create transform feedback program
      this.transformFeedbackProgram = this.createTransformFeedbackProgram(gl);

      if (!this.transformFeedbackProgram) {
        console.warn(
          "Failed to create transform feedback program, using CPU physics",
        );
        this.useGPUPhysics = false;
        return;
      }

      // Create double-buffered VAOs and VBOs
      this.particleVboA = gl.createBuffer();
      this.particleVboB = gl.createBuffer();

      if (!this.particleVboA || !this.particleVboB) {
        throw new Error("Failed to create particle VBOs");
      }

      // Initialize VBO A with particle data
      gl.bindBuffer(gl.ARRAY_BUFFER, this.particleVboA);
      gl.bufferData(gl.ARRAY_BUFFER, particleBufferA, gl.DYNAMIC_COPY);

      // Initialize VBO B
      gl.bindBuffer(gl.ARRAY_BUFFER, this.particleVboB);
      gl.bufferData(gl.ARRAY_BUFFER, particleBufferB, gl.DYNAMIC_COPY);

      // Create VAOs
      this.vaoA = gl.createVertexArray();
      this.vaoB = gl.createVertexArray();

      if (!this.vaoA || !this.vaoB) {
        throw new Error("Failed to create VAOs");
      }

      // Set up VAOs
      this.setupParticleVAO(gl, this.vaoA, this.particleVboA);
      this.setupParticleVAO(gl, this.vaoB, this.particleVboB);

      // Create transform feedback objects
      this.transformFeedbackA = gl.createTransformFeedback();
      this.transformFeedbackB = gl.createTransformFeedback();

      if (!this.transformFeedbackA || !this.transformFeedbackB) {
        throw new Error("Failed to create transform feedback objects");
      }

      // Bind VBO B as output for transform feedback A
      gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, this.transformFeedbackA);
      gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 0, this.particleVboB);

      // Bind VBO A as output for transform feedback B
      gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, this.transformFeedbackB);
      gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 0, this.particleVboA);

      gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, null);

      // Create force field texture
      this.forceFieldBuffer = new Float32Array(MAX_FORCE_FIELDS * 16);
      this.forceFieldTexture = new THREE.DataTexture(
        this.forceFieldBuffer as unknown as BufferSource,
        MAX_FORCE_FIELDS,
        4,
        THREE.RGBAFormat,
        THREE.FloatType,
      );

      this.useGPUPhysics = true;
      this.gpuPhysicsInitialized = true;

      console.log("GPU physics initialized with Transform Feedback");
    } catch (error) {
      console.warn("GPU physics initialization failed:", error);
      this.useGPUPhysics = false;
      this.cleanup();
    }
  }

  /**
   * Set up vertex attribute pointers for particle VAO
   */
  private setupParticleVAO(
    gl: WebGL2RenderingContext,
    vao: WebGLVertexArrayObject,
    vbo: WebGLBuffer,
  ): void {
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
   * Create the transform feedback shader program
   */
  private createTransformFeedbackProgram(
    gl: WebGL2RenderingContext,
  ): WebGLProgram | null {
    const vsSource = TRANSFORM_FEEDBACK_VERTEX_SHADER;
    const fsSource = TRANSFORM_FEEDBACK_FRAGMENT_SHADER;

    const vs = gl.createShader(gl.VERTEX_SHADER);
    const fs = gl.createShader(gl.FRAGMENT_SHADER);

    if (!vs || !fs) return null;

    gl.shaderSource(vs, vsSource);
    gl.compileShader(vs);

    if (!gl.getShaderParameter(vs, gl.COMPILE_STATUS)) {
      console.error(
        "Transform feedback vertex shader error:",
        gl.getShaderInfoLog(vs),
      );
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      return null;
    }

    gl.shaderSource(fs, fsSource);
    gl.compileShader(fs);

    if (!gl.getShaderParameter(fs, gl.COMPILE_STATUS)) {
      console.error(
        "Transform feedback fragment shader error:",
        gl.getShaderInfoLog(fs),
      );
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
      console.error(
        "Transform feedback program link error:",
        gl.getProgramInfoLog(program),
      );
      gl.deleteProgram(program);
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      return null;
    }

    gl.deleteShader(vs);
    gl.deleteShader(fs);

    return program;
  }

  // ============================================================================
  // UPDATE
  // ============================================================================

  /**
   * Update particle physics on GPU
   * @returns The current buffer indicator after update
   */
  update(
    dt: number,
    state: GPUPhysicsState,
    particleBufferA: Float32Array,
    particleBufferB: Float32Array,
    forceFields: Map<string, ForceFieldConfig>,
    freeIndices: number[],
    onDeath: DeathCallback,
  ): { currentBuffer: "A" | "B"; particleCount: number } {
    // Validate dt to prevent NaN/Infinity propagation to GPU
    const safeDt = Number.isFinite(dt) && dt >= 0 ? Math.min(dt, 1.0) : 0.016;  // Cap at 1s, default 60fps
    
    if (this.useWebGPU && this.webgpuCompute) {
      return this.updateWebGPU(
        safeDt,
        state,
        particleBufferA,
        particleBufferB,
        forceFields,
        freeIndices,
        onDeath,
      );
    } else if (this.useGPUPhysics && this.transformFeedbackProgram) {
      return this.updateTransformFeedback(
        safeDt,
        state,
        forceFields,
        freeIndices,
        onDeath,
      );
    }

    // Return current state if no GPU physics
    return { currentBuffer: this.currentBuffer, particleCount: -1 };
  }

  /**
   * Update using WebGPU compute shaders
   */
  private updateWebGPU(
    dt: number,
    state: GPUPhysicsState,
    particleBufferA: Float32Array,
    particleBufferB: Float32Array,
    forceFields: Map<string, ForceFieldConfig>,
    freeIndices: number[],
    onDeath: DeathCallback,
  ): { currentBuffer: "A" | "B"; particleCount: number } {
    if (!this.webgpuCompute) {
      return { currentBuffer: this.currentBuffer, particleCount: -1 };
    }

    const buffer =
      this.currentBuffer === "A" ? particleBufferA : particleBufferB;

    // Prepare force field data for WebGPU
    const forceFieldData: Array<{
      type: number;
      position: [number, number, number];
      strength: number;
      radius: number;
      falloff: number;
      direction: [number, number, number];
    }> = [];

    // Helper to sanitize values for WebGPU
    const safe = (val: number | undefined, fallback: number): number => {
      if (val === undefined) return fallback;
      return Number.isFinite(val) ? val : fallback;
    };

    for (const field of forceFields.values()) {
      if (!field.enabled) continue;
      forceFieldData.push({
        type: getForceFieldTypeIndex(field.type),
        position: [
          safe(field.position.x, 0),
          safe(field.position.y, 0),
          safe(field.position.z, 0),
        ],
        strength: safe(field.strength, 0),
        radius: safe(field.falloffEnd, 100),
        falloff:
          field.falloffType === "linear"
            ? 1
            : field.falloffType === "quadratic"
              ? 2
              : 0,
        direction: [
          safe(
            field.direction?.x ?? field.vortexAxis?.x ?? field.windDirection?.x,
            0,
          ),
          safe(
            field.direction?.y ?? field.vortexAxis?.y ?? field.windDirection?.y,
            0,
          ),
          safe(
            field.direction?.z ?? field.vortexAxis?.z ?? field.windDirection?.z,
            0,
          ),
        ],
      });
    }

    // Upload particle data to GPU
    this.webgpuCompute.uploadParticles(buffer);
    this.webgpuCompute.uploadForceFields(forceFieldData);

    // Update simulation parameters (validate simulationTime)
    const safeSimTime = Number.isFinite(state.simulationTime) ? state.simulationTime : 0;
    this.webgpuCompute.updateParams(
      dt,
      safeSimTime,
      this.config.maxParticles,
      forceFieldData.length,
    );

    // Run physics step on GPU
    this.webgpuCompute.step(this.config.maxParticles);

    // Periodically read back particle data for CPU-side operations
    let particleCount = -1;
    if (state.frameCount % 10 === 0 && !this.webgpuReadbackPending) {
      this.webgpuReadbackPending = true;
      this.webgpuCompute
        .readParticles(this.config.maxParticles)
        .then((data) => {
          const targetBuffer =
            this.currentBuffer === "A" ? particleBufferA : particleBufferB;
          targetBuffer.set(data);

          // Process deaths
          let activeCount = 0;
          for (let i = 0; i < this.config.maxParticles; i++) {
            const offset = i * PARTICLE_STRIDE;
            const age = targetBuffer[offset + 6];
            const lifetime = targetBuffer[offset + 7];

            if (lifetime > 0 && age < lifetime) {
              activeCount++;
            } else if (lifetime > 0 && age >= lifetime) {
              if (!freeIndices.includes(i)) {
                freeIndices.push(i);
                onDeath(i);
              }
            }
          }

          particleCount = activeCount;
          this.webgpuReadbackPending = false;
        });
    }

    return { currentBuffer: this.currentBuffer, particleCount };
  }

  /**
   * Update using Transform Feedback
   */
  private updateTransformFeedback(
    dt: number,
    state: GPUPhysicsState,
    forceFields: Map<string, ForceFieldConfig>,
    freeIndices: number[],
    onDeath: DeathCallback,
  ): { currentBuffer: "A" | "B"; particleCount: number } {
    if (!this.gl || !this.transformFeedbackProgram) {
      return { currentBuffer: this.currentBuffer, particleCount: -1 };
    }

    const gl = this.gl;

    // Update force field texture data
    this.updateForceFieldTexture(forceFields);

    // Use transform feedback program
    gl.useProgram(this.transformFeedbackProgram);

    // Set uniforms
    const dtLoc = gl.getUniformLocation(
      this.transformFeedbackProgram,
      "u_deltaTime",
    );
    const timeLoc = gl.getUniformLocation(
      this.transformFeedbackProgram,
      "u_time",
    );
    const ffCountLoc = gl.getUniformLocation(
      this.transformFeedbackProgram,
      "u_forceFieldCount",
    );
    const ffTexLoc = gl.getUniformLocation(
      this.transformFeedbackProgram,
      "u_forceFields",
    );

    gl.uniform1f(dtLoc, dt);
    // Validate simulationTime
    const safeSimTime = Number.isFinite(state.simulationTime) ? state.simulationTime : 0;
    gl.uniform1f(timeLoc, safeSimTime);
    gl.uniform1i(ffCountLoc, Math.min(forceFields.size, MAX_FORCE_FIELDS));

    // Bind force field texture
    if (this.forceFieldTexture && this.renderer) {
      gl.activeTexture(gl.TEXTURE0);
      const textureProps = this.renderer.properties.get(
        this.forceFieldTexture,
      ) as { __webglTexture?: WebGLTexture } | undefined;
      const tex = textureProps?.__webglTexture;
      if (tex) {
        gl.bindTexture(gl.TEXTURE_2D, tex);
        gl.uniform1i(ffTexLoc, 0);
      }
    }

    // Determine which buffers to use (ping-pong)
    const readVAO = this.currentBuffer === "A" ? this.vaoA : this.vaoB;
    const writeTF =
      this.currentBuffer === "A"
        ? this.transformFeedbackA
        : this.transformFeedbackB;
    const writeVBO =
      this.currentBuffer === "A" ? this.particleVboB : this.particleVboA;

    // Bind read VAO
    gl.bindVertexArray(readVAO);

    // Disable rasterization
    gl.enable(gl.RASTERIZER_DISCARD);

    // Begin transform feedback
    gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, writeTF);
    gl.beginTransformFeedback(gl.POINTS);

    // Draw all particles
    gl.drawArrays(gl.POINTS, 0, this.config.maxParticles);

    // End transform feedback
    gl.endTransformFeedback();
    gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, null);

    // Re-enable rasterization
    gl.disable(gl.RASTERIZER_DISCARD);

    // Unbind VAO
    gl.bindVertexArray(null);

    // Swap buffers for next frame
    this.currentBuffer = this.currentBuffer === "A" ? "B" : "A";

    // Read back particle data periodically
    let particleCount = -1;
    if (state.frameCount % 10 === 0) {
      particleCount = this.readBackParticleData(
        writeVBO,
        this.currentBuffer === "A" ? this.particleVboA : this.particleVboB,
        freeIndices,
        onDeath,
      );
    }

    return { currentBuffer: this.currentBuffer, particleCount };
  }

  /**
   * Update force field texture data
   */
  private updateForceFieldTexture(
    forceFields: Map<string, ForceFieldConfig>,
  ): void {
    if (!this.forceFieldBuffer || !this.forceFieldTexture) return;

    let fieldIndex = 0;
    for (const field of forceFields.values()) {
      if (fieldIndex >= MAX_FORCE_FIELDS) break;
      if (!field.enabled) continue;

      const baseOffset = fieldIndex * 16;

      // Helper to sanitize position values
      const safePos = (val: number): number => Number.isFinite(val) ? val : 0;
      const safePositive = (val: number, fallback: number): number => 
        Number.isFinite(val) && val >= 0 ? val : fallback;

      // Row 0: position.xyz, type
      this.forceFieldBuffer[baseOffset + 0] = safePos(field.position.x);
      this.forceFieldBuffer[baseOffset + 1] = safePos(field.position.y);
      this.forceFieldBuffer[baseOffset + 2] = safePos(field.position.z);
      this.forceFieldBuffer[baseOffset + 3] = getForceFieldTypeIndex(
        field.type,
      );

      // Row 1: strength, falloffStart, falloffEnd, falloffType
      this.forceFieldBuffer[baseOffset + 4] = Number.isFinite(field.strength) ? field.strength : 0;
      this.forceFieldBuffer[baseOffset + 5] = safePositive(field.falloffStart, 0);
      this.forceFieldBuffer[baseOffset + 6] = safePositive(field.falloffEnd, 100);
      this.forceFieldBuffer[baseOffset + 7] = getFalloffTypeIndex(
        field.falloffType,
      );

      // Helper to sanitize float values for GPU
      const safeFloat = (val: number | undefined, fallback: number): number => {
        if (val === undefined) return fallback;
        return Number.isFinite(val) ? val : fallback;
      };

      // Row 2: direction/axis.xyz, extra param
      if (field.type === "lorenz") {
        this.forceFieldBuffer[baseOffset + 8] = safeFloat(field.lorenzSigma, 10.0);
        this.forceFieldBuffer[baseOffset + 9] = safeFloat(field.lorenzRho, 28.0);
        this.forceFieldBuffer[baseOffset + 10] = safeFloat(field.lorenzBeta, 2.666667);
        this.forceFieldBuffer[baseOffset + 11] = 0;
      } else if (field.type === "orbit" || field.type === "path") {
        this.forceFieldBuffer[baseOffset + 8] = safeFloat(field.vortexAxis?.x, 0);
        this.forceFieldBuffer[baseOffset + 9] = safeFloat(field.vortexAxis?.y, 1);
        this.forceFieldBuffer[baseOffset + 10] = safeFloat(field.vortexAxis?.z, 0);
        this.forceFieldBuffer[baseOffset + 11] = safeFloat(field.pathRadius, 100);
      } else {
        this.forceFieldBuffer[baseOffset + 8] = safeFloat(
          field.direction?.x ?? field.vortexAxis?.x ?? field.windDirection?.x,
          0,
        );
        this.forceFieldBuffer[baseOffset + 9] = safeFloat(
          field.direction?.y ?? field.vortexAxis?.y ?? field.windDirection?.y,
          0,
        );
        this.forceFieldBuffer[baseOffset + 10] = safeFloat(
          field.direction?.z ?? field.vortexAxis?.z ?? field.windDirection?.z,
          0,
        );
        this.forceFieldBuffer[baseOffset + 11] = safeFloat(field.inwardForce, 0);
      }

      // Row 3: extra params
      if (field.type === "magnetic") {
        this.forceFieldBuffer[baseOffset + 12] = 1.0;
        this.forceFieldBuffer[baseOffset + 13] = 0;
        this.forceFieldBuffer[baseOffset + 14] = 0;
        this.forceFieldBuffer[baseOffset + 15] = 0;
      } else {
        this.forceFieldBuffer[baseOffset + 12] = safeFloat(
          field.noiseScale ?? field.linearDrag ?? field.gustStrength,
          0,
        );
        this.forceFieldBuffer[baseOffset + 13] = safeFloat(
          field.noiseSpeed ?? field.quadraticDrag ?? field.gustFrequency,
          0,
        );
        this.forceFieldBuffer[baseOffset + 14] = 0;
        this.forceFieldBuffer[baseOffset + 15] = 0;
      }

      fieldIndex++;
    }

    this.forceFieldTexture.needsUpdate = true;
  }

  /**
   * Read back particle data from GPU
   */
  private readBackParticleData(
    vbo: WebGLBuffer | null,
    _targetBuffer: Float32Array | WebGLBuffer | null,
    _freeIndices: number[],
    _onDeath: DeathCallback,
  ): number {
    if (!this.gl || !vbo) return -1;

    const gl = this.gl;

    // Get the actual target buffer (not the VBO, but the Float32Array we want to read into)
    // This is a bit of a hack - we need to get the CPU buffer from outside
    gl.bindBuffer(gl.ARRAY_BUFFER, vbo);

    // We can't directly read into the Float32Array here without knowing which buffer
    // Instead, return that a read is needed
    gl.bindBuffer(gl.ARRAY_BUFFER, null);

    return -1; // Indicates caller should handle readback
  }

  /**
   * Read particle data from GPU into CPU buffer
   */
  readParticleData(targetBuffer: Float32Array): void {
    if (!this.gl) return;

    const gl = this.gl;
    const vbo =
      this.currentBuffer === "A" ? this.particleVboA : this.particleVboB;

    if (vbo) {
      gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
      gl.getBufferSubData(gl.ARRAY_BUFFER, 0, targetBuffer);
      gl.bindBuffer(gl.ARRAY_BUFFER, null);
    }
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  isEnabled(): boolean {
    return this.useGPUPhysics || this.useWebGPU;
  }

  isGPUPhysicsInitialized(): boolean {
    return this.gpuPhysicsInitialized;
  }

  isWebGPUEnabled(): boolean {
    return this.useWebGPU;
  }

  getCurrentBuffer(): "A" | "B" {
    return this.currentBuffer;
  }

  setCurrentBuffer(buffer: "A" | "B"): void {
    this.currentBuffer = buffer;
  }

  setEnabled(enabled: boolean): void {
    if (enabled && !this.gpuPhysicsInitialized && !this.webgpuInitialized) {
      console.warn("Cannot enable GPU physics - not initialized");
      return;
    }
    this.useGPUPhysics = enabled && this.gpuPhysicsInitialized;
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  cleanup(): void {
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

    // Cleanup WebGPU
    if (this.webgpuCompute) {
      this.webgpuCompute.dispose();
      this.webgpuCompute = null;
    }

    this.useWebGPU = false;
    this.gpuPhysicsInitialized = false;
    this.useGPUPhysics = false;
  }

  dispose(): void {
    this.cleanup();
    this.gl = null;
    this.renderer = null;
  }
}
