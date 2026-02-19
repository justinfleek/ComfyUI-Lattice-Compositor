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
import { assertDefined } from "@/utils/typeGuards";
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
    
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Deterministic: Ensure bounds has correct tuple types [number, number, number]
    const boundsRaw = (config.bounds !== null && config.bounds !== undefined && typeof config.bounds === "object") ? config.bounds : null;
    const bounds = boundsRaw !== null
      ? {
          min: boundsRaw.min as [number, number, number],
          max: boundsRaw.max as [number, number, number],
        }
      : {
          min: [-10000, -10000, -10000] as [number, number, number],
          max: [10000, 10000, 10000] as [number, number, number],
        };
    const damping = (typeof config.damping === "number" && Number.isFinite(config.damping) && config.damping >= 0 && config.damping <= 1) ? config.damping : 0.99;
    const noiseScale = (typeof config.noiseScale === "number" && Number.isFinite(config.noiseScale) && config.noiseScale >= 0) ? config.noiseScale : 0.005;
    const noiseSpeed = (typeof config.noiseSpeed === "number" && Number.isFinite(config.noiseSpeed) && config.noiseSpeed >= 0) ? config.noiseSpeed : 0.5;
    this.config = {
      maxParticles: safeMaxParticles,
      bounds,
      damping,
      noiseScale,
      noiseSpeed,
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

      // Type proof: bounds, damping, noiseScale, noiseSpeed are guaranteed by constructor defaults
      assertDefined(this.config.bounds, "bounds must exist after constructor initialization");
      assertDefined(this.config.damping, "damping must exist after constructor initialization");
      assertDefined(this.config.noiseScale, "noiseScale must exist after constructor initialization");
      assertDefined(this.config.noiseSpeed, "noiseSpeed must exist after constructor initialization");
      const webgpuConfig: WebGPUParticleConfig = {
        maxParticles: this.config.maxParticles,
        bounds: this.config.bounds,
        damping: this.config.damping,
        noiseScale: this.config.noiseScale,
        noiseSpeed: this.config.noiseSpeed,
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
      // System F/Omega pattern: Wrap in try/catch for expected "WebGL failure" case
      // When WebGL operations fail, fallback to CPU physics is a valid state
      this.transformFeedbackProgram = this.createTransformFeedbackProgram(gl);

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
        this.forceFieldBuffer.buffer as ArrayBuffer,
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
   * 
   * System F/Omega proof: Explicit validation of WebGL shader creation and compilation
   * Type proof: gl ∈ WebGL2RenderingContext → WebGLProgram (non-nullable)
   * Mathematical proof: All WebGL operations must succeed to create valid program
   * Pattern proof: WebGL failures are explicit error conditions, not lazy null returns
   */
  private createTransformFeedbackProgram(
    gl: WebGL2RenderingContext,
  ): WebGLProgram {
    const vsSource = TRANSFORM_FEEDBACK_VERTEX_SHADER;
    const fsSource = TRANSFORM_FEEDBACK_FRAGMENT_SHADER;

    const vs = gl.createShader(gl.VERTEX_SHADER);
    const fs = gl.createShader(gl.FRAGMENT_SHADER);

    // System F/Omega proof: Explicit validation of shader creation
    // Type proof: gl.createShader() ∈ WebGLShader | null
    // Mathematical proof: Shader creation must succeed for both vertex and fragment shaders
    if (!vs || !fs) {
      const vsStatus = vs ? "created" : "failed";
      const fsStatus = fs ? "created" : "failed";
      if (vs) gl.deleteShader(vs);
      if (fs) gl.deleteShader(fs);
      throw new Error(
        `[ParticleGPUPhysics] Cannot create transform feedback program: Shader creation failed. ` +
        `Vertex shader: ${vsStatus}, fragment shader: ${fsStatus}. ` +
        `WebGL context may be lost or invalid. Wrap in try/catch to fallback to CPU physics.`
      );
    }

    gl.shaderSource(vs, vsSource);
    gl.compileShader(vs);

    // System F/Omega proof: Explicit validation of vertex shader compilation
    // Type proof: gl.getShaderParameter(vs, gl.COMPILE_STATUS) ∈ boolean
    // Mathematical proof: Vertex shader must compile successfully
    if (!gl.getShaderParameter(vs, gl.COMPILE_STATUS)) {
      const errorLog = gl.getShaderInfoLog(vs) || "No error log available";
      console.error("Transform feedback vertex shader error:", errorLog);
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      throw new Error(
        `[ParticleGPUPhysics] Cannot create transform feedback program: Vertex shader compilation failed. ` +
        `Error log: ${errorLog}. ` +
        `Shader source length: ${vsSource.length} characters. ` +
        `Wrap in try/catch to fallback to CPU physics.`
      );
    }

    gl.shaderSource(fs, fsSource);
    gl.compileShader(fs);

    // System F/Omega proof: Explicit validation of fragment shader compilation
    // Type proof: gl.getShaderParameter(fs, gl.COMPILE_STATUS) ∈ boolean
    // Mathematical proof: Fragment shader must compile successfully
    if (!gl.getShaderParameter(fs, gl.COMPILE_STATUS)) {
      const errorLog = gl.getShaderInfoLog(fs) || "No error log available";
      console.error("Transform feedback fragment shader error:", errorLog);
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      throw new Error(
        `[ParticleGPUPhysics] Cannot create transform feedback program: Fragment shader compilation failed. ` +
        `Error log: ${errorLog}. ` +
        `Shader source length: ${fsSource.length} characters. ` +
        `Wrap in try/catch to fallback to CPU physics.`
      );
    }

    const program = gl.createProgram();
    
    // System F/Omega proof: Explicit validation of program creation
    // Type proof: gl.createProgram() ∈ WebGLProgram | null
    // Mathematical proof: Program creation must succeed
    if (!program) {
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      throw new Error(
        `[ParticleGPUPhysics] Cannot create transform feedback program: Program creation failed. ` +
        `WebGL context may be lost or invalid. ` +
        `Wrap in try/catch to fallback to CPU physics.`
      );
    }

    gl.attachShader(program, vs);
    gl.attachShader(program, fs);

    // Specify transform feedback varyings before linking
    gl.transformFeedbackVaryings(program, TF_VARYINGS, gl.INTERLEAVED_ATTRIBS);

    gl.linkProgram(program);

    // System F/Omega proof: Explicit validation of program linking
    // Type proof: gl.getProgramParameter(program, gl.LINK_STATUS) ∈ boolean
    // Mathematical proof: Program must link successfully
    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
      const errorLog = gl.getProgramInfoLog(program) || "No error log available";
      console.error("Transform feedback program link error:", errorLog);
      gl.deleteProgram(program);
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      throw new Error(
        `[ParticleGPUPhysics] Cannot create transform feedback program: Program linking failed. ` +
        `Error log: ${errorLog}. ` +
        `Transform feedback varyings: ${TF_VARYINGS.join(", ")}. ` +
        `Wrap in try/catch to fallback to CPU physics.`
      );
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
      // Priority: direction > vortexAxis > windDirection
      const directionX = (field.direction !== null && field.direction !== undefined && typeof field.direction === "object" && "x" in field.direction && typeof field.direction.x === "number") ? field.direction.x : ((field.vortexAxis !== null && field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && "x" in field.vortexAxis && typeof field.vortexAxis.x === "number") ? field.vortexAxis.x : ((field.windDirection !== null && field.windDirection !== undefined && typeof field.windDirection === "object" && "x" in field.windDirection && typeof field.windDirection.x === "number") ? field.windDirection.x : 0));
      const directionY = (field.direction !== null && field.direction !== undefined && typeof field.direction === "object" && "y" in field.direction && typeof field.direction.y === "number") ? field.direction.y : ((field.vortexAxis !== null && field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && "y" in field.vortexAxis && typeof field.vortexAxis.y === "number") ? field.vortexAxis.y : ((field.windDirection !== null && field.windDirection !== undefined && typeof field.windDirection === "object" && "y" in field.windDirection && typeof field.windDirection.y === "number") ? field.windDirection.y : 0));
      const directionZ = (field.direction !== null && field.direction !== undefined && typeof field.direction === "object" && "z" in field.direction && typeof field.direction.z === "number") ? field.direction.z : ((field.vortexAxis !== null && field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && "z" in field.vortexAxis && typeof field.vortexAxis.z === "number") ? field.vortexAxis.z : ((field.windDirection !== null && field.windDirection !== undefined && typeof field.windDirection === "object" && "z" in field.windDirection && typeof field.windDirection.z === "number") ? field.windDirection.z : 0));
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
          safe(directionX, 0),
          safe(directionY, 0),
          safe(directionZ, 0),
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const tex = (textureProps != null && typeof textureProps === "object" && "__webglTexture" in textureProps && textureProps.__webglTexture != null) ? textureProps.__webglTexture : undefined;
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
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const vortexAxis = (field != null && typeof field === "object" && "vortexAxis" in field && field.vortexAxis != null && typeof field.vortexAxis === "object") ? field.vortexAxis : undefined;
        const vortexAxisX = (vortexAxis != null && typeof vortexAxis === "object" && "x" in vortexAxis && typeof vortexAxis.x === "number") ? vortexAxis.x : undefined;
        const vortexAxisY = (vortexAxis != null && typeof vortexAxis === "object" && "y" in vortexAxis && typeof vortexAxis.y === "number") ? vortexAxis.y : undefined;
        const vortexAxisZ = (vortexAxis != null && typeof vortexAxis === "object" && "z" in vortexAxis && typeof vortexAxis.z === "number") ? vortexAxis.z : undefined;
        this.forceFieldBuffer[baseOffset + 8] = safeFloat(vortexAxisX, 0);
        this.forceFieldBuffer[baseOffset + 9] = safeFloat(vortexAxisY, 1);
        this.forceFieldBuffer[baseOffset + 10] = safeFloat(vortexAxisZ, 0);
        this.forceFieldBuffer[baseOffset + 11] = safeFloat(field.pathRadius, 100);
      } else {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
        // Priority: direction > vortexAxis > windDirection
        const directionX = (field.direction !== null && field.direction !== undefined && typeof field.direction === "object" && "x" in field.direction && typeof field.direction.x === "number") ? field.direction.x : ((field.vortexAxis !== null && field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && "x" in field.vortexAxis && typeof field.vortexAxis.x === "number") ? field.vortexAxis.x : ((field.windDirection !== null && field.windDirection !== undefined && typeof field.windDirection === "object" && "x" in field.windDirection && typeof field.windDirection.x === "number") ? field.windDirection.x : 0));
        const directionY = (field.direction !== null && field.direction !== undefined && typeof field.direction === "object" && "y" in field.direction && typeof field.direction.y === "number") ? field.direction.y : ((field.vortexAxis !== null && field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && "y" in field.vortexAxis && typeof field.vortexAxis.y === "number") ? field.vortexAxis.y : ((field.windDirection !== null && field.windDirection !== undefined && typeof field.windDirection === "object" && "y" in field.windDirection && typeof field.windDirection.y === "number") ? field.windDirection.y : 0));
        const directionZ = (field.direction !== null && field.direction !== undefined && typeof field.direction === "object" && "z" in field.direction && typeof field.direction.z === "number") ? field.direction.z : ((field.vortexAxis !== null && field.vortexAxis !== undefined && typeof field.vortexAxis === "object" && "z" in field.vortexAxis && typeof field.vortexAxis.z === "number") ? field.vortexAxis.z : ((field.windDirection !== null && field.windDirection !== undefined && typeof field.windDirection === "object" && "z" in field.windDirection && typeof field.windDirection.z === "number") ? field.windDirection.z : 0));
        this.forceFieldBuffer[baseOffset + 8] = safeFloat(directionX, 0);
        this.forceFieldBuffer[baseOffset + 9] = safeFloat(directionY, 0);
        this.forceFieldBuffer[baseOffset + 10] = safeFloat(directionZ, 0);
        this.forceFieldBuffer[baseOffset + 11] = safeFloat(field.inwardForce, 0);
      }

      // Row 3: extra params
      if (field.type === "magnetic") {
        this.forceFieldBuffer[baseOffset + 12] = 1.0;
        this.forceFieldBuffer[baseOffset + 13] = 0;
        this.forceFieldBuffer[baseOffset + 14] = 0;
        this.forceFieldBuffer[baseOffset + 15] = 0;
      } else {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Priority: noiseScale > linearDrag > gustStrength
        const param1 = (typeof field.noiseScale === "number" && Number.isFinite(field.noiseScale)) ? field.noiseScale : ((typeof field.linearDrag === "number" && Number.isFinite(field.linearDrag)) ? field.linearDrag : ((typeof field.gustStrength === "number" && Number.isFinite(field.gustStrength)) ? field.gustStrength : 0));
        // Priority: noiseSpeed > quadraticDrag > gustFrequency
        const param2 = (typeof field.noiseSpeed === "number" && Number.isFinite(field.noiseSpeed)) ? field.noiseSpeed : ((typeof field.quadraticDrag === "number" && Number.isFinite(field.quadraticDrag)) ? field.quadraticDrag : ((typeof field.gustFrequency === "number" && Number.isFinite(field.gustFrequency)) ? field.gustFrequency : 0));
        this.forceFieldBuffer[baseOffset + 12] = safeFloat(param1, 0);
        this.forceFieldBuffer[baseOffset + 13] = safeFloat(param2, 0);
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

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const forceFieldTexture = this.forceFieldTexture;
    if (forceFieldTexture != null && typeof forceFieldTexture === "object" && typeof forceFieldTexture.dispose === "function") {
      forceFieldTexture.dispose();
    }
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
