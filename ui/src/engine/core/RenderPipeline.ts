/**
 * RenderPipeline - Multi-Pass WebGL Rendering
 *
 * Manages the Three.js WebGL renderer with:
 * - Main color rendering
 * - Depth buffer capture
 * - Post-processing effects via EffectComposer
 * - Frame capture for export
 */

import * as THREE from "three";
import { BokehPass } from "three/examples/jsm/postprocessing/BokehPass.js";
import { EffectComposer } from "three/examples/jsm/postprocessing/EffectComposer.js";
import { OutputPass } from "three/examples/jsm/postprocessing/OutputPass.js";
import type { Pass } from "three/examples/jsm/postprocessing/Pass.js";
import { RenderPass } from "three/examples/jsm/postprocessing/RenderPass.js";
import { ShaderPass } from "three/examples/jsm/postprocessing/ShaderPass.js";
import { SSAOPass } from "three/examples/jsm/postprocessing/SSAOPass.js";
import { UnrealBloomPass } from "three/examples/jsm/postprocessing/UnrealBloomPass.js";
import {
  MOTION_BLUR_PRESETS,
  MotionBlurProcessor,
  type MotionBlurType,
} from "@/services/motionBlur";
import type { CameraController } from "./CameraController";
import type { SceneManager } from "./SceneManager";

// Local Pass type since PostPass doesn't exist in main namespace
type PostPass = Pass;

// ============================================================================
// DOF CONFIGURATION
// ============================================================================

export interface DOFConfig {
  enabled: boolean;
  focusDistance: number; // Focus distance in world units
  aperture: number; // Aperture size (affects bokeh intensity)
  maxBlur: number; // Maximum blur amount (0-1)
}

/**
 * SSAO (Screen Space Ambient Occlusion) Configuration
 */
export interface SSAOConfig {
  enabled: boolean;
  kernelRadius: number; // Occlusion sampling radius (default: 8)
  minDistance: number; // Minimum distance threshold (default: 0.005)
  maxDistance: number; // Maximum distance threshold (default: 0.1)
  intensity: number; // Occlusion intensity multiplier (default: 1)
  output: "default" | "ssao" | "blur" | "depth" | "normal";
}

/**
 * Bloom Configuration
 * For emissive objects (lights, particles, bright areas)
 */
export interface BloomConfig {
  enabled: boolean;
  strength: number; // Bloom intensity (default: 1.5)
  radius: number; // Bloom spread radius (default: 0.4)
  threshold: number; // Brightness threshold for bloom (default: 0.85)
}

/**
 * Motion Blur Configuration
 * Uses MotionBlurProcessor for various blur types
 */
export interface MotionBlurConfig {
  enabled: boolean;
  type: MotionBlurType;
  shutterAngle: number; // 0-720 (180 = standard film)
  shutterPhase: number; // -180 to 180
  samplesPerFrame: number; // Quality (2-64)
  // For advanced use
  preset?: string; // Named preset from MOTION_BLUR_PRESETS
}

export interface RenderPipelineConfig {
  canvas: HTMLCanvasElement;
  width: number;
  height: number;
  pixelRatio?: number;
  antialias?: boolean;
  alpha?: boolean;
}

export class RenderPipeline {
  private readonly renderer: THREE.WebGLRenderer;
  private readonly composer: EffectComposer;
  private readonly scene: SceneManager;
  private readonly camera: CameraController;

  // Render targets
  private colorTarget: THREE.WebGLRenderTarget;
  private depthTarget: THREE.WebGLRenderTarget;

  // Frame capture
  private readonly captureCanvas: OffscreenCanvas;
  private readonly captureCtx: OffscreenCanvasRenderingContext2D;

  // Depth capture material
  private readonly depthMaterial: THREE.ShaderMaterial;

  // Normal material for normal pass
  private readonly normalMaterial: THREE.MeshNormalMaterial;

  // Dimensions
  private width: number;
  private height: number;
  private pixelRatio: number;

  // Render mode
  private renderMode: "color" | "depth" | "normal" = "color";

  // DOF pass
  private bokehPass: BokehPass | null = null;
  private dofConfig: DOFConfig = {
    enabled: false,
    focusDistance: 500,
    aperture: 0.025,
    maxBlur: 0.01,
  };

  // SSAO pass
  private ssaoPass: SSAOPass | null = null;
  private ssaoConfig: SSAOConfig = {
    enabled: false,
    kernelRadius: 8,
    minDistance: 0.005,
    maxDistance: 0.1,
    intensity: 1,
    output: "default",
  };

  // Bloom pass (for emissive objects and lights)
  private bloomPass: UnrealBloomPass | null = null;
  private bloomConfig: BloomConfig = {
    enabled: false,
    strength: 1.5,
    radius: 0.4,
    threshold: 0.85,
  };

  // Motion blur processor (canvas-based, applied post-render)
  private motionBlurProcessor: MotionBlurProcessor;
  private motionBlurConfig: MotionBlurConfig = {
    enabled: false,
    type: "standard",
    shutterAngle: 180,
    shutterPhase: -90,
    samplesPerFrame: 16,
  };

  constructor(
    config: RenderPipelineConfig,
    scene: SceneManager,
    camera: CameraController,
  ) {
    this.scene = scene;
    this.camera = camera;
    this.width = config.width;
    this.height = config.height;
    this.pixelRatio = config.pixelRatio ?? Math.min(window.devicePixelRatio, 2);

    // Create WebGL renderer with optimized settings
    this.renderer = new THREE.WebGLRenderer({
      canvas: config.canvas,
      antialias: config.antialias ?? true,
      alpha: config.alpha ?? true,
      preserveDrawingBuffer: true, // Required for frame capture
      powerPreference: "high-performance",
      stencil: false,
      depth: true,
    });

    // Configure renderer
    this.renderer.setPixelRatio(this.pixelRatio);
    this.renderer.setSize(this.width, this.height);

    // Color space and tone mapping - wrapped in try-catch due to potential
    // conflicts with multiple Three.js instances in ComfyUI environment
    try {
      this.renderer.outputColorSpace = THREE.SRGBColorSpace;
      this.renderer.toneMapping = THREE.ACESFilmicToneMapping;
      this.renderer.toneMappingExposure = 1.0;
    } catch (e) {
      console.warn(
        "[RenderPipeline] Could not set color space/tone mapping:",
        e,
      );
      // Fallback: just set tone mapping exposure if possible
      try {
        this.renderer.toneMappingExposure = 1.0;
      } catch {
        /* ignore */
      }
    }

    // Enable shadows
    this.renderer.shadowMap.enabled = true;
    this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;

    // Create render targets
    const scaledWidth = Math.floor(this.width * this.pixelRatio);
    const scaledHeight = Math.floor(this.height * this.pixelRatio);

    this.colorTarget = this.createColorTarget(scaledWidth, scaledHeight);
    this.depthTarget = this.createDepthTarget(scaledWidth, scaledHeight);

    // Create effect composer
    this.composer = new EffectComposer(this.renderer, this.colorTarget);
    this.setupDefaultPasses();

    // Create capture canvas
    this.captureCanvas = new OffscreenCanvas(scaledWidth, scaledHeight);
    this.captureCtx = this.captureCanvas.getContext("2d")!;

    // Create depth material
    this.depthMaterial = this.createDepthMaterial();

    // Create normal material
    this.normalMaterial = new THREE.MeshNormalMaterial();

    // Initialize motion blur processor
    this.motionBlurProcessor = new MotionBlurProcessor(
      scaledWidth,
      scaledHeight,
    );
  }

  // ============================================================================
  // RENDER TARGET CREATION
  // ============================================================================

  private createColorTarget(
    width: number,
    height: number,
  ): THREE.WebGLRenderTarget {
    const target = new THREE.WebGLRenderTarget(width, height, {
      minFilter: THREE.LinearFilter,
      magFilter: THREE.LinearFilter,
      format: THREE.RGBAFormat,
      type: THREE.HalfFloatType,
      colorSpace: THREE.SRGBColorSpace,
      depthBuffer: true,
      stencilBuffer: false,
      samples: 4, // MSAA
    });

    // Attach depth texture for depth visualization
    // This allows us to read the depth buffer in post-processing
    target.depthTexture = new THREE.DepthTexture(width, height);
    target.depthTexture.format = THREE.DepthFormat;
    target.depthTexture.type = THREE.UnsignedIntType;

    return target;
  }

  private createDepthTarget(
    width: number,
    height: number,
  ): THREE.WebGLRenderTarget {
    const target = new THREE.WebGLRenderTarget(width, height, {
      minFilter: THREE.NearestFilter,
      magFilter: THREE.NearestFilter,
      format: THREE.RGBAFormat,
      type: THREE.FloatType,
      depthBuffer: true,
      stencilBuffer: false,
    });

    // Attach depth texture
    target.depthTexture = new THREE.DepthTexture(width, height);
    target.depthTexture.format = THREE.DepthFormat;
    target.depthTexture.type = THREE.FloatType;

    return target;
  }

  private createDepthMaterial(): THREE.ShaderMaterial {
    return new THREE.ShaderMaterial({
      vertexShader: `
        varying vec2 vUv;
        void main() {
          vUv = uv;
          gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
        }
      `,
      fragmentShader: `
        #include <packing>

        varying vec2 vUv;
        uniform sampler2D tDepth;
        uniform float cameraNear;
        uniform float cameraFar;

        float readDepth(sampler2D depthSampler, vec2 coord) {
          float fragCoordZ = texture2D(depthSampler, coord).x;
          float viewZ = perspectiveDepthToViewZ(fragCoordZ, cameraNear, cameraFar);
          return viewZToOrthographicDepth(viewZ, cameraNear, cameraFar);
        }

        void main() {
          float depth = readDepth(tDepth, vUv);
          gl_FragColor = vec4(vec3(1.0 - depth), 1.0);
        }
      `,
      uniforms: {
        tDepth: { value: null },
        cameraNear: { value: 0.1 },
        cameraFar: { value: 10000 },
      },
      depthWrite: false,
      depthTest: false,
    });
  }

  // ============================================================================
  // POST-PROCESSING
  // ============================================================================

  private setupDefaultPasses(): void {
    // Main render pass
    const renderPass = new RenderPass(this.scene.scene, this.camera.camera);
    this.composer.addPass(renderPass);

    // Output pass (tone mapping, color space conversion)
    const outputPass = new OutputPass();
    this.composer.addPass(outputPass);
  }

  /**
   * Add a post-processing pass
   */
  addPass(pass: PostPass): void {
    // Insert before output pass
    const outputIndex = this.composer.passes.findIndex(
      (p) => p.constructor.name === "OutputPass",
    );

    if (outputIndex > -1) {
      this.composer.insertPass(pass, outputIndex);
    } else {
      this.composer.addPass(pass);
    }
  }

  /**
   * Remove a post-processing pass
   */
  removePass(pass: PostPass): void {
    this.composer.removePass(pass);
  }

  // ============================================================================
  // DEPTH OF FIELD
  // ============================================================================

  /**
   * Configure depth of field effect
   */
  setDOF(config: Partial<DOFConfig>): void {
    // Update config
    this.dofConfig = { ...this.dofConfig, ...config };

    if (this.dofConfig.enabled) {
      // Create or update bokeh pass
      if (!this.bokehPass) {
        this.createBokehPass();
      }
      this.updateBokehPass();
    } else {
      // Remove bokeh pass if it exists
      if (this.bokehPass) {
        this.composer.removePass(this.bokehPass);
        this.bokehPass = null;
      }
    }
  }

  /**
   * Get current DOF configuration
   */
  getDOF(): DOFConfig {
    return { ...this.dofConfig };
  }

  /**
   * Create the bokeh (DOF) pass
   */
  private createBokehPass(): void {
    const _scaledWidth = Math.floor(this.width * this.pixelRatio);
    const _scaledHeight = Math.floor(this.height * this.pixelRatio);

    // BokehPass needs the scene, camera, and focus parameters
    this.bokehPass = new BokehPass(
      this.scene.scene,
      this.camera.camera,
      {
        focus: this.dofConfig.focusDistance,
        aperture: this.dofConfig.aperture,
        maxblur: this.dofConfig.maxBlur,
      } as any, // width/height are needed but not in types
    );

    // Insert before output pass
    this.addPass(this.bokehPass);
  }

  /**
   * Update bokeh pass parameters
   */
  private updateBokehPass(): void {
    if (!this.bokehPass) return;

    const uniforms = (this.bokehPass as any).uniforms;
    if (uniforms) {
      uniforms.focus.value = this.dofConfig.focusDistance;
      uniforms.aperture.value = this.dofConfig.aperture;
      uniforms.maxblur.value = this.dofConfig.maxBlur;
    }
  }

  /**
   * Set focus distance (convenience method)
   */
  setFocusDistance(distance: number): void {
    this.setDOF({ focusDistance: distance });
  }

  /**
   * Set aperture size (convenience method)
   */
  setAperture(aperture: number): void {
    this.setDOF({ aperture });
  }

  /**
   * Enable/disable DOF (convenience method)
   */
  setDOFEnabled(enabled: boolean): void {
    this.setDOF({ enabled });
  }

  // ============================================================================
  // SSAO (Screen Space Ambient Occlusion)
  // ============================================================================

  /**
   * Configure SSAO effect
   */
  setSSAO(config: Partial<SSAOConfig>): void {
    this.ssaoConfig = { ...this.ssaoConfig, ...config };

    if (this.ssaoConfig.enabled) {
      if (!this.ssaoPass) {
        this.createSSAOPass();
      }
      this.updateSSAOPass();
    } else {
      if (this.ssaoPass) {
        this.composer.removePass(this.ssaoPass);
        this.ssaoPass = null;
      }
    }
  }

  /**
   * Get current SSAO configuration
   */
  getSSAO(): SSAOConfig {
    return { ...this.ssaoConfig };
  }

  /**
   * Create the SSAO pass
   */
  private createSSAOPass(): void {
    const scaledWidth = Math.floor(this.width * this.pixelRatio);
    const scaledHeight = Math.floor(this.height * this.pixelRatio);

    this.ssaoPass = new SSAOPass(
      this.scene.scene,
      this.camera.camera,
      scaledWidth,
      scaledHeight,
    );

    // SSAO should be applied early in the pipeline (after render, before DOF)
    // Find the render pass and insert after it
    const renderPassIndex = this.composer.passes.findIndex(
      (p) => p.constructor.name === "RenderPass",
    );

    if (renderPassIndex > -1) {
      this.composer.insertPass(this.ssaoPass, renderPassIndex + 1);
    } else {
      this.addPass(this.ssaoPass);
    }
  }

  /**
   * Update SSAO pass parameters
   */
  private updateSSAOPass(): void {
    if (!this.ssaoPass) return;

    this.ssaoPass.kernelRadius = this.ssaoConfig.kernelRadius;
    this.ssaoPass.minDistance = this.ssaoConfig.minDistance;
    this.ssaoPass.maxDistance = this.ssaoConfig.maxDistance;

    // Map output mode to SSAOPass output enum
    const outputMap: Record<SSAOConfig["output"], number> = {
      default: SSAOPass.OUTPUT.Default,
      ssao: SSAOPass.OUTPUT.SSAO,
      blur: SSAOPass.OUTPUT.Blur,
      depth: SSAOPass.OUTPUT.Depth,
      normal: SSAOPass.OUTPUT.Normal,
    };
    this.ssaoPass.output = outputMap[this.ssaoConfig.output];
  }

  /**
   * Enable/disable SSAO (convenience method)
   */
  setSSAOEnabled(enabled: boolean): void {
    this.setSSAO({ enabled });
  }

  /**
   * Set SSAO intensity (convenience method)
   */
  setSSAOIntensity(intensity: number): void {
    this.setSSAO({ intensity });
  }

  /**
   * Set SSAO kernel radius (convenience method)
   */
  setSSAORadius(radius: number): void {
    this.setSSAO({ kernelRadius: radius });
  }

  // ============================================================================
  // BLOOM (Emissive Glow)
  // ============================================================================

  /**
   * Configure bloom effect
   * Makes emissive objects (lights, particles) glow
   */
  setBloom(config: Partial<BloomConfig>): void {
    this.bloomConfig = { ...this.bloomConfig, ...config };

    if (this.bloomConfig.enabled) {
      if (!this.bloomPass) {
        this.createBloomPass();
      }
      this.updateBloomPass();
    } else {
      if (this.bloomPass) {
        this.composer.removePass(this.bloomPass);
        this.bloomPass = null;
      }
    }
  }

  /**
   * Get current bloom configuration
   */
  getBloom(): BloomConfig {
    return { ...this.bloomConfig };
  }

  /**
   * Create the bloom pass
   */
  private createBloomPass(): void {
    const scaledWidth = Math.floor(this.width * this.pixelRatio);
    const scaledHeight = Math.floor(this.height * this.pixelRatio);

    this.bloomPass = new UnrealBloomPass(
      new THREE.Vector2(scaledWidth, scaledHeight),
      this.bloomConfig.strength,
      this.bloomConfig.radius,
      this.bloomConfig.threshold,
    );

    // Insert bloom after SSAO but before DOF
    // Find SSAO pass first
    const ssaoIndex = this.composer.passes.findIndex(
      (p) => p.constructor.name === "SSAOPass",
    );

    if (ssaoIndex > -1) {
      this.composer.insertPass(this.bloomPass, ssaoIndex + 1);
    } else {
      // Insert after render pass
      const renderIndex = this.composer.passes.findIndex(
        (p) => p.constructor.name === "RenderPass",
      );
      if (renderIndex > -1) {
        this.composer.insertPass(this.bloomPass, renderIndex + 1);
      } else {
        this.addPass(this.bloomPass);
      }
    }
  }

  /**
   * Update bloom pass parameters
   */
  private updateBloomPass(): void {
    if (!this.bloomPass) return;

    this.bloomPass.strength = this.bloomConfig.strength;
    this.bloomPass.radius = this.bloomConfig.radius;
    this.bloomPass.threshold = this.bloomConfig.threshold;
  }

  /**
   * Enable/disable bloom (convenience method)
   */
  setBloomEnabled(enabled: boolean): void {
    this.setBloom({ enabled });
  }

  /**
   * Set bloom intensity (convenience method)
   */
  setBloomStrength(strength: number): void {
    this.setBloom({ strength });
  }

  /**
   * Set bloom threshold (convenience method)
   */
  setBloomThreshold(threshold: number): void {
    this.setBloom({ threshold });
  }

  // ============================================================================
  // MOTION BLUR CONFIGURATION
  // ============================================================================

  /**
   * Configure motion blur
   */
  setMotionBlur(config: Partial<MotionBlurConfig>): void {
    this.motionBlurConfig = { ...this.motionBlurConfig, ...config };

    // Update processor settings
    this.motionBlurProcessor.setSettings({
      enabled: this.motionBlurConfig.enabled,
      type: this.motionBlurConfig.type,
      shutterAngle: this.motionBlurConfig.shutterAngle,
      shutterPhase: this.motionBlurConfig.shutterPhase,
      samplesPerFrame: this.motionBlurConfig.samplesPerFrame,
    });
  }

  /**
   * Enable/disable motion blur
   */
  setMotionBlurEnabled(enabled: boolean): void {
    this.setMotionBlur({ enabled });
  }

  /**
   * Set motion blur type
   */
  setMotionBlurType(type: MotionBlurType): void {
    this.setMotionBlur({ type });
  }

  /**
   * Set shutter angle (0-720, 180 = standard film)
   */
  setMotionBlurShutterAngle(shutterAngle: number): void {
    this.setMotionBlur({ shutterAngle });
  }

  /**
   * Apply a motion blur preset by name
   */
  setMotionBlurPreset(presetName: string): void {
    const preset = MOTION_BLUR_PRESETS[presetName];
    if (preset) {
      this.setMotionBlur({
        enabled: true,
        type: preset.type || "standard",
        shutterAngle: preset.shutterAngle || 180,
        shutterPhase: preset.shutterPhase || -90,
        samplesPerFrame: preset.samplesPerFrame || 16,
        preset: presetName,
      });
    }
  }

  /**
   * Get current motion blur configuration
   */
  getMotionBlurConfig(): MotionBlurConfig {
    return { ...this.motionBlurConfig };
  }

  /**
   * Get the motion blur processor (for advanced use)
   */
  getMotionBlurProcessor(): MotionBlurProcessor {
    return this.motionBlurProcessor;
  }

  // ============================================================================
  // RENDERING
  // ============================================================================

  /**
   * Render the current frame
   */
  render(): void {
    try {
      // Ensure layers are sorted by Z
      this.scene.sortByZ();

      // Ensure all scene objects have required methods (multi-Three.js compatibility)
      // This is CRITICAL for handling TransformControls when other ComfyUI extensions
      // load their own Three.js instance
      this.scene.prepareForRender();

      // Ensure camera has layers (cross-Three.js compatibility)
      if (this.camera?.camera && !this.camera.camera.layers) {
        this.camera.camera.layers = new THREE.Layers();
      }

      // Render through effect composer
      this.composer.render();
    } catch (e) {
      // Log but don't crash - the render loop must continue
      console.warn("[RenderPipeline] Render error (continuing):", e);
    }
  }

  /**
   * Render directly to a render target
   */
  renderToTarget(target: THREE.WebGLRenderTarget): void {
    const prevTarget = this.renderer.getRenderTarget();
    this.renderer.setRenderTarget(target);
    this.renderer.render(this.scene.scene, this.camera.camera);
    this.renderer.setRenderTarget(prevTarget);
  }

  // ============================================================================
  // RENDER MODE
  // ============================================================================

  // Depth visualization pass for post-processing
  private depthVisualizationPass: ShaderPass | null = null;

  // Normal visualization pass for post-processing
  private normalVisualizationPass: ShaderPass | null = null;

  /**
   * Set the render mode (color, depth, normal)
   * Uses post-processing to visualize depth/normals from the depth buffer
   * This works with ALL geometry including text since it reads from the depth buffer
   */
  setRenderMode(mode: "color" | "depth" | "normal"): void {
    this.renderMode = mode;

    // Remove existing visualization passes
    if (this.depthVisualizationPass) {
      this.composer.removePass(this.depthVisualizationPass);
      this.depthVisualizationPass = null;
    }
    if (this.normalVisualizationPass) {
      this.composer.removePass(this.normalVisualizationPass);
      this.normalVisualizationPass = null;
    }

    // Clear any override material
    this.scene.scene.overrideMaterial = null;

    if (mode === "depth") {
      // Create depth visualization pass that reads from the depth buffer
      // Uses the colorTarget's depth texture which contains actual Z-depth of ALL geometry
      this.depthVisualizationPass = new ShaderPass({
        uniforms: {
          tDiffuse: { value: null },
          tDepth: { value: this.colorTarget.depthTexture },
          cameraNear: { value: this.camera.camera.near },
          cameraFar: { value: this.camera.camera.far },
        },
        vertexShader: `
          varying vec2 vUv;
          void main() {
            vUv = uv;
            gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
          }
        `,
        fragmentShader: `
          #include <packing>
          uniform sampler2D tDiffuse;
          uniform sampler2D tDepth;
          uniform float cameraNear;
          uniform float cameraFar;
          varying vec2 vUv;

          float readDepth(sampler2D depthSampler, vec2 coord) {
            float fragCoordZ = texture2D(depthSampler, coord).x;
            float viewZ = perspectiveDepthToViewZ(fragCoordZ, cameraNear, cameraFar);
            return viewZToOrthographicDepth(viewZ, cameraNear, cameraFar);
          }

          void main() {
            float depth = readDepth(tDepth, vUv);
            // White = close, Black = far (standard depth map convention for AI video)
            gl_FragColor = vec4(vec3(1.0 - depth), 1.0);
          }
        `,
      });

      // Insert before output pass
      const outputIndex = this.composer.passes.findIndex(
        (p) => p.constructor.name === "OutputPass",
      );
      if (outputIndex > -1) {
        this.composer.insertPass(this.depthVisualizationPass, outputIndex);
      } else {
        this.composer.addPass(this.depthVisualizationPass);
      }
    } else if (mode === "normal") {
      // Screen-space normal reconstruction from depth buffer
      // This works with ALL geometry including text, particles, etc.
      // Reconstructs normals by computing gradients in the depth buffer
      const scaledWidth = Math.floor(this.width * this.pixelRatio);
      const scaledHeight = Math.floor(this.height * this.pixelRatio);

      this.normalVisualizationPass = new ShaderPass({
        uniforms: {
          tDiffuse: { value: null },
          tDepth: { value: this.colorTarget.depthTexture },
          cameraNear: { value: this.camera.camera.near },
          cameraFar: { value: this.camera.camera.far },
          resolution: { value: new THREE.Vector2(scaledWidth, scaledHeight) },
          cameraProjectionMatrix: {
            value: this.camera.camera.projectionMatrix,
          },
          cameraProjectionMatrixInverse: {
            value: this.camera.camera.projectionMatrixInverse,
          },
        },
        vertexShader: `
          varying vec2 vUv;
          void main() {
            vUv = uv;
            gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
          }
        `,
        fragmentShader: `
          #include <packing>
          uniform sampler2D tDiffuse;
          uniform sampler2D tDepth;
          uniform float cameraNear;
          uniform float cameraFar;
          uniform vec2 resolution;
          uniform mat4 cameraProjectionMatrix;
          uniform mat4 cameraProjectionMatrixInverse;
          varying vec2 vUv;

          // Convert depth buffer value to linear depth
          float getLinearDepth(vec2 coord) {
            float fragCoordZ = texture2D(tDepth, coord).x;
            float viewZ = perspectiveDepthToViewZ(fragCoordZ, cameraNear, cameraFar);
            return viewZToOrthographicDepth(viewZ, cameraNear, cameraFar);
          }

          // Reconstruct view-space position from depth
          vec3 getViewPosition(vec2 coord, float depth) {
            vec4 clipPos = vec4(coord * 2.0 - 1.0, depth * 2.0 - 1.0, 1.0);
            vec4 viewPos = cameraProjectionMatrixInverse * clipPos;
            return viewPos.xyz / viewPos.w;
          }

          void main() {
            // Sample depth at current pixel and neighbors
            vec2 texelSize = 1.0 / resolution;

            float depthC = getLinearDepth(vUv);
            float depthL = getLinearDepth(vUv - vec2(texelSize.x, 0.0));
            float depthR = getLinearDepth(vUv + vec2(texelSize.x, 0.0));
            float depthU = getLinearDepth(vUv + vec2(0.0, texelSize.y));
            float depthD = getLinearDepth(vUv - vec2(0.0, texelSize.y));

            // Handle edges and background (depth = 1.0)
            if (depthC > 0.999) {
              gl_FragColor = vec4(0.5, 0.5, 1.0, 1.0); // Default normal pointing at camera
              return;
            }

            // Reconstruct view-space positions
            vec3 posC = getViewPosition(vUv, depthC);
            vec3 posL = getViewPosition(vUv - vec2(texelSize.x, 0.0), depthL);
            vec3 posR = getViewPosition(vUv + vec2(texelSize.x, 0.0), depthR);
            vec3 posU = getViewPosition(vUv + vec2(0.0, texelSize.y), depthU);
            vec3 posD = getViewPosition(vUv - vec2(0.0, texelSize.y), depthD);

            // Calculate screen-space derivatives
            // Use the neighbor with smaller depth difference to reduce artifacts at edges
            vec3 ddx = abs(depthR - depthC) < abs(depthC - depthL) ? posR - posC : posC - posL;
            vec3 ddy = abs(depthU - depthC) < abs(depthC - depthD) ? posU - posC : posC - posD;

            // Calculate normal from cross product
            vec3 normal = normalize(cross(ddx, ddy));

            // Flip normal to face camera if needed
            if (normal.z < 0.0) normal = -normal;

            // Convert from view-space normal (-1 to 1) to color (0 to 1)
            // Standard normal map convention: RGB = (normal + 1) / 2
            gl_FragColor = vec4(normal * 0.5 + 0.5, 1.0);
          }
        `,
      });

      // Insert before output pass
      const outputIndex = this.composer.passes.findIndex(
        (p) => p.constructor.name === "OutputPass",
      );
      if (outputIndex > -1) {
        this.composer.insertPass(this.normalVisualizationPass, outputIndex);
      } else {
        this.composer.addPass(this.normalVisualizationPass);
      }
    }
    // For 'color' mode, passes are already removed and override cleared
  }

  /**
   * Get the current render mode
   */
  getRenderMode(): "color" | "depth" | "normal" {
    return this.renderMode;
  }

  // ============================================================================
  // FRAME CAPTURE
  // ============================================================================

  /**
   * Capture the current frame as ImageData
   */
  captureFrame(): ImageData {
    const width = Math.floor(this.width * this.pixelRatio);
    const height = Math.floor(this.height * this.pixelRatio);

    // Read pixels from render target
    const buffer = new Uint8Array(width * height * 4);
    this.renderer.readRenderTargetPixels(
      this.colorTarget,
      0,
      0,
      width,
      height,
      buffer,
    );

    // Convert to Uint8ClampedArray and flip Y
    const flipped = new Uint8ClampedArray(buffer.length);
    const rowSize = width * 4;

    for (let y = 0; y < height; y++) {
      const srcRow = (height - 1 - y) * rowSize;
      const dstRow = y * rowSize;
      flipped.set(buffer.subarray(srcRow, srcRow + rowSize), dstRow);
    }

    return new ImageData(flipped, width, height);
  }

  /**
   * Capture the depth buffer
   */
  captureDepth(): Float32Array {
    const width = Math.floor(this.width * this.pixelRatio);
    const height = Math.floor(this.height * this.pixelRatio);

    // Render to depth target
    this.renderToTarget(this.depthTarget);

    // Read depth texture
    const buffer = new Float32Array(width * height * 4);
    this.renderer.readRenderTargetPixels(
      this.depthTarget,
      0,
      0,
      width,
      height,
      buffer,
    );

    // Extract single channel (depth is in all channels for float target)
    const depth = new Float32Array(width * height);
    for (let i = 0; i < width * height; i++) {
      // Normalize depth from clip space
      depth[i] = buffer[i * 4]; // R channel contains depth
    }

    // Flip Y
    const flipped = new Float32Array(width * height);
    for (let y = 0; y < height; y++) {
      const srcRow = (height - 1 - y) * width;
      const dstRow = y * width;
      flipped.set(depth.subarray(srcRow, srcRow + width), dstRow);
    }

    return flipped;
  }

  // ============================================================================
  // RESIZE
  // ============================================================================

  /**
   * Resize the renderer and targets
   */
  resize(width: number, height: number): void {
    this.width = width;
    this.height = height;

    const scaledWidth = Math.floor(width * this.pixelRatio);
    const scaledHeight = Math.floor(height * this.pixelRatio);

    // Resize renderer
    this.renderer.setSize(width, height);

    // Resize effect composer
    this.composer.setSize(scaledWidth, scaledHeight);

    // Dispose and recreate render targets
    this.colorTarget.dispose();
    this.depthTarget.dispose();

    this.colorTarget = this.createColorTarget(scaledWidth, scaledHeight);
    this.depthTarget = this.createDepthTarget(scaledWidth, scaledHeight);

    // Update composer's render target
    this.composer.renderTarget1.dispose();
    this.composer.renderTarget2.dispose();
    (this.composer as any).renderTarget1 = this.colorTarget.clone();
    (this.composer as any).renderTarget2 = this.colorTarget.clone();

    // Resize capture canvas
    this.captureCanvas.width = scaledWidth;
    this.captureCanvas.height = scaledHeight;

    // Recreate bokeh pass if DOF is enabled (needs new render targets)
    if (this.bokehPass && this.dofConfig.enabled) {
      this.composer.removePass(this.bokehPass);
      this.bokehPass = null;
      this.createBokehPass();
    }

    // Recreate SSAO pass if enabled (needs new dimensions)
    if (this.ssaoPass && this.ssaoConfig.enabled) {
      this.composer.removePass(this.ssaoPass);
      this.ssaoPass = null;
      this.createSSAOPass();
      this.updateSSAOPass();
    }

    // Recreate bloom pass if enabled (needs new dimensions)
    if (this.bloomPass && this.bloomConfig.enabled) {
      this.composer.removePass(this.bloomPass);
      this.bloomPass.dispose();
      this.bloomPass = null;
      this.createBloomPass();
      this.updateBloomPass();
    }
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Get the underlying WebGL renderer
   */
  getWebGLRenderer(): THREE.WebGLRenderer {
    return this.renderer;
  }

  /**
   * Get renderer info (for debugging)
   */
  getInfo(): THREE.WebGLInfo {
    return this.renderer.info;
  }

  /**
   * Get current dimensions
   */
  getDimensions(): { width: number; height: number; pixelRatio: number } {
    return {
      width: this.width,
      height: this.height,
      pixelRatio: this.pixelRatio,
    };
  }

  // ============================================================================
  // NESTED COMPOSITION RENDER-TO-TEXTURE
  // ============================================================================

  /** Cache of render targets for nested compositions (keyed by compositionId) */
  private nestedCompTargets: Map<string, THREE.WebGLRenderTarget> = new Map();

  /**
   * Create or get a render target for a nested composition
   */
  getNestedCompRenderTarget(
    compositionId: string,
    width: number,
    height: number,
  ): THREE.WebGLRenderTarget {
    const key = `${compositionId}_${width}_${height}`;

    let target = this.nestedCompTargets.get(key);
    if (!target) {
      target = new THREE.WebGLRenderTarget(width, height, {
        minFilter: THREE.LinearFilter,
        magFilter: THREE.LinearFilter,
        format: THREE.RGBAFormat,
        type: THREE.UnsignedByteType,
        colorSpace: THREE.SRGBColorSpace,
        depthBuffer: true,
        stencilBuffer: false,
      });
      this.nestedCompTargets.set(key, target);
    }

    return target;
  }

  /**
   * Render a scene to an offscreen target and return the texture
   * Used for nested composition rendering
   */
  renderSceneToTexture(
    scene: THREE.Scene,
    camera: THREE.Camera,
    target: THREE.WebGLRenderTarget,
  ): THREE.Texture {
    const prevTarget = this.renderer.getRenderTarget();

    this.renderer.setRenderTarget(target);
    this.renderer.clear();
    this.renderer.render(scene, camera);
    this.renderer.setRenderTarget(prevTarget);

    return target.texture;
  }

  /**
   * Dispose a nested composition render target
   */
  disposeNestedCompTarget(compositionId: string): void {
    // Find and dispose all targets for this composition
    for (const [key, target] of this.nestedCompTargets.entries()) {
      if (key.startsWith(`${compositionId}_`)) {
        target.dispose();
        this.nestedCompTargets.delete(key);
      }
    }
  }

  /**
   * Dispose all nested composition render targets
   */
  disposeAllNestedCompTargets(): void {
    for (const target of this.nestedCompTargets.values()) {
      target.dispose();
    }
    this.nestedCompTargets.clear();
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  /**
   * Get the DOM element (canvas) attached to the renderer
   * Used for attaching controls like TransformControls
   */
  getDomElement(): HTMLCanvasElement {
    return this.renderer.domElement;
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    // Dispose DOF pass if enabled
    if (this.bokehPass) {
      this.composer.removePass(this.bokehPass);
      this.bokehPass = null;
    }

    // Dispose SSAO pass if enabled
    if (this.ssaoPass) {
      this.composer.removePass(this.ssaoPass);
      this.ssaoPass = null;
    }

    // Dispose bloom pass if enabled
    if (this.bloomPass) {
      this.composer.removePass(this.bloomPass);
      this.bloomPass.dispose();
      this.bloomPass = null;
    }

    // Dispose nested composition targets
    this.disposeAllNestedCompTargets();

    this.colorTarget.dispose();
    this.depthTarget.dispose();
    this.depthMaterial.dispose();
    this.normalMaterial.dispose();
    this.composer.dispose();
    this.renderer.dispose();
  }
}
