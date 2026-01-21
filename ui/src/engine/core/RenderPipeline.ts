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
import { Pass } from "three/examples/jsm/postprocessing/Pass.js";
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
// SENTINEL PASS OBJECTS - Lean4/PureScript/Haskell: Explicit pattern matching
// Pattern match: Never use null - use sentinel objects that implement Pass interface
// ============================================================================

/**
 * Sentinel "uninitialized" pass object
 * Extends Pass class but does nothing (no-op)
 * Used instead of null to eliminate lazy null checks
 * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
 */
class SentinelPass extends Pass {
  constructor() {
    super();
    this.enabled = false;
    this.needsSwap = false;
    this.clear = false;
    this.renderToScreen = false;
  }
  
  setSize(_width: number, _height: number): void {
    // No-op
  }
  
  render(
    _renderer: THREE.WebGLRenderer,
    _writeBuffer: THREE.WebGLRenderTarget,
    _readBuffer: THREE.WebGLRenderTarget,
    _deltaTime?: number,
    _maskActive?: boolean,
  ): void {
    // No-op
  }
  
  dispose(): void {
    // No-op
  }
}

// Singleton sentinel instance
const SENTINEL_PASS = new SentinelPass();

/**
 * Type guard to check if a pass is the sentinel (uninitialized)
 */
function isSentinelPass(pass: Pass): boolean {
  return pass === SENTINEL_PASS;
}

/**
 * Type guard to check if a pass is initialized (not sentinel)
 */
function isInitializedPass<T extends Pass>(pass: T | SentinelPass): pass is T {
  return pass !== SENTINEL_PASS;
}

// ============================================================================
// TYPE EXTENSIONS FOR THREE.JS POST-PROCESSING
// ============================================================================

/**
 * Extended BokehPass options interface
 * BokehPass constructor accepts width/height but TypeScript types may not include them
 */
interface BokehPassOptions {
  focus: number;
  aperture: number;
  maxblur: number;
  width?: number;
  height?: number;
}

/**
 * Extended BokehPass type with uniforms property
 * BokehPass has uniforms at runtime but TypeScript types may not expose them
 * System F/Omega proof: Use intersection type instead of interface extension
 * Type proof: BokehPass & { uniforms?: {...} } allows runtime property access
 */
type BokehPassWithUniforms = BokehPass & {
  uniforms?: {
    focus?: { value: number };
    aperture?: { value: number };
    maxblur?: { value: number };
  };
};

/**
 * Extended EffectComposer type with renderTarget properties
 * System F/Omega proof: Use intersection type instead of interface extension
 * EffectComposer has renderTarget1/renderTarget2 but TypeScript types may not expose them
 */
type EffectComposerWithTargets = EffectComposer & {
  renderTarget1?: THREE.WebGLRenderTarget;
  renderTarget2?: THREE.WebGLRenderTarget;
};

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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: Use sentinel object instead of null
  private bokehPass: BokehPass | SentinelPass = SENTINEL_PASS;
  private dofConfig: DOFConfig = {
    enabled: false,
    focusDistance: 500,
    aperture: 0.025,
    maxBlur: 0.01,
  };

  // SSAO pass
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: Use sentinel object instead of null
  private ssaoPass: SSAOPass | SentinelPass = SENTINEL_PASS;
  private ssaoConfig: SSAOConfig = {
    enabled: false,
    kernelRadius: 8,
    minDistance: 0.005,
    maxDistance: 0.1,
    intensity: 1,
    output: "default",
  };

  // Bloom pass (for emissive objects and lights)
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: Use sentinel object instead of null
  private bloomPass: UnrealBloomPass | SentinelPass = SENTINEL_PASS;
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null/undefined
    // PureScript: case config.pixelRatio of Just x -> x; Nothing -> default
    if (typeof config.pixelRatio === "number") {
      this.pixelRatio = config.pixelRatio;
    } else {
      this.pixelRatio = Math.min(window.devicePixelRatio, 2);
    }

    // Create WebGL renderer with optimized settings
    this.renderer = new THREE.WebGLRenderer({
      canvas: config.canvas,
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined/null checks
      // Pattern match: antialias ∈ boolean | undefined → boolean (never check undefined)
      antialias: (typeof config.antialias === "boolean") ? config.antialias : true,
      // Pattern match: alpha ∈ boolean | undefined → boolean (never check undefined)
      alpha: (typeof config.alpha === "boolean") ? config.alpha : true,
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
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
        // Pattern match: Use empty texture instead of null for Three.js uniforms
        tDepth: { value: new THREE.DataTexture(new Uint8Array([0, 0, 0, 0]), 1, 1) },
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (isSentinelPass(this.bokehPass)) {
        this.createBokehPass();
      }
      this.updateBokehPass();
    } else {
      // Remove bokeh pass if it exists
      if (isInitializedPass(this.bokehPass)) {
        this.composer.removePass(this.bokehPass);
        this.bokehPass = SENTINEL_PASS;
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
    const scaledWidth = Math.floor(this.width * this.pixelRatio);
    const scaledHeight = Math.floor(this.height * this.pixelRatio);

    // BokehPass needs the scene, camera, and focus parameters
    // Type-safe options with width/height (may not be in TypeScript types but needed at runtime)
    const bokehOptions: BokehPassOptions = {
      focus: this.dofConfig.focusDistance,
      aperture: this.dofConfig.aperture,
      maxblur: this.dofConfig.maxBlur,
      width: scaledWidth,
      height: scaledHeight,
    };
    
    this.bokehPass = new BokehPass(
      this.scene.scene,
      this.camera.camera,
      bokehOptions,
    );

    // Insert before output pass
    this.addPass(this.bokehPass);
  }

  /**
   * Update bokeh pass parameters
   */
  private updateBokehPass(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (isSentinelPass(this.bokehPass)) return;

    // Type-safe access to uniforms (may not be in TypeScript types but exists at runtime)
    // Pattern match: bokehPass is guaranteed to be BokehPass here (not SentinelPass)
    const bokehPass = this.bokehPass as BokehPass;
    const bokehWithUniforms = bokehPass as BokehPassWithUniforms;
    if (bokehWithUniforms.uniforms) {
      if (bokehWithUniforms.uniforms.focus) {
        bokehWithUniforms.uniforms.focus.value = this.dofConfig.focusDistance;
      }
      if (bokehWithUniforms.uniforms.aperture) {
        bokehWithUniforms.uniforms.aperture.value = this.dofConfig.aperture;
      }
      if (bokehWithUniforms.uniforms.maxblur) {
        bokehWithUniforms.uniforms.maxblur.value = this.dofConfig.maxBlur;
      }
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (isSentinelPass(this.ssaoPass)) {
        this.createSSAOPass();
      }
      this.updateSSAOPass();
    } else {
      if (isInitializedPass(this.ssaoPass)) {
        this.composer.removePass(this.ssaoPass);
        this.ssaoPass = SENTINEL_PASS;
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

    const ssaoPass = new SSAOPass(
      this.scene.scene,
      this.camera.camera,
      scaledWidth,
      scaledHeight,
    );
    this.ssaoPass = ssaoPass;

    // SSAO should be applied early in the pipeline (after render, before DOF)
    // Find the render pass and insert after it
    const renderPassIndex = this.composer.passes.findIndex(
      (p) => p.constructor.name === "RenderPass",
    );

    if (renderPassIndex > -1) {
      this.composer.insertPass(ssaoPass, renderPassIndex + 1);
    } else {
      this.addPass(ssaoPass);
    }
  }

  /**
   * Update SSAO pass parameters
   */
  private updateSSAOPass(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (isSentinelPass(this.ssaoPass)) return;

    // Pattern match: ssaoPass is guaranteed to be SSAOPass here (not SentinelPass)
    const ssaoPass = this.ssaoPass as SSAOPass;
    ssaoPass.kernelRadius = this.ssaoConfig.kernelRadius;
    ssaoPass.minDistance = this.ssaoConfig.minDistance;
    ssaoPass.maxDistance = this.ssaoConfig.maxDistance;

    // Map output mode to SSAOPass output enum
    const outputMap: Record<SSAOConfig["output"], number> = {
      default: SSAOPass.OUTPUT.Default,
      ssao: SSAOPass.OUTPUT.SSAO,
      blur: SSAOPass.OUTPUT.Blur,
      depth: SSAOPass.OUTPUT.Depth,
      normal: SSAOPass.OUTPUT.Normal,
    };
    ssaoPass.output = outputMap[this.ssaoConfig.output];
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (isSentinelPass(this.bloomPass)) {
        this.createBloomPass();
      }
      this.updateBloomPass();
    } else {
      if (isInitializedPass(this.bloomPass)) {
        this.composer.removePass(this.bloomPass);
        this.bloomPass = SENTINEL_PASS;
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

    const bloomPass = new UnrealBloomPass(
      new THREE.Vector2(scaledWidth, scaledHeight),
      this.bloomConfig.strength,
      this.bloomConfig.radius,
      this.bloomConfig.threshold,
    );
    this.bloomPass = bloomPass;

    // Insert bloom after SSAO but before DOF
    // Find SSAO pass first
    const ssaoIndex = this.composer.passes.findIndex(
      (p) => p.constructor.name === "SSAOPass",
    );

    if (ssaoIndex > -1) {
      this.composer.insertPass(bloomPass, ssaoIndex + 1);
    } else {
      // Insert after render pass
      const renderIndex = this.composer.passes.findIndex(
        (p) => p.constructor.name === "RenderPass",
      );
      if (renderIndex > -1) {
        this.composer.insertPass(bloomPass, renderIndex + 1);
      } else {
        this.addPass(bloomPass);
      }
    }
  }

  /**
   * Update bloom pass parameters
   */
  private updateBloomPass(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (isSentinelPass(this.bloomPass)) return;

    // Pattern match: bloomPass is guaranteed to be UnrealBloomPass here (not SentinelPass)
    const bloomPass = this.bloomPass as UnrealBloomPass;
    bloomPass.strength = this.bloomConfig.strength;
    bloomPass.radius = this.bloomConfig.radius;
    bloomPass.threshold = this.bloomConfig.threshold;
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null checks
    // Pattern match: preset ∈ MotionBlurSettings | undefined (never null)
    if (typeof preset === "object" && preset !== null) {
      // Pattern match: type ∈ MotionBlurType | undefined → MotionBlurType
      const typeValue = (typeof preset.type === "string" && preset.type.length > 0) ? preset.type : "standard";
      // Pattern match: shutterAngle ∈ number | undefined → number
      const shutterAngleValue = (typeof preset.shutterAngle === "number" && Number.isFinite(preset.shutterAngle)) ? preset.shutterAngle : 180;
      // Pattern match: shutterPhase ∈ number | undefined → number
      const shutterPhaseValue = (typeof preset.shutterPhase === "number" && Number.isFinite(preset.shutterPhase)) ? preset.shutterPhase : -90;
      // Pattern match: samplesPerFrame ∈ number | undefined → number
      const samplesPerFrameValue = (typeof preset.samplesPerFrame === "number" && Number.isFinite(preset.samplesPerFrame) && preset.samplesPerFrame > 0) ? preset.samplesPerFrame : 16;
      this.setMotionBlur({
        enabled: true,
        type: typeValue,
        shutterAngle: shutterAngleValue,
        shutterPhase: shutterPhaseValue,
        samplesPerFrame: samplesPerFrameValue,
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null checks
      // Pattern match: this.camera is always initialized (never null)
      if (typeof this.camera === "object" && "camera" in this.camera && typeof this.camera.camera === "object" && this.camera.camera !== null && !this.camera.camera.layers) {
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
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: Use sentinel object instead of null
  private depthVisualizationPass: ShaderPass | SentinelPass = SENTINEL_PASS;

  // Normal visualization pass for post-processing
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: Use sentinel object instead of null
  private normalVisualizationPass: ShaderPass | SentinelPass = SENTINEL_PASS;

  /**
   * Set the render mode (color, depth, normal)
   * Uses post-processing to visualize depth/normals from the depth buffer
   * This works with ALL geometry including text since it reads from the depth buffer
   */
  setRenderMode(mode: "color" | "depth" | "normal"): void {
    this.renderMode = mode;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    // Remove existing visualization passes
    if (isInitializedPass(this.depthVisualizationPass)) {
      this.composer.removePass(this.depthVisualizationPass);
      this.depthVisualizationPass = SENTINEL_PASS;
    }
    if (isInitializedPass(this.normalVisualizationPass)) {
      this.composer.removePass(this.normalVisualizationPass);
      this.normalVisualizationPass = SENTINEL_PASS;
    }

    // Clear any override material
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
    // Pattern match: Three.js overrideMaterial accepts null for "no override"
    // Note: Three.js API requires null here - this is the only acceptable use of null
    // as it's part of the Three.js Scene API contract
    const currentOverride = this.scene.scene.overrideMaterial;
    if (currentOverride !== null && typeof currentOverride === "object") {
      // Three.js API contract: null means "no override material"
      // This is the ONLY acceptable null assignment in this file (Three.js API requirement)
      this.scene.scene.overrideMaterial = null;
    }

    if (mode === "depth") {
      // Create depth visualization pass that reads from the depth buffer
      // Uses the colorTarget's depth texture which contains actual Z-depth of ALL geometry
      const depthVisualizationPass = new ShaderPass({
        uniforms: {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
          // Pattern match: Use empty texture instead of null for Three.js uniforms
          tDiffuse: { value: new THREE.DataTexture(new Uint8Array([0, 0, 0, 0]), 1, 1) },
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
        this.composer.insertPass(depthVisualizationPass, outputIndex);
      } else {
        this.composer.addPass(depthVisualizationPass);
      }
      this.depthVisualizationPass = depthVisualizationPass;
    } else if (mode === "normal") {
      // Screen-space normal reconstruction from depth buffer
      // This works with ALL geometry including text, particles, etc.
      // Reconstructs normals by computing gradients in the depth buffer
      const scaledWidth = Math.floor(this.width * this.pixelRatio);
      const scaledHeight = Math.floor(this.height * this.pixelRatio);

      const normalVisualizationPass = new ShaderPass({
        uniforms: {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
          // Pattern match: Use empty texture instead of null for Three.js uniforms
          tDiffuse: { value: new THREE.DataTexture(new Uint8Array([0, 0, 0, 0]), 1, 1) },
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
        this.composer.insertPass(normalVisualizationPass, outputIndex);
      } else {
        this.composer.addPass(normalVisualizationPass);
      }
      this.normalVisualizationPass = normalVisualizationPass;
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

    // Update composer's render target (type-safe access)
    // EffectComposerWithTargets interface defined at top of file
    const composerWithTargets = this.composer as EffectComposerWithTargets;
    if (composerWithTargets.renderTarget1) {
      composerWithTargets.renderTarget1.dispose();
    }
    if (composerWithTargets.renderTarget2) {
      composerWithTargets.renderTarget2.dispose();
    }
    composerWithTargets.renderTarget1 = this.colorTarget.clone();
    composerWithTargets.renderTarget2 = this.colorTarget.clone();

    // Resize capture canvas
    this.captureCanvas.width = scaledWidth;
    this.captureCanvas.height = scaledHeight;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    // Recreate bokeh pass if DOF is enabled (needs new render targets)
    if (isInitializedPass(this.bokehPass) && this.dofConfig.enabled) {
      this.composer.removePass(this.bokehPass);
      this.bokehPass = SENTINEL_PASS;
      this.createBokehPass();
    }

    // Recreate SSAO pass if enabled (needs new dimensions)
    if (isInitializedPass(this.ssaoPass) && this.ssaoConfig.enabled) {
      this.composer.removePass(this.ssaoPass);
      this.ssaoPass = SENTINEL_PASS;
      this.createSSAOPass();
      this.updateSSAOPass();
    }

    // Recreate bloom pass if enabled (needs new dimensions)
    if (isInitializedPass(this.bloomPass) && this.bloomConfig.enabled) {
      this.composer.removePass(this.bloomPass);
      this.bloomPass.dispose();
      this.bloomPass = SENTINEL_PASS;
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    // Dispose DOF pass if enabled
    if (isInitializedPass(this.bokehPass)) {
      this.composer.removePass(this.bokehPass);
      this.bokehPass = SENTINEL_PASS;
    }

    // Dispose SSAO pass if enabled
    if (isInitializedPass(this.ssaoPass)) {
      this.composer.removePass(this.ssaoPass);
      this.ssaoPass = SENTINEL_PASS;
    }

    // Dispose bloom pass if enabled
    if (isInitializedPass(this.bloomPass)) {
      this.composer.removePass(this.bloomPass);
      this.bloomPass.dispose();
      this.bloomPass = SENTINEL_PASS;
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
