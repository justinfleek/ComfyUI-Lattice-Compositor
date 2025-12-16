/**
 * RenderPipeline - Multi-Pass WebGL Rendering
 *
 * Manages the Three.js WebGL renderer with:
 * - Main color rendering
 * - Depth buffer capture
 * - Post-processing effects via EffectComposer
 * - Frame capture for export
 */

import * as THREE from 'three';
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js';
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js';
import { OutputPass } from 'three/examples/jsm/postprocessing/OutputPass.js';
import { ShaderPass } from 'three/examples/jsm/postprocessing/ShaderPass.js';
import { BokehPass } from 'three/examples/jsm/postprocessing/BokehPass.js';
import { Pass } from 'three/examples/jsm/postprocessing/Pass.js';
import type { SceneManager } from './SceneManager';
import type { CameraController } from './CameraController';

// Local Pass type since PostPass doesn't exist in main namespace
type PostPass = Pass;

// ============================================================================
// DOF CONFIGURATION
// ============================================================================

export interface DOFConfig {
  enabled: boolean;
  focusDistance: number;  // Focus distance in world units
  aperture: number;       // Aperture size (affects bokeh intensity)
  maxBlur: number;        // Maximum blur amount (0-1)
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
  private renderMode: 'color' | 'depth' | 'normal' = 'color';

  // DOF pass
  private bokehPass: BokehPass | null = null;
  private dofConfig: DOFConfig = {
    enabled: false,
    focusDistance: 500,
    aperture: 0.025,
    maxBlur: 0.01,
  };

  constructor(
    config: RenderPipelineConfig,
    scene: SceneManager,
    camera: CameraController
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
      powerPreference: 'high-performance',
      stencil: false,
      depth: true,
    });

    // Configure renderer
    this.renderer.setPixelRatio(this.pixelRatio);
    this.renderer.setSize(this.width, this.height);
    this.renderer.outputColorSpace = THREE.SRGBColorSpace;
    this.renderer.toneMapping = THREE.ACESFilmicToneMapping;
    this.renderer.toneMappingExposure = 1.0;

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
    this.captureCtx = this.captureCanvas.getContext('2d')!;

    // Create depth material
    this.depthMaterial = this.createDepthMaterial();

    // Create normal material
    this.normalMaterial = new THREE.MeshNormalMaterial();
  }

  // ============================================================================
  // RENDER TARGET CREATION
  // ============================================================================

  private createColorTarget(width: number, height: number): THREE.WebGLRenderTarget {
    return new THREE.WebGLRenderTarget(width, height, {
      minFilter: THREE.LinearFilter,
      magFilter: THREE.LinearFilter,
      format: THREE.RGBAFormat,
      type: THREE.HalfFloatType,
      colorSpace: THREE.SRGBColorSpace,
      depthBuffer: true,
      stencilBuffer: false,
      samples: 4, // MSAA
    });
  }

  private createDepthTarget(width: number, height: number): THREE.WebGLRenderTarget {
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
      p => p.constructor.name === 'OutputPass'
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
    const scaledWidth = Math.floor(this.width * this.pixelRatio);
    const scaledHeight = Math.floor(this.height * this.pixelRatio);

    // BokehPass needs the scene, camera, and focus parameters
    this.bokehPass = new BokehPass(
      this.scene.scene,
      this.camera.camera,
      {
        focus: this.dofConfig.focusDistance,
        aperture: this.dofConfig.aperture,
        maxblur: this.dofConfig.maxBlur,
      } as any // width/height are needed but not in types
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
  // RENDERING
  // ============================================================================

  /**
   * Render the current frame
   */
  render(): void {
    // Ensure layers are sorted by Z
    this.scene.sortByZ();

    // Render through effect composer
    this.composer.render();
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

  /**
   * Set the render mode (color, depth, normal)
   */
  setRenderMode(mode: 'color' | 'depth' | 'normal'): void {
    this.renderMode = mode;

    if (mode === 'depth' || mode === 'normal') {
      // Override scene materials
      this.scene.scene.overrideMaterial = mode === 'depth' ? this.depthMaterial : this.normalMaterial;
    } else {
      // Clear override to use original materials
      this.scene.scene.overrideMaterial = null;
    }
  }

  /**
   * Get the current render mode
   */
  getRenderMode(): 'color' | 'depth' | 'normal' {
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
      0, 0, width, height,
      buffer
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
      0, 0, width, height,
      buffer
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
  // PRECOMP RENDER-TO-TEXTURE
  // ============================================================================

  /** Cache of render targets for precomps (keyed by compositionId) */
  private precompTargets: Map<string, THREE.WebGLRenderTarget> = new Map();

  /**
   * Create or get a render target for a precomp composition
   */
  getPrecompRenderTarget(compositionId: string, width: number, height: number): THREE.WebGLRenderTarget {
    const key = `${compositionId}_${width}_${height}`;

    let target = this.precompTargets.get(key);
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
      this.precompTargets.set(key, target);
    }

    return target;
  }

  /**
   * Render a scene to an offscreen target and return the texture
   * Used for precomp rendering
   */
  renderSceneToTexture(
    scene: THREE.Scene,
    camera: THREE.Camera,
    target: THREE.WebGLRenderTarget
  ): THREE.Texture {
    const prevTarget = this.renderer.getRenderTarget();

    this.renderer.setRenderTarget(target);
    this.renderer.clear();
    this.renderer.render(scene, camera);
    this.renderer.setRenderTarget(prevTarget);

    return target.texture;
  }

  /**
   * Dispose a precomp render target
   */
  disposePrecompTarget(compositionId: string): void {
    // Find and dispose all targets for this composition
    for (const [key, target] of this.precompTargets.entries()) {
      if (key.startsWith(compositionId + '_')) {
        target.dispose();
        this.precompTargets.delete(key);
      }
    }
  }

  /**
   * Dispose all precomp render targets
   */
  disposeAllPrecompTargets(): void {
    for (const target of this.precompTargets.values()) {
      target.dispose();
    }
    this.precompTargets.clear();
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

    // Dispose precomp targets
    this.disposeAllPrecompTargets();

    this.colorTarget.dispose();
    this.depthTarget.dispose();
    this.depthMaterial.dispose();
    this.normalMaterial.dispose();
    this.composer.dispose();
    this.renderer.dispose();
  }
}
