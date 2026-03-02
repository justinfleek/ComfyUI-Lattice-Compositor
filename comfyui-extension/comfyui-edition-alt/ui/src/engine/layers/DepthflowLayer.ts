/**
 * DepthflowLayer - Depth-Based Parallax Effect Layer
 *
 * Creates Ken Burns / parallax 3D effects using depth maps:
 * - Takes a source image layer and depth map layer
 * - Applies displacement based on camera movement
 * - Supports multiple presets (zoom, pan, orbit, dolly zoom, etc.)
 * - Edge dilation and inpainting for cleaner parallax
 */

import * as THREE from "three";
import type {
  DepthflowConfig,
  DepthflowLayerData,
  Layer,
} from "@/types/project";
import { layerLogger } from "@/utils/logger";
import type { ResourceManager } from "../core/ResourceManager";
import { BaseLayer } from "./BaseLayer";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                   // shaders
// ════════════════════════════════════════════════════════════════════════════

const depthflowVertexShader = `
  varying vec2 vUv;

  void main() {
    vUv = uv;
    gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
  }
`;

const depthflowFragmentShader = `
  uniform sampler2D sourceTexture;
  uniform sampler2D depthTexture;
  uniform float depthScale;
  uniform float focusDepth;
  uniform vec2 offset;
  uniform float zoom;
  uniform float rotation;
  uniform float edgeDilation;
  uniform float time;

  varying vec2 vUv;

  // Rotate UV around center
  vec2 rotateUV(vec2 uv, float angle) {
    float s = sin(angle);
    float c = cos(angle);
    uv -= 0.5;
    uv = vec2(uv.x * c - uv.y * s, uv.x * s + uv.y * c);
    uv += 0.5;
    return uv;
  }

  void main() {
    // Sample depth at current UV
    float depth = texture2D(depthTexture, vUv).r;

    // Calculate displacement based on depth
    // Objects at focusDepth have no displacement
    float depthDiff = depth - focusDepth;
    float displacement = depthDiff * depthScale;

    // Apply zoom (perspective effect - closer objects move more)
    vec2 zoomedUV = (vUv - 0.5) / zoom + 0.5;

    // Apply rotation
    vec2 rotatedUV = rotateUV(zoomedUV, rotation);

    // Apply offset with depth-based parallax
    vec2 parallaxOffset = offset * (1.0 + displacement);
    vec2 finalUV = rotatedUV + parallaxOffset;

    // Edge handling - dilate edges slightly
    vec2 edgeUV = finalUV;
    if (edgeDilation > 0.0) {
      // Simple edge stretch when outside [0,1] range
      if (finalUV.x < 0.0) edgeUV.x = finalUV.x * (1.0 - edgeDilation);
      if (finalUV.x > 1.0) edgeUV.x = 1.0 - (1.0 - finalUV.x) * (1.0 - edgeDilation);
      if (finalUV.y < 0.0) edgeUV.y = finalUV.y * (1.0 - edgeDilation);
      if (finalUV.y > 1.0) edgeUV.y = 1.0 - (1.0 - finalUV.y) * (1.0 - edgeDilation);
    }

    // Clamp to valid range (or could use mirror/repeat)
    finalUV = clamp(edgeUV, 0.0, 1.0);

    // Sample source with displaced UVs
    vec4 color = texture2D(sourceTexture, finalUV);

    // Handle edges - fade out pixels that would be outside the source
    float edgeFade = 1.0;
    float edgeThreshold = 0.01;
    if (edgeUV.x < edgeThreshold || edgeUV.x > 1.0 - edgeThreshold ||
        edgeUV.y < edgeThreshold || edgeUV.y > 1.0 - edgeThreshold) {
      edgeFade = 0.0;
    }

    gl_FragColor = vec4(color.rgb, color.a * edgeFade);
  }
`;

// ════════════════════════════════════════════════════════════════════════════
//                                                        // depthflow // layer
// ════════════════════════════════════════════════════════════════════════════

export class DepthflowLayer extends BaseLayer {
  private readonly resources: ResourceManager;

  // Textures
  private sourceTexture: THREE.Texture | null = null;
  private depthTexture: THREE.Texture | null = null;

  // Mesh and material
  private mesh: THREE.Mesh;
  private geometry: THREE.PlaneGeometry;
  private material: THREE.ShaderMaterial;

  // Layer data
  private depthflowData: DepthflowLayerData;

  // Dimensions
  private width: number = 1920;
  private height: number = 1080;

  constructor(layerData: Layer, resources: ResourceManager) {
    super(layerData);

    this.resources = resources;

    // Extract depthflow data
    this.depthflowData = this.extractDepthflowData(layerData);

    // Create geometry
    this.geometry = new THREE.PlaneGeometry(this.width, this.height);

    // Create shader material
    this.material = new THREE.ShaderMaterial({
      uniforms: {
        sourceTexture: { value: null },
        depthTexture: { value: null },
        depthScale: { value: this.depthflowData.config.depthScale },
        focusDepth: { value: this.depthflowData.config.focusDepth },
        offset: { value: new THREE.Vector2(0, 0) },
        zoom: { value: this.depthflowData.config.zoom },
        rotation: { value: this.depthflowData.config.rotation },
        edgeDilation: { value: this.depthflowData.config.edgeDilation },
        time: { value: 0 },
      },
      vertexShader: depthflowVertexShader,
      fragmentShader: depthflowFragmentShader,
      transparent: true,
      side: THREE.DoubleSide,
      depthWrite: false,
    });

    // Create mesh
    this.mesh = new THREE.Mesh(this.geometry, this.material);
    this.mesh.name = `depthflow_${this.id}`;
    this.group.add(this.mesh);

    // Load source and depth textures
    this.loadTextures();

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  /**
   * Extract depthflow data with defaults
   */
  private extractDepthflowData(layerData: Layer): DepthflowLayerData {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: data ∈ DepthflowLayerData | null → DepthflowLayerData (with explicit defaults)
    const data = (layerData.data !== null && typeof layerData.data === "object") ? layerData.data as DepthflowLayerData : null;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: Extract each property with explicit type narrowing and defaults
    const sourceLayerIdValue = (data !== null && typeof data === "object" && "sourceLayerId" in data && typeof data.sourceLayerId === "string") ? data.sourceLayerId : "";
    const depthLayerIdValue = (data !== null && typeof data === "object" && "depthLayerId" in data && typeof data.depthLayerId === "string") ? data.depthLayerId : "";
    
    // Pattern match: config properties with explicit type narrowing
    const configData = (data !== null && typeof data === "object" && "config" in data && typeof data.config === "object" && data.config !== null) ? data.config : null;
    const presetValue = (configData !== null && typeof configData === "object" && "preset" in configData && typeof configData.preset === "string") ? configData.preset : "static";
    const zoomValue = (configData !== null && typeof configData === "object" && "zoom" in configData && typeof configData.zoom === "number" && Number.isFinite(configData.zoom)) ? configData.zoom : 1;
    const offsetXValue = (configData !== null && typeof configData === "object" && "offsetX" in configData && typeof configData.offsetX === "number" && Number.isFinite(configData.offsetX)) ? configData.offsetX : 0;
    const offsetYValue = (configData !== null && typeof configData === "object" && "offsetY" in configData && typeof configData.offsetY === "number" && Number.isFinite(configData.offsetY)) ? configData.offsetY : 0;
    const rotationValue = (configData !== null && typeof configData === "object" && "rotation" in configData && typeof configData.rotation === "number" && Number.isFinite(configData.rotation)) ? configData.rotation : 0;
    const depthScaleValue = (configData !== null && typeof configData === "object" && "depthScale" in configData && typeof configData.depthScale === "number" && Number.isFinite(configData.depthScale)) ? configData.depthScale : 0.1;
    const focusDepthValue = (configData !== null && typeof configData === "object" && "focusDepth" in configData && typeof configData.focusDepth === "number" && Number.isFinite(configData.focusDepth)) ? configData.focusDepth : 0.5;
    const dollyZoomValue = (configData !== null && typeof configData === "object" && "dollyZoom" in configData && typeof configData.dollyZoom === "number" && Number.isFinite(configData.dollyZoom)) ? configData.dollyZoom : 0;
    const orbitRadiusValue = (configData !== null && typeof configData === "object" && "orbitRadius" in configData && typeof configData.orbitRadius === "number" && Number.isFinite(configData.orbitRadius)) ? configData.orbitRadius : 0.1;
    const orbitSpeedValue = (configData !== null && typeof configData === "object" && "orbitSpeed" in configData && typeof configData.orbitSpeed === "number" && Number.isFinite(configData.orbitSpeed)) ? configData.orbitSpeed : 1;
    const swingAmplitudeValue = (configData !== null && typeof configData === "object" && "swingAmplitude" in configData && typeof configData.swingAmplitude === "number" && Number.isFinite(configData.swingAmplitude)) ? configData.swingAmplitude : 0.05;
    const swingFrequencyValue = (configData !== null && typeof configData === "object" && "swingFrequency" in configData && typeof configData.swingFrequency === "number" && Number.isFinite(configData.swingFrequency)) ? configData.swingFrequency : 1;
    const edgeDilationValue = (configData !== null && typeof configData === "object" && "edgeDilation" in configData && typeof configData.edgeDilation === "number" && Number.isFinite(configData.edgeDilation)) ? configData.edgeDilation : 0;
    const inpaintEdgesValue = (configData !== null && typeof configData === "object" && "inpaintEdges" in configData && typeof configData.inpaintEdges === "boolean") ? configData.inpaintEdges : false;
    
    const animatedZoomValue = (data !== null && typeof data === "object" && "animatedZoom" in data) ? data.animatedZoom : undefined;
    const animatedOffsetXValue = (data !== null && typeof data === "object" && "animatedOffsetX" in data) ? data.animatedOffsetX : undefined;

    return {
      sourceLayerId: sourceLayerIdValue,
      depthLayerId: depthLayerIdValue,
      config: {
        preset: presetValue,
        zoom: zoomValue,
        offsetX: offsetXValue,
        offsetY: offsetYValue,
        rotation: rotationValue,
        depthScale: depthScaleValue,
        focusDepth: focusDepthValue,
        dollyZoom: dollyZoomValue,
        orbitRadius: orbitRadiusValue,
        orbitSpeed: orbitSpeedValue,
        swingAmplitude: swingAmplitudeValue,
        swingFrequency: swingFrequencyValue,
        edgeDilation: edgeDilationValue,
        inpaintEdges: inpaintEdgesValue,
      },
      animatedZoom: animatedZoomValue,
      animatedOffsetX: animatedOffsetXValue,
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      animatedOffsetY: (data != null && typeof data === "object" && "animatedOffsetY" in data && typeof data.animatedOffsetY === "boolean") ? data.animatedOffsetY : undefined,
      animatedRotation: (data != null && typeof data === "object" && "animatedRotation" in data && typeof data.animatedRotation === "boolean") ? data.animatedRotation : undefined,
      animatedDepthScale: (data != null && typeof data === "object" && "animatedDepthScale" in data && typeof data.animatedDepthScale === "boolean") ? data.animatedDepthScale : undefined,
    };
  }

  /**
   * Load source and depth textures from referenced layers
   */
  private async loadTextures(): Promise<void> {
    // Load source texture
    if (this.depthflowData.sourceLayerId) {
      // System F/Omega: loadTextureFromLayer throws explicit errors - wrap in try/catch for expected failures
      try {
        const sourceTexture = await this.loadTextureFromLayer(
          this.depthflowData.sourceLayerId,
        );
        this.sourceTexture = sourceTexture;
        this.material.uniforms.sourceTexture.value = sourceTexture;
        
        // Update dimensions from texture
        if (sourceTexture.image) {
          this.setDimensions(
            sourceTexture.image.width,
            sourceTexture.image.height,
          );
        }
      } catch (error) {
        // Texture not available - skip source texture (expected state)
        layerLogger.warn(
          `DepthflowLayer: Could not load source texture:`,
          error instanceof Error ? error.message : String(error),
        );
      }
    }

    // Load depth texture
    if (this.depthflowData.depthLayerId) {
      // System F/Omega: loadTextureFromLayer throws explicit errors - wrap in try/catch for expected failures
      try {
        const depthTexture = await this.loadTextureFromLayer(
          this.depthflowData.depthLayerId,
        );
        this.depthTexture = depthTexture;
        this.material.uniforms.depthTexture.value = depthTexture;
      } catch (error) {
        // Texture not available - skip depth texture (expected state)
        layerLogger.warn(
          `DepthflowLayer: Could not load depth texture:`,
          error instanceof Error ? error.message : String(error),
        );
      }
    }
  }

  /**
   * Load texture from a layer (image layer asset)
   * 
   * System F/Omega proof: Explicit error throwing - never return null
   * Type proof: layerId ∈ string → Promise<THREE.Texture> (non-nullable)
   * Mathematical proof: Texture loading must succeed or throw explicit error
   * Pattern proof: Missing texture is an explicit error condition
   */
  private async loadTextureFromLayer(
    layerId: string,
  ): Promise<THREE.Texture> {
    // System F/Omega: getLayerTexture throws explicit errors - propagate them
    try {
      const texture = this.resources.getLayerTexture(layerId);
      return texture;
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      layerLogger.warn(
        `DepthflowLayer: Could not load texture for layer ${layerId}:`,
        errorMessage,
      );
      throw new Error(
        `[DepthflowLayer] Cannot load texture from layer: Texture not found. ` +
        `Layer ID: ${layerId}. ` +
        `Original error: ${errorMessage}. ` +
        `Wrap in try/catch if "texture not cached" is an expected state.`
      );
    }
  }

  /**
   * Set mesh dimensions
   */
  setDimensions(width: number, height: number): void {
    // Validate dimensions (NaN/0 would create invalid geometry)
    const validWidth = Number.isFinite(width) && width > 0 ? width : 1920;
    const validHeight = Number.isFinite(height) && height > 0 ? height : 1080;

    if (validWidth === this.width && validHeight === this.height) return;

    this.width = validWidth;
    this.height = validHeight;

    // Recreate geometry
    this.geometry.dispose();
    this.geometry = new THREE.PlaneGeometry(validWidth, validHeight);
    this.mesh.geometry = this.geometry;
  }

  /**
   * Set source layer
   */
  async setSourceLayer(layerId: string): Promise<void> {
    this.depthflowData.sourceLayerId = layerId;
    // System F/Omega: loadTextureFromLayer throws explicit errors - wrap in try/catch for expected failures
    try {
      const texture = await this.loadTextureFromLayer(layerId);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const sourceTexture = this.sourceTexture;
      if (sourceTexture != null && typeof sourceTexture === "object" && typeof sourceTexture.dispose === "function") {
        sourceTexture.dispose();
      }
      this.sourceTexture = texture;
      this.material.uniforms.sourceTexture.value = texture;
    } catch (error) {
      // Texture not available - clear source texture (expected state)
      layerLogger.warn(
        `DepthflowLayer: Could not set source layer texture:`,
        error instanceof Error ? error.message : String(error),
      );
      const sourceTexture = this.sourceTexture;
      if (sourceTexture != null && typeof sourceTexture === "object" && typeof sourceTexture.dispose === "function") {
        sourceTexture.dispose();
      }
      this.sourceTexture = null;
    }
  }

  /**
   * Set depth layer
   */
  async setDepthLayer(layerId: string): Promise<void> {
    this.depthflowData.depthLayerId = layerId;
    // System F/Omega: loadTextureFromLayer throws explicit errors - wrap in try/catch for expected failures
    try {
      const texture = await this.loadTextureFromLayer(layerId);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const depthTexture = this.depthTexture;
      if (depthTexture != null && typeof depthTexture === "object" && typeof depthTexture.dispose === "function") {
        depthTexture.dispose();
      }
      this.depthTexture = texture;
      this.material.uniforms.depthTexture.value = texture;
    } catch (error) {
      // Texture not available - clear depth texture (expected state)
      layerLogger.warn(
        `DepthflowLayer: Could not set depth layer texture:`,
        error instanceof Error ? error.message : String(error),
      );
      const depthTexture = this.depthTexture;
      if (depthTexture != null && typeof depthTexture === "object" && typeof depthTexture.dispose === "function") {
        depthTexture.dispose();
      }
      this.depthTexture = null;
    }
  }

  /**
   * Update config values
   */
  updateConfig(config: Partial<DepthflowConfig>): void {
    Object.assign(this.depthflowData.config, config);

    // Update uniforms
    if (config.depthScale !== undefined) {
      this.material.uniforms.depthScale.value = config.depthScale;
    }
    if (config.focusDepth !== undefined) {
      this.material.uniforms.focusDepth.value = config.focusDepth;
    }
    if (config.zoom !== undefined) {
      this.material.uniforms.zoom.value = config.zoom;
    }
    if (config.rotation !== undefined) {
      this.material.uniforms.rotation.value = THREE.MathUtils.degToRad(
        config.rotation,
      );
    }
    if (config.edgeDilation !== undefined) {
      this.material.uniforms.edgeDilation.value = config.edgeDilation;
    }
  }

  /**
   * Calculate preset-based animation values
   */
  private calculatePresetValues(
    frame: number,
    fps: number = 16,
  ): {
    zoom: number;
    offsetX: number;
    offsetY: number;
    rotation: number;
  } {
    const config = this.depthflowData.config;
    const duration = this.outPoint - this.inPoint;
    const progress = duration > 0 ? (frame - this.inPoint) / duration : 0;
    const time = frame / fps;

    // Base values
    let zoom = config.zoom;
    let offsetX = config.offsetX;
    let offsetY = config.offsetY;
    const rotation = config.rotation;

    switch (config.preset) {
      case "static":
        // No animation
        break;

      case "zoom_in":
        zoom = 1 + progress * 0.5;
        break;

      case "zoom_out":
        zoom = 1.5 - progress * 0.5;
        break;

      case "dolly_zoom_in":
        zoom = 1 + progress * 0.5;
        // Counteract zoom with depth to create vertigo effect
        this.material.uniforms.depthScale.value =
          config.depthScale * (1 + config.dollyZoom * progress);
        break;

      case "dolly_zoom_out":
        zoom = 1.5 - progress * 0.5;
        this.material.uniforms.depthScale.value =
          config.depthScale * (1 + config.dollyZoom * (1 - progress));
        break;

      case "pan_left":
        offsetX = progress * 0.2;
        break;

      case "pan_right":
        offsetX = -progress * 0.2;
        break;

      case "pan_up":
        offsetY = progress * 0.2;
        break;

      case "pan_down":
        offsetY = -progress * 0.2;
        break;

      case "circle_cw":
        offsetX = Math.sin(progress * Math.PI * 2) * config.orbitRadius;
        offsetY = Math.cos(progress * Math.PI * 2) * config.orbitRadius;
        break;

      case "circle_ccw":
        offsetX = -Math.sin(progress * Math.PI * 2) * config.orbitRadius;
        offsetY = Math.cos(progress * Math.PI * 2) * config.orbitRadius;
        break;

      case "horizontal_swing":
        offsetX =
          Math.sin(time * config.swingFrequency * Math.PI * 2) *
          config.swingAmplitude;
        break;

      case "vertical_swing":
        offsetY =
          Math.sin(time * config.swingFrequency * Math.PI * 2) *
          config.swingAmplitude;
        break;

      case "custom":
        // Use animated properties (handled in evaluateFrame)
        break;
    }

    return { zoom, offsetX, offsetY, rotation };
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                               // abstract // implementations
  // ════════════════════════════════════════════════════════════════════════════

  protected onEvaluateFrame(frame: number): void {
    const _config = this.depthflowData.config;

    // Use composition fps for correct animation timing
    const fps = this.compositionFps;

    // Calculate preset-based values
    const presetValues = this.calculatePresetValues(frame, fps);

    // Override with animated properties if present
    let zoom = presetValues.zoom;
    let offsetX = presetValues.offsetX;
    let offsetY = presetValues.offsetY;
    let rotation = presetValues.rotation;

    if (this.depthflowData.animatedZoom) {
      zoom = this.evaluator.evaluate(this.depthflowData.animatedZoom, frame);
    }
    if (this.depthflowData.animatedOffsetX) {
      offsetX = this.evaluator.evaluate(
        this.depthflowData.animatedOffsetX,
        frame,
      );
    }
    if (this.depthflowData.animatedOffsetY) {
      offsetY = this.evaluator.evaluate(
        this.depthflowData.animatedOffsetY,
        frame,
      );
    }
    if (this.depthflowData.animatedRotation) {
      rotation = this.evaluator.evaluate(
        this.depthflowData.animatedRotation,
        frame,
      );
    }
    if (this.depthflowData.animatedDepthScale) {
      this.material.uniforms.depthScale.value = this.evaluator.evaluate(
        this.depthflowData.animatedDepthScale,
        frame,
      );
    }

    // Apply driven values
    zoom = this.getDrivenOrBase("depthflow.zoom", zoom);
    offsetX = this.getDrivenOrBase("depthflow.offsetX", offsetX);
    offsetY = this.getDrivenOrBase("depthflow.offsetY", offsetY);
    rotation = this.getDrivenOrBase("depthflow.rotation", rotation);

    // Update uniforms
    this.material.uniforms.zoom.value = zoom;
    this.material.uniforms.offset.value.set(offsetX, offsetY);
    this.material.uniforms.rotation.value = THREE.MathUtils.degToRad(rotation);
    this.material.uniforms.time.value = frame / fps;

    // Mark material as needing update
    this.material.needsUpdate = true;
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    const props = state.properties;

    // Apply evaluated depthflow properties
    if (props.zoom !== undefined) {
      this.material.uniforms.zoom.value = props.zoom as number;
    }

    if (props.offsetX !== undefined || props.offsetY !== undefined) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      // Pattern match: props.offsetX ∈ PropertyValue | undefined → number (fallback to material uniform)
      const offsetXValue = (typeof props.offsetX === "number" && Number.isFinite(props.offsetX)) ? props.offsetX : this.material.uniforms.offset.value.x;
      // Pattern match: props.offsetY ∈ PropertyValue | undefined → number (fallback to material uniform)
      const offsetYValue = (typeof props.offsetY === "number" && Number.isFinite(props.offsetY)) ? props.offsetY : this.material.uniforms.offset.value.y;
      this.material.uniforms.offset.value.set(offsetXValue, offsetYValue);
    }

    if (props.rotation !== undefined) {
      this.material.uniforms.rotation.value = THREE.MathUtils.degToRad(
        props.rotation as number,
      );
    }

    if (props.depthScale !== undefined) {
      this.material.uniforms.depthScale.value = props.depthScale as number;
    }

    // Apply audio-reactive modifiers (additive to base values)
    // Validate all audio modifier values to prevent NaN from corrupting uniforms
    const audioMod = this.currentAudioModifiers;

    if (
      audioMod.depthflowZoom !== undefined &&
      Number.isFinite(audioMod.depthflowZoom) &&
      audioMod.depthflowZoom !== 0
    ) {
      this.material.uniforms.zoom.value += audioMod.depthflowZoom;
    }

    if (
      audioMod.depthflowOffsetX !== undefined &&
      Number.isFinite(audioMod.depthflowOffsetX) &&
      audioMod.depthflowOffsetX !== 0
    ) {
      this.material.uniforms.offset.value.x += audioMod.depthflowOffsetX;
    }

    if (
      audioMod.depthflowOffsetY !== undefined &&
      Number.isFinite(audioMod.depthflowOffsetY) &&
      audioMod.depthflowOffsetY !== 0
    ) {
      this.material.uniforms.offset.value.y += audioMod.depthflowOffsetY;
    }

    if (
      audioMod.depthflowRotation !== undefined &&
      Number.isFinite(audioMod.depthflowRotation) &&
      audioMod.depthflowRotation !== 0
    ) {
      // Add rotation in radians (convert from degrees)
      this.material.uniforms.rotation.value += THREE.MathUtils.degToRad(
        audioMod.depthflowRotation,
      );
    }

    if (
      audioMod.depthflowDepthScale !== undefined &&
      Number.isFinite(audioMod.depthflowDepthScale) &&
      audioMod.depthflowDepthScale !== 0
    ) {
      this.material.uniforms.depthScale.value += audioMod.depthflowDepthScale;
    }

    this.material.needsUpdate = true;
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<DepthflowLayerData> | undefined;

    if (!data) return;

    // Update source/depth layers (handle null values)
    if (
      data.sourceLayerId !== undefined &&
      data.sourceLayerId !== this.depthflowData.sourceLayerId
    ) {
      if (data.sourceLayerId !== null) {
        this.setSourceLayer(data.sourceLayerId);
      } else {
        this.depthflowData.sourceLayerId = null;
      }
    }

    if (
      data.depthLayerId !== undefined &&
      data.depthLayerId !== this.depthflowData.depthLayerId
    ) {
      if (data.depthLayerId !== null) {
        this.setDepthLayer(data.depthLayerId);
      } else {
        this.depthflowData.depthLayerId = null;
      }
    }

    // Update config
    if (data.config) {
      this.updateConfig(data.config);
    }

    // Update animated properties
    if (data.animatedZoom !== undefined) {
      this.depthflowData.animatedZoom = data.animatedZoom;
    }
    if (data.animatedOffsetX !== undefined) {
      this.depthflowData.animatedOffsetX = data.animatedOffsetX;
    }
    if (data.animatedOffsetY !== undefined) {
      this.depthflowData.animatedOffsetY = data.animatedOffsetY;
    }
    if (data.animatedRotation !== undefined) {
      this.depthflowData.animatedRotation = data.animatedRotation;
    }
    if (data.animatedDepthScale !== undefined) {
      this.depthflowData.animatedDepthScale = data.animatedDepthScale;
    }
  }

  protected onDispose(): void {
    // Dispose textures
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const sourceTexture = this.sourceTexture;
    if (sourceTexture != null && typeof sourceTexture === "object" && typeof sourceTexture.dispose === "function") {
      sourceTexture.dispose();
    }
    const depthTexture = this.depthTexture;
    if (depthTexture != null && typeof depthTexture === "object" && typeof depthTexture.dispose === "function") {
      depthTexture.dispose();
    }

    // Dispose geometry and material
    this.geometry.dispose();
    this.material.dispose();
  }
}
