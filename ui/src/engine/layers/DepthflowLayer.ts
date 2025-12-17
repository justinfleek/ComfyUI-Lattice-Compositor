/**
 * DepthflowLayer - Depth-Based Parallax Effect Layer
 *
 * Creates Ken Burns / parallax 3D effects using depth maps:
 * - Takes a source image layer and depth map layer
 * - Applies displacement based on camera movement
 * - Supports multiple presets (zoom, pan, orbit, dolly zoom, etc.)
 * - Edge dilation and inpainting for cleaner parallax
 */

import * as THREE from 'three';
import type { Layer, DepthflowLayerData, DepthflowConfig, AnimatableProperty } from '@/types/project';
import type { ResourceManager } from '../core/ResourceManager';
import { BaseLayer } from './BaseLayer';
import { layerLogger } from '@/utils/logger';

// ============================================================================
// SHADERS
// ============================================================================

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

// ============================================================================
// DEPTHFLOW LAYER
// ============================================================================

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

  // Animation state
  private animationTime: number = 0;

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
    const data = layerData.data as DepthflowLayerData | null;

    return {
      sourceLayerId: data?.sourceLayerId ?? '',
      depthLayerId: data?.depthLayerId ?? '',
      config: {
        preset: data?.config?.preset ?? 'static',
        zoom: data?.config?.zoom ?? 1,
        offsetX: data?.config?.offsetX ?? 0,
        offsetY: data?.config?.offsetY ?? 0,
        rotation: data?.config?.rotation ?? 0,
        depthScale: data?.config?.depthScale ?? 0.1,
        focusDepth: data?.config?.focusDepth ?? 0.5,
        dollyZoom: data?.config?.dollyZoom ?? 0,
        orbitRadius: data?.config?.orbitRadius ?? 0.1,
        orbitSpeed: data?.config?.orbitSpeed ?? 1,
        swingAmplitude: data?.config?.swingAmplitude ?? 0.05,
        swingFrequency: data?.config?.swingFrequency ?? 1,
        edgeDilation: data?.config?.edgeDilation ?? 0,
        inpaintEdges: data?.config?.inpaintEdges ?? false,
      },
      animatedZoom: data?.animatedZoom,
      animatedOffsetX: data?.animatedOffsetX,
      animatedOffsetY: data?.animatedOffsetY,
      animatedRotation: data?.animatedRotation,
      animatedDepthScale: data?.animatedDepthScale,
    };
  }

  /**
   * Load source and depth textures from referenced layers
   */
  private async loadTextures(): Promise<void> {
    // Load source texture
    if (this.depthflowData.sourceLayerId) {
      const sourceTexture = await this.loadTextureFromLayer(this.depthflowData.sourceLayerId);
      if (sourceTexture) {
        this.sourceTexture = sourceTexture;
        this.material.uniforms.sourceTexture.value = sourceTexture;

        // Update dimensions from texture
        if (sourceTexture.image) {
          this.setDimensions(sourceTexture.image.width, sourceTexture.image.height);
        }
      }
    }

    // Load depth texture
    if (this.depthflowData.depthLayerId) {
      const depthTexture = await this.loadTextureFromLayer(this.depthflowData.depthLayerId);
      if (depthTexture) {
        this.depthTexture = depthTexture;
        this.material.uniforms.depthTexture.value = depthTexture;
      }
    }
  }

  /**
   * Load texture from a layer (image layer asset)
   */
  private async loadTextureFromLayer(layerId: string): Promise<THREE.Texture | null> {
    // Try to get the layer's texture from ResourceManager
    // This assumes the source layer is an image layer with an assetId
    const texture = this.resources.getLayerTexture(layerId);
    if (texture) return texture;

    layerLogger.warn(`DepthflowLayer: Could not load texture for layer ${layerId}`);
    return null;
  }

  /**
   * Set mesh dimensions
   */
  setDimensions(width: number, height: number): void {
    if (width === this.width && height === this.height) return;

    this.width = width;
    this.height = height;

    // Recreate geometry
    this.geometry.dispose();
    this.geometry = new THREE.PlaneGeometry(width, height);
    this.mesh.geometry = this.geometry;
  }

  /**
   * Set source layer
   */
  async setSourceLayer(layerId: string): Promise<void> {
    this.depthflowData.sourceLayerId = layerId;
    const texture = await this.loadTextureFromLayer(layerId);
    if (texture) {
      this.sourceTexture?.dispose();
      this.sourceTexture = texture;
      this.material.uniforms.sourceTexture.value = texture;
    }
  }

  /**
   * Set depth layer
   */
  async setDepthLayer(layerId: string): Promise<void> {
    this.depthflowData.depthLayerId = layerId;
    const texture = await this.loadTextureFromLayer(layerId);
    if (texture) {
      this.depthTexture?.dispose();
      this.depthTexture = texture;
      this.material.uniforms.depthTexture.value = texture;
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
      this.material.uniforms.rotation.value = THREE.MathUtils.degToRad(config.rotation);
    }
    if (config.edgeDilation !== undefined) {
      this.material.uniforms.edgeDilation.value = config.edgeDilation;
    }
  }

  /**
   * Calculate preset-based animation values
   */
  private calculatePresetValues(frame: number, fps: number = 30): {
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
    let rotation = config.rotation;

    switch (config.preset) {
      case 'static':
        // No animation
        break;

      case 'zoom_in':
        zoom = 1 + progress * 0.5;
        break;

      case 'zoom_out':
        zoom = 1.5 - progress * 0.5;
        break;

      case 'dolly_zoom_in':
        zoom = 1 + progress * 0.5;
        // Counteract zoom with depth to create vertigo effect
        this.material.uniforms.depthScale.value = config.depthScale * (1 + config.dollyZoom * progress);
        break;

      case 'dolly_zoom_out':
        zoom = 1.5 - progress * 0.5;
        this.material.uniforms.depthScale.value = config.depthScale * (1 + config.dollyZoom * (1 - progress));
        break;

      case 'pan_left':
        offsetX = progress * 0.2;
        break;

      case 'pan_right':
        offsetX = -progress * 0.2;
        break;

      case 'pan_up':
        offsetY = progress * 0.2;
        break;

      case 'pan_down':
        offsetY = -progress * 0.2;
        break;

      case 'circle_cw':
        offsetX = Math.sin(progress * Math.PI * 2) * config.orbitRadius;
        offsetY = Math.cos(progress * Math.PI * 2) * config.orbitRadius;
        break;

      case 'circle_ccw':
        offsetX = -Math.sin(progress * Math.PI * 2) * config.orbitRadius;
        offsetY = Math.cos(progress * Math.PI * 2) * config.orbitRadius;
        break;

      case 'horizontal_swing':
        offsetX = Math.sin(time * config.swingFrequency * Math.PI * 2) * config.swingAmplitude;
        break;

      case 'vertical_swing':
        offsetY = Math.sin(time * config.swingFrequency * Math.PI * 2) * config.swingAmplitude;
        break;

      case 'custom':
        // Use animated properties (handled in evaluateFrame)
        break;
    }

    return { zoom, offsetX, offsetY, rotation };
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    const config = this.depthflowData.config;

    // Calculate preset-based values
    const presetValues = this.calculatePresetValues(frame);

    // Override with animated properties if present
    let zoom = presetValues.zoom;
    let offsetX = presetValues.offsetX;
    let offsetY = presetValues.offsetY;
    let rotation = presetValues.rotation;

    if (this.depthflowData.animatedZoom) {
      zoom = this.evaluator.evaluate(this.depthflowData.animatedZoom, frame);
    }
    if (this.depthflowData.animatedOffsetX) {
      offsetX = this.evaluator.evaluate(this.depthflowData.animatedOffsetX, frame);
    }
    if (this.depthflowData.animatedOffsetY) {
      offsetY = this.evaluator.evaluate(this.depthflowData.animatedOffsetY, frame);
    }
    if (this.depthflowData.animatedRotation) {
      rotation = this.evaluator.evaluate(this.depthflowData.animatedRotation, frame);
    }
    if (this.depthflowData.animatedDepthScale) {
      this.material.uniforms.depthScale.value = this.evaluator.evaluate(
        this.depthflowData.animatedDepthScale,
        frame
      );
    }

    // Apply driven values
    zoom = this.getDrivenOrBase('depthflow.zoom', zoom);
    offsetX = this.getDrivenOrBase('depthflow.offsetX', offsetX);
    offsetY = this.getDrivenOrBase('depthflow.offsetY', offsetY);
    rotation = this.getDrivenOrBase('depthflow.rotation', rotation);

    // Update uniforms
    this.material.uniforms.zoom.value = zoom;
    this.material.uniforms.offset.value.set(offsetX, offsetY);
    this.material.uniforms.rotation.value = THREE.MathUtils.degToRad(rotation);
    this.material.uniforms.time.value = frame / 30;

    // Mark material as needing update
    this.material.needsUpdate = true;
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    const props = state.properties;

    // Apply evaluated depthflow properties
    if (props['zoom'] !== undefined) {
      this.material.uniforms.zoom.value = props['zoom'] as number;
    }

    if (props['offsetX'] !== undefined || props['offsetY'] !== undefined) {
      const offsetX = (props['offsetX'] as number) ?? this.material.uniforms.offset.value.x;
      const offsetY = (props['offsetY'] as number) ?? this.material.uniforms.offset.value.y;
      this.material.uniforms.offset.value.set(offsetX, offsetY);
    }

    if (props['rotation'] !== undefined) {
      this.material.uniforms.rotation.value = THREE.MathUtils.degToRad(props['rotation'] as number);
    }

    if (props['depthScale'] !== undefined) {
      this.material.uniforms.depthScale.value = props['depthScale'] as number;
    }

    this.material.needsUpdate = true;
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<DepthflowLayerData> | undefined;

    if (!data) return;

    // Update source/depth layers
    if (data.sourceLayerId !== undefined && data.sourceLayerId !== this.depthflowData.sourceLayerId) {
      this.setSourceLayer(data.sourceLayerId);
    }

    if (data.depthLayerId !== undefined && data.depthLayerId !== this.depthflowData.depthLayerId) {
      this.setDepthLayer(data.depthLayerId);
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
    this.sourceTexture?.dispose();
    this.depthTexture?.dispose();

    // Dispose geometry and material
    this.geometry.dispose();
    this.material.dispose();
  }
}
