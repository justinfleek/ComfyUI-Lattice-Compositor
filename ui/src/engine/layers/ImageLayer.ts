/**
 * ImageLayer - Static and Animated Image Layer
 *
 * Displays images with full transform support:
 * - Static images (PNG, JPEG, WebP)
 * - Image sequences
 * - Dynamic texture updates
 */

import * as THREE from 'three';
import type { Layer } from '@/types/project';
import type { ResourceManager } from '../core/ResourceManager';
import { BaseLayer } from './BaseLayer';
import { layerLogger } from '@/utils/logger';

export class ImageLayer extends BaseLayer {
  private mesh: THREE.Mesh;
  private geometry: THREE.PlaneGeometry;
  private material: THREE.MeshBasicMaterial;
  private texture: THREE.Texture | null = null;

  /** Resource manager for texture loading */
  private readonly resources: ResourceManager;

  /** Image dimensions */
  private imageWidth: number = 100;
  private imageHeight: number = 100;

  /** Source URL or asset ID */
  private sourceUrl: string | null = null;

  /** Fit mode for image display */
  private fit: 'none' | 'contain' | 'cover' | 'fill' = 'none';

  /** Target dimensions for fit calculations (null = use native dimensions) */
  private targetWidth: number | null = null;
  private targetHeight: number | null = null;

  /** Original (unprocessed) texture for effects source */
  private originalTexture: THREE.Texture | null = null;

  /** Canvas for rendering texture to 2D for effect processing */
  private textureCanvas: HTMLCanvasElement | null = null;
  private textureCanvasCtx: CanvasRenderingContext2D | null = null;

  constructor(layerData: Layer, resources: ResourceManager) {
    super(layerData);

    this.resources = resources;

    // Create geometry (will be resized when image loads)
    this.geometry = new THREE.PlaneGeometry(1, 1);

    // Create material
    this.material = new THREE.MeshBasicMaterial({
      color: 0xffffff,
      transparent: true,
      side: THREE.DoubleSide,
      depthWrite: false,
    });

    // Create mesh
    this.mesh = new THREE.Mesh(this.geometry, this.material);
    this.mesh.name = `image_${this.id}`;

    // Add to group
    this.group.add(this.mesh);

    // Load image if source is provided
    const imageData = this.extractImageData(layerData);
    this.fit = imageData.fit;
    this.targetWidth = imageData.targetWidth;
    this.targetHeight = imageData.targetHeight;
    if (imageData.source) {
      this.loadImage(imageData.source);
    }

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  /**
   * Extract image data from layer object
   */
  private extractImageData(layerData: Layer): {
    source: string | null;
    targetWidth: number | null;
    targetHeight: number | null;
    fit: 'none' | 'contain' | 'cover' | 'fill';
  } {
    const data = layerData.data as any;

    return {
      source: data?.source ?? data?.url ?? data?.assetId ?? null,
      targetWidth: data?.width ?? null,
      targetHeight: data?.height ?? null,
      fit: data?.fit ?? 'none',
    };
  }

  // ============================================================================
  // IMAGE LOADING
  // ============================================================================

  /**
   * Load image from URL
   */
  async loadImage(url: string): Promise<void> {
    this.sourceUrl = url;

    try {
      const texture = await this.resources.loadTexture(url, {
        minFilter: THREE.LinearFilter,
        magFilter: THREE.LinearFilter,
        generateMipmaps: false,
        colorSpace: THREE.SRGBColorSpace,
      });

      this.setTexture(texture);
    } catch (error) {
      layerLogger.error(`ImageLayer: Failed to load image: ${url}`, error);
    }
  }

  /**
   * Set texture directly
   */
  setTexture(texture: THREE.Texture): void {
    // Store as both current and original (for effects processing)
    this.texture = texture;
    this.originalTexture = texture;
    this.material.map = texture;
    this.material.needsUpdate = true;

    // Update dimensions from texture
    if (texture.image) {
      this.imageWidth = texture.image.width || texture.image.videoWidth || 100;
      this.imageHeight = texture.image.height || texture.image.videoHeight || 100;
      this.updateMeshSize();

      // Invalidate texture canvas when source changes
      this.textureCanvas = null;
      this.textureCanvasCtx = null;
      this.effectsDirty = true;
    }
  }

  /**
   * Set texture from ImageData
   */
  setTextureFromImageData(imageData: ImageData): void {
    const texture = this.resources.createTextureFromImageData(
      imageData,
      `layer_${this.id}_imagedata`,
      {
        minFilter: THREE.LinearFilter,
        magFilter: THREE.LinearFilter,
        generateMipmaps: false,
        colorSpace: THREE.SRGBColorSpace,
      }
    );

    this.setTexture(texture);
  }

  /**
   * Set texture from canvas
   */
  setTextureFromCanvas(canvas: HTMLCanvasElement | OffscreenCanvas): void {
    const texture = this.resources.createTextureFromCanvas(
      canvas,
      `layer_${this.id}_canvas`,
      {
        minFilter: THREE.LinearFilter,
        magFilter: THREE.LinearFilter,
        generateMipmaps: false,
        colorSpace: THREE.SRGBColorSpace,
      }
    );

    this.setTexture(texture);
  }

  /**
   * Update mesh size based on image dimensions and fit mode
   */
  private updateMeshSize(): void {
    // Dispose old geometry
    this.geometry.dispose();

    // Calculate final dimensions based on fit mode
    // Validate dimensions (guard against 0/NaN from upstream)
    let finalWidth = (Number.isFinite(this.imageWidth) && this.imageWidth > 0) ? this.imageWidth : 100;
    let finalHeight = (Number.isFinite(this.imageHeight) && this.imageHeight > 0) ? this.imageHeight : 100;

    // Only apply fit if we have valid target dimensions and fit is not 'none'
    const validTargetWidth = this.targetWidth && Number.isFinite(this.targetWidth) && this.targetWidth > 0;
    const validTargetHeight = this.targetHeight && Number.isFinite(this.targetHeight) && this.targetHeight > 0;
    if (validTargetWidth && validTargetHeight && this.fit !== 'none') {
      const targetAspect = this.targetWidth! / this.targetHeight!;
      const imageAspect = finalWidth / finalHeight;

      switch (this.fit) {
        case 'contain':
          // Scale to fit within target bounds, preserving aspect ratio
          if (imageAspect > targetAspect) {
            // Image is wider than target - fit to width
            finalWidth = this.targetWidth;
            finalHeight = this.targetWidth / imageAspect;
          } else {
            // Image is taller than target - fit to height
            finalHeight = this.targetHeight;
            finalWidth = this.targetHeight * imageAspect;
          }
          break;

        case 'cover':
          // Scale to cover target bounds, preserving aspect ratio (may crop)
          if (imageAspect > targetAspect) {
            // Image is wider than target - fit to height, crop width
            finalHeight = this.targetHeight;
            finalWidth = this.targetHeight * imageAspect;
          } else {
            // Image is taller than target - fit to width, crop height
            finalWidth = this.targetWidth;
            finalHeight = this.targetWidth / imageAspect;
          }
          break;

        case 'fill':
          // Stretch to fill target bounds exactly (ignores aspect ratio)
          finalWidth = this.targetWidth;
          finalHeight = this.targetHeight;
          break;
      }
    }

    // Create new geometry with calculated dimensions
    this.geometry = new THREE.PlaneGeometry(finalWidth, finalHeight);
    this.mesh.geometry = this.geometry;
  }

  // ============================================================================
  // PROPERTIES
  // ============================================================================

  /**
   * Get image dimensions
   */
  getDimensions(): { width: number; height: number } {
    return {
      width: this.imageWidth,
      height: this.imageHeight,
    };
  }

  /**
   * Set dimensions (stretches the image)
   */
  setDimensions(width: number, height: number): void {
    // Validate dimensions (NaN/0 would corrupt geometry and cause division by zero)
    this.imageWidth = (Number.isFinite(width) && width > 0) ? width : 100;
    this.imageHeight = (Number.isFinite(height) && height > 0) ? height : 100;
    this.updateMeshSize();
  }

  /**
   * Get source URL
   */
  getSource(): string | null {
    return this.sourceUrl;
  }

  /**
   * Set tint color
   */
  setTint(color: string | number): void {
    this.material.color.set(color);
    this.material.needsUpdate = true;
  }

  /**
   * Clear tint (reset to white)
   */
  clearTint(): void {
    this.material.color.set(0xffffff);
    this.material.needsUpdate = true;
  }

  // ============================================================================
  // EFFECTS SUPPORT
  // ============================================================================

  /**
   * Get source canvas for effect processing
   * Renders the original texture to a 2D canvas
   */
  protected override getSourceCanvas(): HTMLCanvasElement | null {
    if (!this.originalTexture?.image) {
      return null;
    }

    const image = this.originalTexture.image as HTMLImageElement | HTMLCanvasElement | ImageBitmap;

    // Lazy create/resize canvas
    if (!this.textureCanvas ||
        this.textureCanvas.width !== this.imageWidth ||
        this.textureCanvas.height !== this.imageHeight) {
      this.textureCanvas = document.createElement('canvas');
      this.textureCanvas.width = this.imageWidth;
      this.textureCanvas.height = this.imageHeight;
      this.textureCanvasCtx = this.textureCanvas.getContext('2d');
    }

    if (!this.textureCanvasCtx) {
      return null;
    }

    // Draw original image to canvas
    this.textureCanvasCtx.clearRect(0, 0, this.imageWidth, this.imageHeight);
    this.textureCanvasCtx.drawImage(image, 0, 0, this.imageWidth, this.imageHeight);

    return this.textureCanvas;
  }

  /**
   * Apply processed effects canvas back to the material
   */
  protected override applyProcessedEffects(processedCanvas: HTMLCanvasElement): void {
    // Create a new texture from the processed canvas
    const processedTexture = this.resources.createTextureFromCanvas(
      processedCanvas,
      `layer_${this.id}_effects`,
      {
        minFilter: THREE.LinearFilter,
        magFilter: THREE.LinearFilter,
        generateMipmaps: false,
        colorSpace: THREE.SRGBColorSpace,
      }
    );

    // Apply to material (keep original texture reference intact)
    this.texture = processedTexture;
    this.material.map = processedTexture;
    this.material.needsUpdate = true;
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Process effects if any are enabled
    this.evaluateEffects(frame);
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    // Apply tint if present in evaluated properties
    if (state.properties['tint'] !== undefined) {
      this.setTint(state.properties['tint'] as string | number);
    }

    // Process effects using evaluated effect parameters
    if (state.effects.length > 0) {
      this.applyEvaluatedEffects(state.effects);
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as any;
    let needsResize = false;

    // Handle source change
    if (data?.source || data?.url || data?.assetId) {
      const newSource = data.source ?? data.url ?? data.assetId;
      if (newSource !== this.sourceUrl) {
        this.loadImage(newSource);
      }
    }

    // Handle fit mode change
    if (data?.fit !== undefined && data.fit !== this.fit) {
      this.fit = data.fit;
      needsResize = true;
    }

    // Handle target dimension change (for fit calculations)
    if (data?.width !== undefined || data?.height !== undefined) {
      this.targetWidth = data.width ?? this.targetWidth;
      this.targetHeight = data.height ?? this.targetHeight;
      needsResize = true;
    }

    // Recalculate mesh size if fit or target changed
    if (needsResize) {
      this.updateMeshSize();
    }
  }

  protected onDispose(): void {
    this.geometry.dispose();
    this.material.dispose();

    // Note: texture disposal is handled by ResourceManager
    // unless it was created directly
  }
}
