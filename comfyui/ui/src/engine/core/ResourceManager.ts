/**
 * ResourceManager - Texture and Geometry Resource Management
 *
 * Handles caching, pooling, and disposal of shared resources:
 * - Textures (images, videos, render targets)
 * - Geometries (reusable primitives)
 * - Materials (shared materials)
 */

import * as THREE from "three";
import { validateURL } from "@/services/security/urlValidator";
import type { AssetReference } from "@/types/project";
import { renderLogger } from "@/utils/logger";

export interface TextureOptions {
  wrapS?: THREE.Wrapping;
  wrapT?: THREE.Wrapping;
  minFilter?: THREE.TextureFilter;
  magFilter?: THREE.MagnificationTextureFilter;
  generateMipmaps?: boolean;
  flipY?: boolean;
  colorSpace?: THREE.ColorSpace;
}

/** Callback to retrieve assets from the store */
export type AssetGetter = (assetId: string) => AssetReference | undefined;

export class ResourceManager {
  // Texture cache (keyed by URL or ID)
  private readonly textures: Map<string, THREE.Texture>;

  // Geometry cache (keyed by type and parameters)
  private readonly geometries: Map<string, THREE.BufferGeometry>;

  // Material cache (keyed by configuration hash)
  private readonly materials: Map<string, THREE.Material>;

  // Texture loader
  private readonly textureLoader: THREE.TextureLoader;

  // Asset getter callback (set by LatticeEngine)
  private assetGetter?: AssetGetter;

  // Statistics
  private stats = {
    texturesLoaded: 0,
    texturesFromCache: 0,
    geometriesCreated: 0,
    geometriesFromCache: 0,
  };

  constructor() {
    this.textures = new Map();
    this.geometries = new Map();
    this.materials = new Map();
    this.textureLoader = new THREE.TextureLoader();

    // Pre-create common geometries
    this.initializeCommonGeometries();
  }

  // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  //                                                          // asset // access
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Set the asset getter callback
   * Called by LatticeEngine to provide access to project assets
   */
  setAssetGetter(getter: AssetGetter): void {
    this.assetGetter = getter;
  }

  /**
   * Get an asset reference by ID
   * 
   * System F/Omega proof: Explicit validation of asset getter and asset existence
   * Type proof: assetId ∈ string → AssetReference (non-nullable)
   * Mathematical proof: Asset getter must be set and asset must exist to retrieve reference
   * Pattern proof: Missing getter or asset is an explicit failure condition, not a lazy undefined return
   */
  getAsset(assetId: string): AssetReference {
    // System F/Omega proof: Explicit validation of asset getter
    // Type proof: assetGetter ∈ AssetGetter | undefined
    // Mathematical proof: Asset getter must be set to retrieve assets
    if (this.assetGetter === undefined || typeof this.assetGetter !== "function") {
      throw new Error(
        `[ResourceManager] Cannot get asset: Asset getter not set. ` +
        `Asset ID: ${assetId}. ` +
        `ResourceManager must have an asset getter configured before retrieving assets. ` +
        `Wrap in try/catch if "asset not found" is an expected state.`
      );
    }

    const asset = this.assetGetter(assetId);
    
    // System F/Omega proof: Explicit validation of asset existence
    // Type proof: assetGetter returns AssetReference | undefined
    // Mathematical proof: Asset must exist to retrieve reference
    if (asset === undefined) {
      throw new Error(
        `[ResourceManager] Cannot get asset: Asset not found. ` +
        `Asset ID: ${assetId}. ` +
        `Asset does not exist in the asset store. ` +
        `Wrap in try/catch if "asset not found" is an expected state.`
      );
    }

    return asset;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                           // initialization
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Pre-create commonly used geometries
   */
  private initializeCommonGeometries(): void {
    // Unit plane (1x1, can be scaled)
    const plane = new THREE.PlaneGeometry(1, 1, 1, 1);
    this.geometries.set("plane:1:1", plane);

    // Unit quad for full-screen effects
    const quad = new THREE.PlaneGeometry(2, 2, 1, 1);
    this.geometries.set("quad:fullscreen", quad);
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                    // texture // management
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Load a texture from URL
   * SECURITY: Validates URL protocol before loading to prevent XSS and code injection
   */
  async loadTexture(
    url: string,
    options?: TextureOptions,
  ): Promise<THREE.Texture> {
    // SECURITY: Validate URL before loading
    const urlValidation = validateURL(url, "asset");
    if (!urlValidation.valid) {
      const error = new Error(
        `[SECURITY] Blocked texture load: ${urlValidation.error}`,
      );
      renderLogger.error("ResourceManager:", error.message, "URL:", url);
      return Promise.reject(error);
    }

    // Log security warnings (e.g., HTTP without TLS)
    if (urlValidation.warning) {
      renderLogger.warn(
        "ResourceManager: Security warning for URL:",
        url,
        "-",
        urlValidation.warning,
      );
    }

    // Use sanitized URL (or original if sanitized is null for valid URLs)
    const safeUrl = urlValidation.sanitized || url;

    // Check cache first
    const cacheKey = this.getTextureCacheKey(safeUrl, options);
    const cached = this.textures.get(cacheKey);

    if (cached) {
      this.stats.texturesFromCache++;
      return cached;
    }

    // Load new texture
    return new Promise((resolve, reject) => {
      this.textureLoader.load(
        safeUrl,
        (texture) => {
          this.applyTextureOptions(texture, options);
          this.textures.set(cacheKey, texture);
          this.stats.texturesLoaded++;
          resolve(texture);
        },
        undefined, // Progress callback
        (error) => {
          renderLogger.error(
            "ResourceManager: Failed to load texture:",
            safeUrl,
            error,
          );
          reject(error);
        },
      );
    });
  }

  /**
   * Create texture from ImageData
   */
  createTextureFromImageData(
    imageData: ImageData,
    id: string,
    options?: TextureOptions,
  ): THREE.DataTexture {
    // Check cache
    const cached = this.textures.get(id);
    if (cached instanceof THREE.DataTexture) {
      // Update existing texture data
      cached.image = imageData;
      cached.needsUpdate = true;
      return cached;
    }

    // Create new texture
    const texture = new THREE.DataTexture(
      imageData.data,
      imageData.width,
      imageData.height,
      THREE.RGBAFormat,
      THREE.UnsignedByteType,
    );

    this.applyTextureOptions(texture, options);
    texture.needsUpdate = true;

    this.textures.set(id, texture);
    this.stats.texturesLoaded++;

    return texture;
  }

  /**
   * Create texture from canvas
   */
  createTextureFromCanvas(
    canvas: HTMLCanvasElement | OffscreenCanvas,
    id: string,
    options?: TextureOptions,
  ): THREE.CanvasTexture {
    // Check cache
    const cached = this.textures.get(id);
    if (cached instanceof THREE.CanvasTexture) {
      // Update canvas reference before marking for upload (fixes stale texture bug)
      cached.image = canvas as HTMLCanvasElement;
      cached.needsUpdate = true;
      return cached;
    }

    // Create new texture
    const texture = new THREE.CanvasTexture(canvas as HTMLCanvasElement);
    this.applyTextureOptions(texture, options);

    this.textures.set(id, texture);
    this.stats.texturesLoaded++;

    return texture;
  }

  /**
   * Get a cached texture
   */
  getTexture(key: string): THREE.Texture | undefined {
    return this.textures.get(key);
  }

  /**
   * Apply options to a texture
   */
  private applyTextureOptions(
    texture: THREE.Texture,
    options?: TextureOptions,
  ): void {
    if (!options) {
      // Default options for crisp 2D graphics
      texture.minFilter = THREE.LinearFilter;
      texture.magFilter = THREE.LinearFilter;
      texture.generateMipmaps = false;
      texture.colorSpace = THREE.SRGBColorSpace;
      return;
    }

    if (options.wrapS !== undefined) texture.wrapS = options.wrapS;
    if (options.wrapT !== undefined) texture.wrapT = options.wrapT;
    if (options.minFilter !== undefined) texture.minFilter = options.minFilter;
    if (options.magFilter !== undefined) texture.magFilter = options.magFilter;
    if (options.generateMipmaps !== undefined)
      texture.generateMipmaps = options.generateMipmaps;
    if (options.flipY !== undefined) texture.flipY = options.flipY;
    if (options.colorSpace !== undefined)
      texture.colorSpace = options.colorSpace;
  }

  /**
   * Generate cache key for texture
   */
  private getTextureCacheKey(url: string, options?: TextureOptions): string {
    if (!options) return url;
    return `${url}:${JSON.stringify(options)}`;
  }

  /**
   * Release a texture
   */
  releaseTexture(key: string): void {
    const texture = this.textures.get(key);
    if (texture) {
      texture.dispose();
      this.textures.delete(key);
    }
  }

  /**
   * Get texture for a layer by its ID
   * Looks up the layer's asset and returns its texture if cached
   * 
   * System F/Omega proof: Explicit validation of texture cache
   * Type proof: layerId ∈ string → THREE.Texture (non-nullable)
   * Mathematical proof: Texture must be cached to retrieve it
   * Pattern proof: Missing texture is an explicit failure condition, not a lazy null return
   */
  getLayerTexture(layerId: string): THREE.Texture {
    // Check if we have a direct layer texture cached
    const layerKey = `layer:${layerId}`;
    const layerTexture = this.textures.get(layerKey);
    
    // System F/Omega proof: Explicit validation of texture existence
    // Type proof: textures.get() returns THREE.Texture | undefined
    // Mathematical proof: Texture must be cached to retrieve it
    if (layerTexture === undefined) {
      throw new Error(
        `[ResourceManager] Cannot get layer texture: Texture not cached. ` +
        `Layer ID: ${layerId}, cache key: ${layerKey}. ` +
        `Texture must be cached before retrieval. ` +
        `This would need to be wired up with LayerManager to access layer assets. ` +
        `Wrap in try/catch if "texture not cached" is an expected state.`
      );
    }

    return layerTexture;
  }

  /**
   * Cache a texture for a layer
   */
  setLayerTexture(layerId: string, texture: THREE.Texture): void {
    const key = `layer:${layerId}`;
    this.textures.set(key, texture);
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                   // geometry // management
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Get a plane geometry (cached)
   */
  getPlaneGeometry(width: number = 1, height: number = 1): THREE.PlaneGeometry {
    const key = `plane:${width}:${height}`;

    let geometry = this.geometries.get(key) as THREE.PlaneGeometry;
    if (geometry) {
      this.stats.geometriesFromCache++;
      return geometry;
    }

    geometry = new THREE.PlaneGeometry(width, height, 1, 1);
    this.geometries.set(key, geometry);
    this.stats.geometriesCreated++;

    return geometry;
  }

  /**
   * Get a circle geometry (cached)
   */
  getCircleGeometry(
    radius: number = 1,
    segments: number = 32,
  ): THREE.CircleGeometry {
    const key = `circle:${radius}:${segments}`;

    let geometry = this.geometries.get(key) as THREE.CircleGeometry;
    if (geometry) {
      this.stats.geometriesFromCache++;
      return geometry;
    }

    geometry = new THREE.CircleGeometry(radius, segments);
    this.geometries.set(key, geometry);
    this.stats.geometriesCreated++;

    return geometry;
  }

  /**
   * Get a box geometry (cached)
   */
  getBoxGeometry(
    width: number = 1,
    height: number = 1,
    depth: number = 1,
  ): THREE.BoxGeometry {
    const key = `box:${width}:${height}:${depth}`;

    let geometry = this.geometries.get(key) as THREE.BoxGeometry;
    if (geometry) {
      this.stats.geometriesFromCache++;
      return geometry;
    }

    geometry = new THREE.BoxGeometry(width, height, depth);
    this.geometries.set(key, geometry);
    this.stats.geometriesCreated++;

    return geometry;
  }

  /**
   * Get the fullscreen quad geometry
   */
  getFullscreenQuad(): THREE.PlaneGeometry {
    return this.geometries.get("quad:fullscreen") as THREE.PlaneGeometry;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                   // material // management
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Get or create a basic material
   */
  getBasicMaterial(options: {
    color?: number | string;
    transparent?: boolean;
    opacity?: number;
    map?: THREE.Texture;
    side?: THREE.Side;
  }): THREE.MeshBasicMaterial {
    const key = `basic:${JSON.stringify(options)}`;

    let material = this.materials.get(key) as THREE.MeshBasicMaterial;
    if (material) {
      return material;
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching on optional properties
    // Type proof: options.color ∈ number | undefined → number (color hex value)
    const colorValue: number = options.color !== undefined && typeof options.color === "number" && Number.isFinite(options.color)
      ? options.color
      : 0xffffff;
    // Type proof: options.transparent ∈ boolean | undefined → boolean
    const transparentValue: boolean = options.transparent !== undefined ? options.transparent : true;
    // Type proof: options.opacity ∈ number | undefined → number (0-1, opacity)
    const opacityValue: number = options.opacity !== undefined && Number.isFinite(options.opacity) && options.opacity >= 0 && options.opacity <= 1
      ? options.opacity
      : 1;
    // Type proof: options.side ∈ THREE.Side | undefined → THREE.Side
    const sideValue: THREE.Side = options.side !== undefined ? options.side : THREE.DoubleSide;
    
    material = new THREE.MeshBasicMaterial({
      color: colorValue,
      transparent: transparentValue,
      opacity: opacityValue,
      map: options.map,
      side: sideValue,
    });

    this.materials.set(key, material);
    return material;
  }

  /**
   * Create a non-cached material (for layers with unique properties)
   */
  createMaterial(type: "basic" | "standard" | "shader"): THREE.Material {
    switch (type) {
      case "basic":
        return new THREE.MeshBasicMaterial({
          transparent: true,
          side: THREE.DoubleSide,
        });

      case "standard":
        return new THREE.MeshStandardMaterial({
          transparent: true,
          side: THREE.DoubleSide,
        });

      case "shader":
        return new THREE.ShaderMaterial();

      default:
        return new THREE.MeshBasicMaterial();
    }
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                               // statistics
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Get resource statistics
   */
  getStats(): {
    textureCount: number;
    geometryCount: number;
    materialCount: number;
    texturesLoaded: number;
    texturesFromCache: number;
    geometriesCreated: number;
    geometriesFromCache: number;
  } {
    return {
      textureCount: this.textures.size,
      geometryCount: this.geometries.size,
      materialCount: this.materials.size,
      ...this.stats,
    };
  }

  /**
   * Reset statistics
   */
  resetStats(): void {
    this.stats = {
      texturesLoaded: 0,
      texturesFromCache: 0,
      geometriesCreated: 0,
      geometriesFromCache: 0,
    };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                                 // disposal
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Dispose all cached resources
   */
  dispose(): void {
    // Dispose textures
    for (const texture of this.textures.values()) {
      texture.dispose();
    }
    this.textures.clear();

    // Dispose geometries
    for (const geometry of this.geometries.values()) {
      geometry.dispose();
    }
    this.geometries.clear();

    // Dispose materials
    for (const material of this.materials.values()) {
      material.dispose();
    }
    this.materials.clear();
  }

  /**
   * Clear unused resources (call periodically)
   */
  clearUnused(): void {
    // This is a simplified implementation
    // A full implementation would track reference counts

    // For now, just log stats
    renderLogger.debug("ResourceManager: Resource stats:", this.getStats());
  }
}
