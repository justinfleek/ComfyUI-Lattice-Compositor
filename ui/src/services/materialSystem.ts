/**
 * Material System - PBR Material Management
 *
 * Provides comprehensive material support for the 3D compositor:
 * - PBR material creation with full texture map support
 * - Environment map (HDRI) management
 * - Material presets and library
 * - Real-time material editing
 * - Material export for external renderers
 *
 * Texture Maps Supported:
 * - Albedo (base color / diffuse)
 * - Normal (tangent space)
 * - Roughness
 * - Metalness
 * - Ambient Occlusion (AO)
 * - Emissive
 * - Height/Displacement
 * - Opacity/Alpha
 */

import * as THREE from "three";
import { EXRLoader } from "three/examples/jsm/loaders/EXRLoader.js";
import { RGBELoader } from "three/examples/jsm/loaders/RGBELoader.js";
import type { AssetReference, TextureMapType } from "@/types/project";

// ============================================================================
// TYPES
// ============================================================================

/** PBR Material definition */
export interface PBRMaterialConfig {
  id: string;
  name: string;

  // Base properties
  color: string;
  opacity: number;
  transparent: boolean;

  // PBR properties
  metalness: number;
  roughness: number;
  envMapIntensity: number;

  // Emissive
  emissive: string;
  emissiveIntensity: number;

  // Normal
  normalScale: number;

  // Displacement
  displacementScale: number;
  displacementBias: number;

  // AO
  aoMapIntensity: number;

  // Texture map asset IDs
  maps: {
    albedo?: string;
    normal?: string;
    roughness?: string;
    metalness?: string;
    ao?: string;
    emissive?: string;
    height?: string;
    opacity?: string;
  };

  // Texture settings
  textureRepeat: { x: number; y: number };
  textureOffset: { x: number; y: number };
  textureRotation: number;

  // Rendering options
  side: "front" | "back" | "double";
  flatShading: boolean;
  wireframe: boolean;
  depthWrite: boolean;
  depthTest: boolean;
}

/** Environment map configuration */
export interface EnvironmentConfig {
  enabled: boolean;
  assetId?: string; // HDRI asset ID
  intensity: number; // Environment intensity
  rotation: number; // Y-axis rotation (degrees)
  backgroundBlur: number; // Background blur amount (0-1)
  useAsBackground: boolean; // Show HDRI as scene background
}

/** Material preset definition */
export interface MaterialPreset {
  id: string;
  name: string;
  category: string;
  thumbnail?: string;
  config: Partial<PBRMaterialConfig>;
}

// ============================================================================
// MATERIAL SYSTEM
// ============================================================================

export class MaterialSystem {
  /** Texture cache */
  private textureCache: Map<string, THREE.Texture> = new Map();

  /** Material cache */
  private materialCache: Map<string, THREE.MeshStandardMaterial> = new Map();

  /** Current environment map */
  private envMap: THREE.Texture | null = null;

  /** Environment configuration */
  private envConfig: EnvironmentConfig = {
    enabled: false,
    intensity: 1,
    rotation: 0,
    backgroundBlur: 0,
    useAsBackground: true,
  };

  /** HDRI loader */
  private rgbeLoader: RGBELoader;
  private exrLoader: EXRLoader;

  /** Texture loader */
  private textureLoader: THREE.TextureLoader;

  /** PMREMGenerator for environment maps */
  private pmremGenerator: THREE.PMREMGenerator | null = null;

  /** Asset getter callback */
  private assetGetter?: (assetId: string) => AssetReference | undefined;

  constructor() {
    this.rgbeLoader = new RGBELoader();
    this.exrLoader = new EXRLoader();
    this.textureLoader = new THREE.TextureLoader();
  }

  /**
   * Initialize with WebGL renderer (required for PMREM)
   */
  initialize(renderer: THREE.WebGLRenderer): void {
    this.pmremGenerator = new THREE.PMREMGenerator(renderer);
    this.pmremGenerator.compileEquirectangularShader();
  }

  /**
   * Set asset getter callback
   */
  setAssetGetter(
    getter: (assetId: string) => AssetReference | undefined,
  ): void {
    this.assetGetter = getter;
  }

  // ============================================================================
  // TEXTURE LOADING
  // ============================================================================

  /**
   * Load a texture from URL or asset ID
   */
  async loadTexture(
    urlOrAssetId: string,
    mapType: TextureMapType,
    options?: {
      repeat?: { x: number; y: number };
      offset?: { x: number; y: number };
      rotation?: number;
    },
  ): Promise<THREE.Texture> {
    // Check cache
    const cacheKey = `${urlOrAssetId}:${mapType}`;
    const cached = this.textureCache.get(cacheKey);
    if (cached) return cached;

    // Resolve URL from asset ID if needed
    let url = urlOrAssetId;
    if (this.assetGetter) {
      const asset = this.assetGetter(urlOrAssetId);
      if (asset?.data) {
        url = asset.data;
      }
    }

    return new Promise((resolve, reject) => {
      this.textureLoader.load(
        url,
        (texture) => {
          // Configure based on map type
          this.configureTextureForMapType(texture, mapType);

          // Apply options
          if (options?.repeat) {
            texture.repeat.set(options.repeat.x, options.repeat.y);
            texture.wrapS = THREE.RepeatWrapping;
            texture.wrapT = THREE.RepeatWrapping;
          }
          if (options?.offset) {
            texture.offset.set(options.offset.x, options.offset.y);
          }
          if (options?.rotation !== undefined) {
            texture.rotation = options.rotation * (Math.PI / 180);
          }

          this.textureCache.set(cacheKey, texture);
          resolve(texture);
        },
        undefined,
        reject,
      );
    });
  }

  /**
   * Configure texture settings based on map type
   */
  private configureTextureForMapType(
    texture: THREE.Texture,
    mapType: TextureMapType,
  ): void {
    // Default settings
    texture.generateMipmaps = true;
    texture.minFilter = THREE.LinearMipmapLinearFilter;
    texture.magFilter = THREE.LinearFilter;

    switch (mapType) {
      case "albedo":
      case "emissive":
        // sRGB color space for color maps
        texture.colorSpace = THREE.SRGBColorSpace;
        break;

      case "normal":
      case "roughness":
      case "metalness":
      case "ao":
      case "height":
      case "opacity":
      case "specular":
        // Linear color space for data maps
        texture.colorSpace = THREE.LinearSRGBColorSpace;
        break;
    }
  }

  // ============================================================================
  // PBR MATERIAL CREATION
  // ============================================================================

  /**
   * Create a PBR material from configuration
   */
  async createPBRMaterial(
    config: PBRMaterialConfig,
  ): Promise<THREE.MeshStandardMaterial> {
    // Check cache
    const cached = this.materialCache.get(config.id);
    if (cached) return cached;

    const material = new THREE.MeshStandardMaterial({
      color: new THREE.Color(config.color),
      metalness: config.metalness,
      roughness: config.roughness,
      transparent: config.transparent,
      opacity: config.opacity,
      emissive: new THREE.Color(config.emissive),
      emissiveIntensity: config.emissiveIntensity,
      envMapIntensity: config.envMapIntensity,
      normalScale: new THREE.Vector2(config.normalScale, config.normalScale),
      displacementScale: config.displacementScale,
      displacementBias: config.displacementBias,
      aoMapIntensity: config.aoMapIntensity,
      flatShading: config.flatShading,
      wireframe: config.wireframe,
      depthWrite: config.depthWrite,
      depthTest: config.depthTest,
      side: this.getSide(config.side),
    });

    // Load texture maps
    const texturePromises: Promise<void>[] = [];

    if (config.maps.albedo) {
      texturePromises.push(
        this.loadTexture(config.maps.albedo, "albedo", {
          repeat: config.textureRepeat,
          offset: config.textureOffset,
          rotation: config.textureRotation,
        }).then((tex) => {
          material.map = tex;
        }),
      );
    }

    if (config.maps.normal) {
      texturePromises.push(
        this.loadTexture(config.maps.normal, "normal", {
          repeat: config.textureRepeat,
          offset: config.textureOffset,
          rotation: config.textureRotation,
        }).then((tex) => {
          material.normalMap = tex;
        }),
      );
    }

    if (config.maps.roughness) {
      texturePromises.push(
        this.loadTexture(config.maps.roughness, "roughness", {
          repeat: config.textureRepeat,
          offset: config.textureOffset,
          rotation: config.textureRotation,
        }).then((tex) => {
          material.roughnessMap = tex;
        }),
      );
    }

    if (config.maps.metalness) {
      texturePromises.push(
        this.loadTexture(config.maps.metalness, "metalness", {
          repeat: config.textureRepeat,
          offset: config.textureOffset,
          rotation: config.textureRotation,
        }).then((tex) => {
          material.metalnessMap = tex;
        }),
      );
    }

    if (config.maps.ao) {
      texturePromises.push(
        this.loadTexture(config.maps.ao, "ao", {
          repeat: config.textureRepeat,
          offset: config.textureOffset,
          rotation: config.textureRotation,
        }).then((tex) => {
          material.aoMap = tex;
        }),
      );
    }

    if (config.maps.emissive) {
      texturePromises.push(
        this.loadTexture(config.maps.emissive, "emissive", {
          repeat: config.textureRepeat,
          offset: config.textureOffset,
          rotation: config.textureRotation,
        }).then((tex) => {
          material.emissiveMap = tex;
        }),
      );
    }

    if (config.maps.height) {
      texturePromises.push(
        this.loadTexture(config.maps.height, "height", {
          repeat: config.textureRepeat,
          offset: config.textureOffset,
          rotation: config.textureRotation,
        }).then((tex) => {
          material.displacementMap = tex;
        }),
      );
    }

    if (config.maps.opacity) {
      texturePromises.push(
        this.loadTexture(config.maps.opacity, "opacity", {
          repeat: config.textureRepeat,
          offset: config.textureOffset,
          rotation: config.textureRotation,
        }).then((tex) => {
          material.alphaMap = tex;
          material.transparent = true;
        }),
      );
    }

    // Apply environment map if available
    if (this.envMap && this.envConfig.enabled) {
      material.envMap = this.envMap;
    }

    await Promise.all(texturePromises);

    material.needsUpdate = true;
    this.materialCache.set(config.id, material);

    return material;
  }

  /**
   * Get THREE.Side from string
   */
  private getSide(side: "front" | "back" | "double"): THREE.Side {
    switch (side) {
      case "front":
        return THREE.FrontSide;
      case "back":
        return THREE.BackSide;
      case "double":
        return THREE.DoubleSide;
    }
  }

  /**
   * Create default PBR material config
   */
  static createDefaultConfig(id: string, name: string): PBRMaterialConfig {
    return {
      id,
      name,
      color: "#ffffff",
      opacity: 1,
      transparent: false,
      metalness: 0,
      roughness: 0.5,
      envMapIntensity: 1,
      emissive: "#000000",
      emissiveIntensity: 1,
      normalScale: 1,
      displacementScale: 0,
      displacementBias: 0,
      aoMapIntensity: 1,
      maps: {},
      textureRepeat: { x: 1, y: 1 },
      textureOffset: { x: 0, y: 0 },
      textureRotation: 0,
      side: "double",
      flatShading: false,
      wireframe: false,
      depthWrite: true,
      depthTest: true,
    };
  }

  // ============================================================================
  // ENVIRONMENT MAPS (HDRI)
  // ============================================================================

  /**
   * Load an environment map (HDR/EXR)
   */
  async loadEnvironmentMap(urlOrAssetId: string): Promise<THREE.Texture> {
    if (!this.pmremGenerator) {
      throw new Error(
        "MaterialSystem not initialized. Call initialize() with renderer first.",
      );
    }

    // Resolve URL from asset ID if needed
    let url = urlOrAssetId;
    if (this.assetGetter) {
      const asset = this.assetGetter(urlOrAssetId);
      if (asset?.data) {
        url = asset.data;
      }
    }

    // Determine loader based on file extension
    const isEXR = url.toLowerCase().endsWith(".exr");
    const loader = isEXR ? this.exrLoader : this.rgbeLoader;

    return new Promise((resolve, reject) => {
      loader.load(
        url,
        (texture) => {
          // Generate PMREM from equirectangular HDR
          const envMap =
            this.pmremGenerator?.fromEquirectangular(texture).texture;
          texture.dispose();

          this.envMap = envMap;
          this.envConfig.enabled = true;

          // Update all cached materials with new env map
          this.updateMaterialsEnvMap();

          resolve(envMap);
        },
        undefined,
        reject,
      );
    });
  }

  /**
   * Set environment configuration
   */
  setEnvironmentConfig(config: Partial<EnvironmentConfig>): void {
    Object.assign(this.envConfig, config);

    // Update material env map intensity
    if (config.intensity !== undefined) {
      for (const material of this.materialCache.values()) {
        material.envMapIntensity = config.intensity;
      }
    }
  }

  /**
   * Get current environment map for scene background
   */
  getEnvironmentMap(): THREE.Texture | null {
    return this.envMap;
  }

  /**
   * Get environment config
   */
  getEnvironmentConfig(): EnvironmentConfig {
    return { ...this.envConfig };
  }

  /**
   * Update all materials with current environment map
   */
  private updateMaterialsEnvMap(): void {
    for (const material of this.materialCache.values()) {
      material.envMap = this.envConfig.enabled ? this.envMap : null;
      material.envMapIntensity = this.envConfig.intensity;
      material.needsUpdate = true;
    }
  }

  // ============================================================================
  // MATERIAL PRESETS
  // ============================================================================

  /**
   * Get built-in material presets
   */
  static getPresets(): MaterialPreset[] {
    return [
      // Metals
      {
        id: "chrome",
        name: "Chrome",
        category: "Metal",
        config: {
          color: "#ffffff",
          metalness: 1,
          roughness: 0.05,
          envMapIntensity: 1.5,
        },
      },
      {
        id: "brushed_steel",
        name: "Brushed Steel",
        category: "Metal",
        config: {
          color: "#c0c0c0",
          metalness: 1,
          roughness: 0.4,
        },
      },
      {
        id: "gold",
        name: "Gold",
        category: "Metal",
        config: {
          color: "#ffd700",
          metalness: 1,
          roughness: 0.2,
        },
      },
      {
        id: "copper",
        name: "Copper",
        category: "Metal",
        config: {
          color: "#b87333",
          metalness: 1,
          roughness: 0.3,
        },
      },

      // Plastics
      {
        id: "glossy_plastic",
        name: "Glossy Plastic",
        category: "Plastic",
        config: {
          color: "#ff0000",
          metalness: 0,
          roughness: 0.1,
        },
      },
      {
        id: "matte_plastic",
        name: "Matte Plastic",
        category: "Plastic",
        config: {
          color: "#ffffff",
          metalness: 0,
          roughness: 0.8,
        },
      },

      // Glass
      {
        id: "clear_glass",
        name: "Clear Glass",
        category: "Glass",
        config: {
          color: "#ffffff",
          metalness: 0,
          roughness: 0,
          opacity: 0.2,
          transparent: true,
          envMapIntensity: 2,
        },
      },
      {
        id: "frosted_glass",
        name: "Frosted Glass",
        category: "Glass",
        config: {
          color: "#ffffff",
          metalness: 0,
          roughness: 0.5,
          opacity: 0.5,
          transparent: true,
        },
      },

      // Natural
      {
        id: "clay",
        name: "Clay",
        category: "Natural",
        config: {
          color: "#d4a574",
          metalness: 0,
          roughness: 0.9,
        },
      },
      {
        id: "stone",
        name: "Stone",
        category: "Natural",
        config: {
          color: "#808080",
          metalness: 0,
          roughness: 0.7,
        },
      },

      // Emissive
      {
        id: "neon_glow",
        name: "Neon Glow",
        category: "Emissive",
        config: {
          color: "#000000",
          emissive: "#00ffff",
          emissiveIntensity: 2,
          metalness: 0,
          roughness: 0.5,
        },
      },
      {
        id: "hot_metal",
        name: "Hot Metal",
        category: "Emissive",
        config: {
          color: "#ff4400",
          emissive: "#ff2200",
          emissiveIntensity: 1,
          metalness: 0.8,
          roughness: 0.4,
        },
      },
    ];
  }

  /**
   * Create material from preset
   */
  async createFromPreset(
    presetId: string,
    materialId: string,
    overrides?: Partial<PBRMaterialConfig>,
  ): Promise<THREE.MeshStandardMaterial> {
    const preset = MaterialSystem.getPresets().find((p) => p.id === presetId);
    if (!preset) {
      throw new Error(`Preset not found: ${presetId}`);
    }

    const config: PBRMaterialConfig = {
      ...MaterialSystem.createDefaultConfig(materialId, preset.name),
      ...preset.config,
      ...overrides,
      id: materialId,
    };

    return this.createPBRMaterial(config);
  }

  // ============================================================================
  // MATERIAL UPDATES
  // ============================================================================

  /**
   * Update an existing material's properties
   */
  updateMaterial(
    materialId: string,
    updates: Partial<PBRMaterialConfig>,
  ): void {
    const material = this.materialCache.get(materialId);
    if (!material) return;

    if (updates.color !== undefined) {
      material.color.set(updates.color);
    }
    if (updates.metalness !== undefined) {
      material.metalness = updates.metalness;
    }
    if (updates.roughness !== undefined) {
      material.roughness = updates.roughness;
    }
    if (updates.opacity !== undefined) {
      material.opacity = updates.opacity;
    }
    if (updates.transparent !== undefined) {
      material.transparent = updates.transparent;
    }
    if (updates.emissive !== undefined) {
      material.emissive.set(updates.emissive);
    }
    if (updates.emissiveIntensity !== undefined) {
      material.emissiveIntensity = updates.emissiveIntensity;
    }
    if (updates.envMapIntensity !== undefined) {
      material.envMapIntensity = updates.envMapIntensity;
    }
    if (updates.normalScale !== undefined) {
      material.normalScale.set(updates.normalScale, updates.normalScale);
    }
    if (updates.wireframe !== undefined) {
      material.wireframe = updates.wireframe;
    }
    if (updates.flatShading !== undefined) {
      material.flatShading = updates.flatShading;
    }
    if (updates.side !== undefined) {
      material.side = this.getSide(updates.side);
    }

    material.needsUpdate = true;
  }

  /**
   * Get a cached material
   */
  getMaterial(materialId: string): THREE.MeshStandardMaterial | undefined {
    return this.materialCache.get(materialId);
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  /**
   * Dispose a material
   */
  disposeMaterial(materialId: string): void {
    const material = this.materialCache.get(materialId);
    if (material) {
      material.dispose();
      this.materialCache.delete(materialId);
    }
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    // Dispose textures
    for (const texture of this.textureCache.values()) {
      texture.dispose();
    }
    this.textureCache.clear();

    // Dispose materials
    for (const material of this.materialCache.values()) {
      material.dispose();
    }
    this.materialCache.clear();

    // Dispose environment map
    if (this.envMap) {
      this.envMap.dispose();
      this.envMap = null;
    }

    // Dispose PMREM generator
    if (this.pmremGenerator) {
      this.pmremGenerator.dispose();
      this.pmremGenerator = null;
    }
  }
}

// Export singleton instance
export const materialSystem = new MaterialSystem();
