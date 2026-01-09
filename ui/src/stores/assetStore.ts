/**
 * Asset Store
 *
 * Manages 3D assets, materials, environment settings, and custom particles.
 * Provides reactive state for:
 * - PBR materials with texture maps
 * - SVG documents with extrusion configs
 * - Custom mesh particles
 * - Sprite sheet animations
 * - HDRI environment maps
 */

import { defineStore } from "pinia";
import * as THREE from "three";
import {
  materialSystem,
  type PBRMaterialConfig,
} from "@/services/materialSystem";
import {
  meshParticleManager,
  type RegisteredMeshParticle,
} from "@/services/meshParticleManager";
import {
  type ParticleSpriteConfig,
  type SpriteSheetConfig,
  spriteSheetService,
} from "@/services/spriteSheet";
import {
  loadAndValidateSprite,
  loadAndValidateSpritesheet,
  type SpritesheetValidationResult,
  type SpriteValidationIssue,
  type SpriteValidationResult,
} from "@/services/spriteValidation";
import {
  type ParsedSVGDocument,
  type SVGLayerConfig,
  svgExtrusionService,
} from "@/services/svgExtrusion";
import { storeLogger } from "@/utils/logger";
import { useToastStore } from "./toastStore";

// ============================================================================
// TYPES
// ============================================================================

/** Stored material with metadata */
export interface StoredMaterial {
  id: string;
  name: string;
  config: PBRMaterialConfig;
  presetName?: string;
  createdAt: number;
  modifiedAt: number;
}

/** Stored SVG document with extrusion settings */
export interface StoredSVGDocument {
  id: string;
  name: string;
  document: ParsedSVGDocument;
  layerConfigs: SVGLayerConfig[];
  createdAt: number;
}

/** Stored custom mesh for particles */
export interface StoredMeshParticle {
  id: string;
  name: string;
  registration: RegisteredMeshParticle;
  source: "svg" | "primitive" | "model" | "custom";
  sourceId?: string; // SVG path ID or model asset ID
}

/** Stored sprite sheet */
export interface StoredSpriteSheet {
  id: string;
  name: string;
  config: SpriteSheetConfig;
  textureUrl: string;
}

/** Environment configuration */
export interface EnvironmentState {
  enabled: boolean;
  url: string | null;
  intensity: number;
  rotation: number;
  backgroundBlur: number;
  useAsBackground: boolean;
  presetName?: string;
}

/** Import result for assets */
export interface AssetImportResult {
  success: boolean;
  assetId?: string;
  error?: string;
}

// ============================================================================
// STATE
// ============================================================================

interface AssetState {
  // Materials
  materials: Map<string, StoredMaterial>;
  selectedMaterialId: string | null;

  // SVG Documents
  svgDocuments: Map<string, StoredSVGDocument>;
  selectedSvgId: string | null;

  // Mesh Particles
  meshParticles: Map<string, StoredMeshParticle>;
  selectedMeshParticleId: string | null;

  // Sprite Sheets
  spriteSheets: Map<string, StoredSpriteSheet>;
  selectedSpriteSheetId: string | null;

  // Environment
  environment: EnvironmentState;
  environmentTexture: THREE.Texture | null;

  // Loading states
  isLoadingMaterial: boolean;
  isLoadingSvg: boolean;
  isLoadingMesh: boolean;
  isLoadingSpriteSheet: boolean;
  isLoadingEnvironment: boolean;

  // Error states
  lastError: string | null;
}

// ============================================================================
// STORE
// ============================================================================

export const useAssetStore = defineStore("assets", {
  state: (): AssetState => ({
    // Materials
    materials: new Map(),
    selectedMaterialId: null,

    // SVG Documents
    svgDocuments: new Map(),
    selectedSvgId: null,

    // Mesh Particles
    meshParticles: new Map(),
    selectedMeshParticleId: null,

    // Sprite Sheets
    spriteSheets: new Map(),
    selectedSpriteSheetId: null,

    // Environment
    environment: {
      enabled: false,
      url: null,
      intensity: 1.0,
      rotation: 0,
      backgroundBlur: 0,
      useAsBackground: true,
    },
    environmentTexture: null,

    // Loading states
    isLoadingMaterial: false,
    isLoadingSvg: false,
    isLoadingMesh: false,
    isLoadingSpriteSheet: false,
    isLoadingEnvironment: false,

    // Error states
    lastError: null,
  }),

  getters: {
    // Materials
    materialList: (state): StoredMaterial[] =>
      Array.from(state.materials.values()),
    selectedMaterial: (state): StoredMaterial | null =>
      state.selectedMaterialId
        ? (state.materials.get(state.selectedMaterialId) ?? null)
        : null,

    // SVG Documents
    svgDocumentList: (state): StoredSVGDocument[] =>
      Array.from(state.svgDocuments.values()),
    selectedSvgDocument: (state): StoredSVGDocument | null =>
      state.selectedSvgId
        ? (state.svgDocuments.get(state.selectedSvgId) ?? null)
        : null,

    // Mesh Particles
    meshParticleList: (state): StoredMeshParticle[] =>
      Array.from(state.meshParticles.values()),
    selectedMeshParticle: (state): StoredMeshParticle | null =>
      state.selectedMeshParticleId
        ? (state.meshParticles.get(state.selectedMeshParticleId) ?? null)
        : null,

    // Sprite Sheets
    spriteSheetList: (state): StoredSpriteSheet[] =>
      Array.from(state.spriteSheets.values()),
    selectedSpriteSheet: (state): StoredSpriteSheet | null =>
      state.selectedSpriteSheetId
        ? (state.spriteSheets.get(state.selectedSpriteSheetId) ?? null)
        : null,

    // Combined loading state
    isLoading: (state): boolean =>
      state.isLoadingMaterial ||
      state.isLoadingSvg ||
      state.isLoadingMesh ||
      state.isLoadingSpriteSheet ||
      state.isLoadingEnvironment,
  },

  actions: {
    // ========================================================================
    // MATERIALS
    // ========================================================================

    /**
     * Create a new material from preset
     */
    createMaterialFromPreset(presetName: string, customName?: string): string {
      const id = `mat_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

      // Get preset base config (these are partial configs)
      const presetConfigs: Record<string, Partial<PBRMaterialConfig>> = {
        chrome: { color: "#ffffff", metalness: 1, roughness: 0.1 },
        gold: { color: "#ffd700", metalness: 1, roughness: 0.2 },
        silver: { color: "#c0c0c0", metalness: 1, roughness: 0.15 },
        copper: { color: "#b87333", metalness: 1, roughness: 0.3 },
        brass: { color: "#b5a642", metalness: 0.9, roughness: 0.25 },
        glass: {
          color: "#ffffff",
          metalness: 0,
          roughness: 0.1,
          opacity: 0.3,
          transparent: true,
        },
        plastic: { color: "#ffffff", metalness: 0, roughness: 0.4 },
        rubber: { color: "#222222", metalness: 0, roughness: 0.9 },
        wood: { color: "#8b4513", metalness: 0, roughness: 0.7 },
        concrete: { color: "#808080", metalness: 0, roughness: 0.9 },
        emissive: {
          color: "#ffffff",
          emissive: "#00aaff",
          emissiveIntensity: 2,
        },
        holographic: {
          color: "#88ffff",
          metalness: 0.8,
          roughness: 0.2,
          emissive: "#ff00ff",
          emissiveIntensity: 0.5,
        },
      };

      const presetConfig = presetConfigs[presetName] || {};
      const config: PBRMaterialConfig = this.createDefaultMaterialConfig(
        id,
        customName || presetName,
        presetConfig,
      );

      const stored: StoredMaterial = {
        id,
        name: customName || presetName,
        config,
        presetName,
        createdAt: Date.now(),
        modifiedAt: Date.now(),
      };

      this.materials.set(id, stored);
      this.selectedMaterialId = id;

      storeLogger.debug("Created material from preset:", presetName, id);
      return id;
    },

    /**
     * Create a new empty material
     */
    createEmptyMaterial(name: string = "New Material"): string {
      const id = `mat_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
      const config = this.createDefaultMaterialConfig(id, name);

      const stored: StoredMaterial = {
        id,
        name,
        config,
        createdAt: Date.now(),
        modifiedAt: Date.now(),
      };

      this.materials.set(id, stored);
      this.selectedMaterialId = id;
      return id;
    },

    /**
     * Helper to create a full default material config
     */
    createDefaultMaterialConfig(
      id: string,
      name: string,
      overrides: Partial<PBRMaterialConfig> = {},
    ): PBRMaterialConfig {
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
        emissiveIntensity: 0,
        normalScale: 1,
        displacementScale: 0,
        displacementBias: 0,
        aoMapIntensity: 1,
        maps: {},
        textureRepeat: { x: 1, y: 1 },
        textureOffset: { x: 0, y: 0 },
        textureRotation: 0,
        side: "front",
        flatShading: false,
        wireframe: false,
        depthWrite: true,
        depthTest: true,
        ...overrides,
      };
    },

    /**
     * Update material configuration
     */
    updateMaterial(id: string, updates: Partial<PBRMaterialConfig>): void {
      const stored = this.materials.get(id);
      if (!stored) return;

      stored.config = { ...stored.config, ...updates };
      stored.modifiedAt = Date.now();
      this.materials.set(id, stored);
    },

    /**
     * Set texture for material
     */
    async setMaterialTexture(
      materialId: string,
      textureType: keyof PBRMaterialConfig,
      file: File,
    ): Promise<void> {
      const stored = this.materials.get(materialId);
      if (!stored) return;

      this.isLoadingMaterial = true;
      try {
        const url = URL.createObjectURL(file);
        (stored.config as any)[textureType] = url;
        stored.modifiedAt = Date.now();
        this.materials.set(materialId, stored);
      } catch (error) {
        this.lastError = `Failed to load texture: ${error}`;
      } finally {
        this.isLoadingMaterial = false;
      }
    },

    /**
     * Delete a material
     */
    deleteMaterial(id: string): void {
      this.materials.delete(id);
      if (this.selectedMaterialId === id) {
        this.selectedMaterialId = null;
      }
    },

    /**
     * Get Three.js material from stored config
     * Note: This creates a simple THREE.MeshStandardMaterial without async texture loading
     * For full PBR with textures, use materialSystem.createPBRMaterial()
     */
    getThreeMaterial(id: string): THREE.Material | null {
      const stored = this.materials.get(id);
      if (!stored) return null;

      const config = stored.config;
      const material = new THREE.MeshStandardMaterial({
        color: new THREE.Color(config.color),
        metalness: config.metalness,
        roughness: config.roughness,
        transparent: config.transparent,
        opacity: config.opacity,
        flatShading: config.flatShading,
        wireframe: config.wireframe,
        side:
          config.side === "double"
            ? THREE.DoubleSide
            : config.side === "back"
              ? THREE.BackSide
              : THREE.FrontSide,
      });

      if (config.emissive && config.emissive !== "#000000") {
        material.emissive = new THREE.Color(config.emissive);
        material.emissiveIntensity = config.emissiveIntensity;
      }

      return material;
    },

    // ========================================================================
    // SVG DOCUMENTS
    // ========================================================================

    /**
     * Import SVG from file
     */
    async importSvgFromFile(file: File): Promise<AssetImportResult> {
      this.isLoadingSvg = true;
      try {
        const text = await file.text();
        const name = file.name.replace(/\.svg$/i, "");
        const document = svgExtrusionService.loadFromString(text, name);

        // Generate default layer configs
        const layerConfigs = svgExtrusionService.generateAutoLayerConfigs(
          document,
          0, // baseDepth
          5, // depthIncrement between layers
          2, // extrusionDepth per layer
        );

        const id = document.id;
        const stored: StoredSVGDocument = {
          id,
          name,
          document,
          layerConfigs,
          createdAt: Date.now(),
        };

        this.svgDocuments.set(id, stored);
        this.selectedSvgId = id;

        storeLogger.debug(
          "Imported SVG:",
          name,
          `${document.paths.length} paths`,
        );
        return { success: true, assetId: id };
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        this.lastError = `SVG import failed: ${message}`;
        return { success: false, error: message };
      } finally {
        this.isLoadingSvg = false;
      }
    },

    /**
     * Import SVG from URL
     */
    async importSvgFromUrl(
      url: string,
      name?: string,
    ): Promise<AssetImportResult> {
      this.isLoadingSvg = true;
      try {
        const document = await svgExtrusionService.loadFromURL(url, name);

        const layerConfigs = svgExtrusionService.generateAutoLayerConfigs(
          document,
          0,
          5,
          2,
        );

        const id = document.id;
        const stored: StoredSVGDocument = {
          id,
          name: document.name,
          document,
          layerConfigs,
          createdAt: Date.now(),
        };

        this.svgDocuments.set(id, stored);
        this.selectedSvgId = id;

        return { success: true, assetId: id };
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        this.lastError = `SVG import failed: ${message}`;
        return { success: false, error: message };
      } finally {
        this.isLoadingSvg = false;
      }
    },

    /**
     * Update layer config for an SVG path
     */
    updateSvgLayerConfig(
      svgId: string,
      pathIndex: number,
      config: Partial<SVGLayerConfig>,
    ): void {
      const stored = this.svgDocuments.get(svgId);
      if (!stored || pathIndex >= stored.layerConfigs.length) return;

      stored.layerConfigs[pathIndex] = {
        ...stored.layerConfigs[pathIndex],
        ...config,
      };
      this.svgDocuments.set(svgId, stored);
    },

    /**
     * Get extruded geometries for all paths in an SVG
     */
    getExtrudedGeometries(svgId: string): THREE.BufferGeometry[] {
      const stored = this.svgDocuments.get(svgId);
      if (!stored) return [];

      return stored.document.paths.map((path, i) => {
        const config = stored.layerConfigs[i];
        return svgExtrusionService.createExtrudedGeometry(path, {
          depth: config.extrusionDepth,
        });
      });
    },

    /**
     * Create a Three.js Group with all extruded SVG paths
     */
    createExtrudedGroup(svgId: string): THREE.Group | null {
      const stored = this.svgDocuments.get(svgId);
      if (!stored) return null;

      return svgExtrusionService.createLayeredMeshes(
        stored.document,
        stored.layerConfigs,
      );
    },

    /**
     * Delete an SVG document
     */
    deleteSvgDocument(id: string): void {
      // Remove from local cache only (svgExtrusionService.clearCache() clears all)
      this.svgDocuments.delete(id);
      if (this.selectedSvgId === id) {
        this.selectedSvgId = null;
      }
    },

    // ========================================================================
    // MESH PARTICLES
    // ========================================================================

    /**
     * Register a primitive shape as mesh particle
     */
    registerPrimitiveMesh(
      type:
        | "cube"
        | "sphere"
        | "cone"
        | "cylinder"
        | "torus"
        | "tetrahedron"
        | "octahedron"
        | "icosahedron",
      name?: string,
      size: number = 1,
    ): string {
      const registration = meshParticleManager.registerPrimitive(
        type,
        name,
        size,
      );

      const stored: StoredMeshParticle = {
        id: registration.id,
        name: registration.name,
        registration,
        source: "primitive",
      };

      this.meshParticles.set(registration.id, stored);
      this.selectedMeshParticleId = registration.id;

      return registration.id;
    },

    /**
     * Register an SVG path as mesh particle
     */
    registerSvgPathAsMesh(
      svgId: string,
      pathIndex: number,
      name?: string,
      options?: { extrusionDepth?: number; scale?: number },
    ): string | null {
      const stored = this.svgDocuments.get(svgId);
      if (!stored || pathIndex >= stored.document.paths.length) return null;

      const path = stored.document.paths[pathIndex];
      const registration = meshParticleManager.registerFromSVG(
        svgId,
        path.id,
        name || `${stored.name}_${pathIndex}`,
        options,
      );

      if (!registration) return null;

      const storedMesh: StoredMeshParticle = {
        id: registration.id,
        name: registration.name,
        registration,
        source: "svg",
        sourceId: path.id,
      };

      this.meshParticles.set(registration.id, storedMesh);
      this.selectedMeshParticleId = registration.id;

      return registration.id;
    },

    /**
     * Get emitter config for mesh-based emission
     */
    getMeshEmitterConfig(meshId: string) {
      return meshParticleManager.getEmitterShapeConfig(meshId);
    },

    /**
     * Create instanced mesh for particle rendering
     */
    createInstancedMesh(
      meshId: string,
      maxInstances: number,
      materialId?: string,
    ): THREE.InstancedMesh | null {
      const material = materialId
        ? this.getThreeMaterial(materialId)
        : undefined;
      const result = meshParticleManager.createInstancedMesh(
        meshId,
        maxInstances,
        material || undefined,
      );
      return result?.mesh || null;
    },

    /**
     * Delete a mesh particle
     */
    deleteMeshParticle(id: string): void {
      meshParticleManager.unregisterMesh(id);
      this.meshParticles.delete(id);
      if (this.selectedMeshParticleId === id) {
        this.selectedMeshParticleId = null;
      }
    },

    // ========================================================================
    // SPRITE SHEETS
    // ========================================================================

    /**
     * Import sprite sheet from file
     */
    async importSpriteSheet(
      file: File,
      columns: number,
      rows: number,
      options?: { name?: string; frameRate?: number },
    ): Promise<AssetImportResult> {
      this.isLoadingSpriteSheet = true;
      try {
        const url = URL.createObjectURL(file);
        const config = await spriteSheetService.loadFromGrid(
          url,
          columns,
          rows,
          {
            name: options?.name || file.name.replace(/\.[^.]+$/, ""),
            frameRate: options?.frameRate,
          },
        );

        const stored: StoredSpriteSheet = {
          id: config.id,
          name: config.name || config.id,
          config,
          textureUrl: url,
        };

        this.spriteSheets.set(config.id, stored);
        this.selectedSpriteSheetId = config.id;

        return { success: true, assetId: config.id };
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        this.lastError = `Sprite sheet import failed: ${message}`;
        return { success: false, error: message };
      } finally {
        this.isLoadingSpriteSheet = false;
      }
    },

    /**
     * Import a single sprite (1x1 grid) with validation
     */
    async importSprite(
      file: File,
      options?: { name?: string; showWarnings?: boolean },
    ): Promise<AssetImportResult & { validation?: SpriteValidationResult }> {
      const toastStore = useToastStore();
      const showWarnings = options?.showWarnings ?? true;

      // Validate first
      const validation = await loadAndValidateSprite(file);

      if (!validation.canImport) {
        // Handle blocking errors
        this.handleValidationIssues(validation.issues, toastStore, true);
        this.lastError =
          validation.issues.find((i) => i.severity === "error")?.message ||
          "Validation failed";
        return { success: false, error: this.lastError, validation };
      }

      // Show warnings if enabled
      if (showWarnings) {
        this.handleValidationIssues(validation.issues, toastStore, false);
      }

      // Import as 1x1 spritesheet
      const result = await this.importSpriteSheet(file, 1, 1, options);

      if (result.success) {
        toastStore.success(
          `Sprite "${options?.name || file.name}" imported successfully`,
        );
      }

      return { ...result, validation };
    },

    /**
     * Import sprite sheet with full validation
     */
    async importSpriteSheetValidated(
      file: File,
      columns: number,
      rows: number,
      options?: { name?: string; frameRate?: number; showWarnings?: boolean },
    ): Promise<
      AssetImportResult & { validation?: SpritesheetValidationResult }
    > {
      const toastStore = useToastStore();
      const showWarnings = options?.showWarnings ?? true;

      // Validate first
      const validation = await loadAndValidateSpritesheet(file, columns, rows);

      if (!validation.canImport) {
        // Handle blocking errors
        this.handleValidationIssues(validation.issues, toastStore, true);
        this.lastError =
          validation.issues.find((i) => i.severity === "error")?.message ||
          "Validation failed";
        return { success: false, error: this.lastError, validation };
      }

      // Show warnings if enabled
      if (showWarnings) {
        this.handleValidationIssues(validation.issues, toastStore, false);
      }

      // Import the spritesheet
      const result = await this.importSpriteSheet(file, columns, rows, options);

      if (result.success && validation.metadata) {
        const meta = validation.metadata;
        toastStore.success(
          `Sprite sheet "${options?.name || file.name}" imported: ${meta.totalFrames} frames (${meta.frameWidth}x${meta.frameHeight}px each)`,
        );
      }

      return { ...result, validation };
    },

    /**
     * Display validation issues as toast notifications
     */
    handleValidationIssues(
      issues: SpriteValidationIssue[],
      toastStore: ReturnType<typeof useToastStore>,
      errorsOnly: boolean = false,
    ): void {
      for (const issue of issues) {
        if (issue.severity === "error") {
          toastStore.error(issue.message);
        } else if (!errorsOnly && issue.severity === "warning") {
          toastStore.warning(issue.message);
        }
      }
    },

    /**
     * Add animation to sprite sheet
     */
    addSpriteAnimation(
      sheetId: string,
      name: string,
      frames: number[],
      options?: { frameRate?: number; loop?: boolean; pingPong?: boolean },
    ): void {
      spriteSheetService.addAnimation(sheetId, {
        name,
        frames,
        frameRate: options?.frameRate ?? 24,
        loop: options?.loop ?? true,
        pingPong: options?.pingPong ?? false,
      });
    },

    /**
     * Get particle texture config for GPU particles
     */
    getParticleTextureConfig(sheetId: string): ParticleSpriteConfig | null {
      return spriteSheetService.getParticleTextureConfig(
        sheetId,
      ) as ParticleSpriteConfig | null;
    },

    /**
     * Delete a sprite sheet
     */
    deleteSpriteSheet(id: string): void {
      const stored = this.spriteSheets.get(id);
      if (stored?.textureUrl) {
        URL.revokeObjectURL(stored.textureUrl);
      }
      spriteSheetService.removeSheet(id);
      this.spriteSheets.delete(id);
      if (this.selectedSpriteSheetId === id) {
        this.selectedSpriteSheetId = null;
      }
    },

    // ========================================================================
    // ENVIRONMENT
    // ========================================================================

    /**
     * Load HDRI environment map
     */
    async loadEnvironment(
      file: File,
      options?: {
        intensity?: number;
        rotation?: number;
        useAsBackground?: boolean;
      },
    ): Promise<AssetImportResult> {
      this.isLoadingEnvironment = true;
      try {
        const url = URL.createObjectURL(file);

        this.environment = {
          ...this.environment,
          url,
          intensity: options?.intensity ?? this.environment.intensity,
          rotation: options?.rotation ?? this.environment.rotation,
          useAsBackground:
            options?.useAsBackground ?? this.environment.useAsBackground,
          enabled: true,
        };

        storeLogger.debug("Environment loaded:", file.name);
        return { success: true };
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        this.lastError = `Environment load failed: ${message}`;
        return { success: false, error: message };
      } finally {
        this.isLoadingEnvironment = false;
      }
    },

    /**
     * Load environment from preset URL
     */
    async loadEnvironmentPreset(
      presetUrl: string,
      presetName: string,
    ): Promise<AssetImportResult> {
      this.isLoadingEnvironment = true;
      try {
        this.environment = {
          ...this.environment,
          url: presetUrl,
          presetName,
          enabled: true,
        };

        return { success: true };
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        this.lastError = `Environment preset load failed: ${message}`;
        return { success: false, error: message };
      } finally {
        this.isLoadingEnvironment = false;
      }
    },

    /**
     * Update environment settings
     */
    updateEnvironment(settings: Partial<EnvironmentState>): void {
      this.environment = { ...this.environment, ...settings };
    },

    /**
     * Clear environment
     */
    clearEnvironment(): void {
      if (this.environment.url && !this.environment.presetName) {
        URL.revokeObjectURL(this.environment.url);
      }
      this.environment = {
        enabled: false,
        url: null,
        intensity: 1.0,
        rotation: 0,
        backgroundBlur: 0,
        useAsBackground: true,
      };
      this.environmentTexture = null;
    },

    // ========================================================================
    // UTILITIES
    // ========================================================================

    /**
     * Clear last error
     */
    clearError(): void {
      this.lastError = null;
    },

    /**
     * Dispose all assets and free resources
     */
    dispose(): void {
      // Revoke all blob URLs
      for (const stored of this.materials.values()) {
        for (const key of Object.keys(stored.config)) {
          const value = (stored.config as any)[key];
          if (typeof value === "string" && value.startsWith("blob:")) {
            URL.revokeObjectURL(value);
          }
        }
      }

      for (const stored of this.spriteSheets.values()) {
        if (stored.textureUrl.startsWith("blob:")) {
          URL.revokeObjectURL(stored.textureUrl);
        }
      }

      if (this.environment.url && !this.environment.presetName) {
        URL.revokeObjectURL(this.environment.url);
      }

      // Dispose services
      svgExtrusionService.dispose();
      meshParticleManager.dispose();
      spriteSheetService.dispose();
      materialSystem.dispose();

      // Clear state
      this.materials.clear();
      this.svgDocuments.clear();
      this.meshParticles.clear();
      this.spriteSheets.clear();
      this.selectedMaterialId = null;
      this.selectedSvgId = null;
      this.selectedMeshParticleId = null;
      this.selectedSpriteSheetId = null;
      this.clearEnvironment();
    },
  },
});
