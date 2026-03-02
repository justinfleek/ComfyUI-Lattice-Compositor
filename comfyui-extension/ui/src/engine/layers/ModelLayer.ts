/**
 * ModelLayer - 3D Model Import Layer
 *
 * Supports loading and rendering 3D models in various formats:
 * - GLTF/GLB (Khronos standard, web-optimized)
 * - OBJ (Wavefront, widely supported)
 * - FBX (Autodesk, animation-rich)
 * - USD/USDZ (Pixar/Apple, AR/VR standard)
 * - DAE (Collada, interchange format)
 *
 * Features:
 * - Animation playback with mixer
 * - Material overrides (wireframe, color, PBR properties)
 * - Bounding box visualization
 * - Skeleton/bone visualization
 * - LOD (Level of Detail) support
 * - Shadow casting/receiving
 * - Depth/Normal material modes for matte export
 */

import * as THREE from "three";
import { SkeletonHelper } from "three";
import { MeshoptDecoder } from "three/examples/jsm/libs/meshopt_decoder.module.js";
import {
  type Collada,
  ColladaLoader,
} from "three/examples/jsm/loaders/ColladaLoader.js";
import { DRACOLoader } from "three/examples/jsm/loaders/DRACOLoader.js";
import { FBXLoader } from "three/examples/jsm/loaders/FBXLoader.js";
import {
  type GLTF,
  GLTFLoader,
} from "three/examples/jsm/loaders/GLTFLoader.js";
import { OBJLoader } from "three/examples/jsm/loaders/OBJLoader.js";
import { interpolateProperty } from "@/services/interpolation";
import type {
  Layer,
  ModelAnimationClip,
  ModelBoundingBox,
  ModelLayerData,
  ModelMaterialOverride,
} from "@/types/project";
import { BaseLayer } from "./BaseLayer";

export class ModelLayer extends BaseLayer {
  /** The loaded 3D model */
  private model: THREE.Group | THREE.Object3D | null = null;

  /** Original materials (for restoring after override) */
  private originalMaterials: Map<
    THREE.Mesh,
    THREE.Material | THREE.Material[]
  > = new Map();

  /** Animation mixer for animated models */
  private mixer: THREE.AnimationMixer | null = null;

  /** Available animation clips */
  private animationClips: THREE.AnimationClip[] = [];

  /** Currently playing animation action */
  private currentAction: THREE.AnimationAction | null = null;

  /** Skeleton helper for bone visualization */
  private skeletonHelper: SkeletonHelper | null = null;

  /** Bounding box helper */
  private boundingBoxHelper: THREE.BoxHelper | null = null;

  /** Layer data */
  private modelData: ModelLayerData;

  /** Loading state */
  private isLoading = false;
  private loadError: string | null = null;

  /** Shared loaders (static for efficiency) */
  private static gltfLoader: GLTFLoader | null = null;
  private static objLoader: OBJLoader | null = null;
  private static fbxLoader: FBXLoader | null = null;
  private static colladaLoader: ColladaLoader | null = null;
  private static dracoLoader: DRACOLoader | null = null;

  constructor(layerData: Layer) {
    super(layerData);

    this.modelData = this.extractModelData(layerData);

    // Initialize loaders on first use
    this.initializeLoaders();

    // Load the model
    this.loadModel();

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  /**
   * Initialize shared loaders
   */
  private initializeLoaders(): void {
    if (!ModelLayer.gltfLoader) {
      ModelLayer.gltfLoader = new GLTFLoader();

      // Set up DRACO decoder for compressed meshes
      ModelLayer.dracoLoader = new DRACOLoader();
      ModelLayer.dracoLoader.setDecoderPath("/draco/");
      ModelLayer.gltfLoader.setDRACOLoader(ModelLayer.dracoLoader);

      // Set up meshopt decoder
      ModelLayer.gltfLoader.setMeshoptDecoder(MeshoptDecoder);
    }

    if (!ModelLayer.objLoader) {
      ModelLayer.objLoader = new OBJLoader();
    }

    if (!ModelLayer.fbxLoader) {
      ModelLayer.fbxLoader = new FBXLoader();
    }

    if (!ModelLayer.colladaLoader) {
      ModelLayer.colladaLoader = new ColladaLoader();
    }
  }

  /**
   * Extract model data from layer
   */
  private extractModelData(layerData: Layer): ModelLayerData {
    const data = layerData.data as ModelLayerData | null;

    // Create default animatable property
    const defaultScale = {
      id: `${layerData.id}_scale`,
      name: "Scale",
      type: "number" as const,
      value: 1,
      animated: false,
      keyframes: [],
    };

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: data ∈ ModelLayerData | null → ModelLayerData (with explicit defaults)
    const dataValue = (layerData.data !== null && typeof layerData.data === "object") ? layerData.data as ModelLayerData : null;
    
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: Extract each property with explicit type narrowing and defaults
    const assetIdValue = (dataValue !== null && typeof dataValue === "object" && "assetId" in dataValue && typeof dataValue.assetId === "string") ? dataValue.assetId : "";
    const formatValue = (dataValue !== null && typeof dataValue === "object" && "format" in dataValue && typeof dataValue.format === "string") ? dataValue.format : "gltf";
    const scaleValue = (dataValue !== null && typeof dataValue === "object" && "scale" in dataValue && dataValue.scale !== null && typeof dataValue.scale === "object") ? dataValue.scale : defaultScale;
    const uniformScaleValue = (dataValue !== null && typeof dataValue === "object" && "uniformScale" in dataValue && typeof dataValue.uniformScale === "boolean") ? dataValue.uniformScale : true;
    const materialOverrideValue = (dataValue !== null && typeof dataValue === "object" && "materialOverride" in dataValue) ? dataValue.materialOverride : undefined;
    const animationValue = (dataValue !== null && typeof dataValue === "object" && "animation" in dataValue) ? dataValue.animation : undefined;
    const boundingBoxValue = (dataValue !== null && typeof dataValue === "object" && "boundingBox" in dataValue) ? dataValue.boundingBox : undefined;
    const castShadowValue = (dataValue !== null && typeof dataValue === "object" && "castShadow" in dataValue && typeof dataValue.castShadow === "boolean") ? dataValue.castShadow : true;
    const receiveShadowValue = (dataValue !== null && typeof dataValue === "object" && "receiveShadow" in dataValue && typeof dataValue.receiveShadow === "boolean") ? dataValue.receiveShadow : true;
    const frustumCulledValue = (dataValue !== null && typeof dataValue === "object" && "frustumCulled" in dataValue && typeof dataValue.frustumCulled === "boolean") ? dataValue.frustumCulled : true;
    const renderOrderValue = (dataValue !== null && typeof dataValue === "object" && "renderOrder" in dataValue && typeof dataValue.renderOrder === "number" && Number.isFinite(dataValue.renderOrder)) ? dataValue.renderOrder : 0;
    const showBoundingBoxValue = (dataValue !== null && typeof dataValue === "object" && "showBoundingBox" in dataValue && typeof dataValue.showBoundingBox === "boolean") ? dataValue.showBoundingBox : false;
    const showSkeletonValue = (dataValue !== null && typeof dataValue === "object" && "showSkeleton" in dataValue && typeof dataValue.showSkeleton === "boolean") ? dataValue.showSkeleton : false;
    const envMapIntensityValue = (dataValue !== null && typeof dataValue === "object" && "envMapIntensity" in dataValue && typeof dataValue.envMapIntensity === "number" && Number.isFinite(dataValue.envMapIntensity)) ? dataValue.envMapIntensity : 1;
    const lodValue = (dataValue !== null && typeof dataValue === "object" && "lod" in dataValue) ? dataValue.lod : undefined;

    return {
      assetId: assetIdValue,
      format: formatValue,
      scale: scaleValue,
      uniformScale: uniformScaleValue,
      materialOverride: materialOverrideValue,
      animation: animationValue,
      boundingBox: boundingBoxValue,
      castShadow: castShadowValue,
      receiveShadow: receiveShadowValue,
      frustumCulled: frustumCulledValue,
      renderOrder: renderOrderValue,
      showBoundingBox: showBoundingBoxValue,
      showSkeleton: showSkeletonValue,
      envMapIntensity: envMapIntensityValue,
      lod: lodValue,
    };
  }

  /**
   * Load the 3D model from asset
   */
  private async loadModel(): Promise<void> {
    if (!this.modelData.assetId) {
      this.createPlaceholder();
      return;
    }

    this.isLoading = true;
    this.loadError = null;

    try {
      // Get asset URL from asset manager (placeholder for now)
      const url = await this.resolveAssetUrl(this.modelData.assetId);

      let loadedObject: THREE.Object3D;

      switch (this.modelData.format) {
        case "gltf":
        case "glb":
          loadedObject = await this.loadGLTF(url);
          break;
        case "obj":
          loadedObject = await this.loadOBJ(url);
          break;
        case "fbx":
          loadedObject = await this.loadFBX(url);
          break;
        case "dae":
          loadedObject = await this.loadCollada(url);
          break;
        case "usd":
        case "usda":
        case "usdc":
        case "usdz":
          loadedObject = await this.loadUSD(url);
          break;
        default:
          throw new Error(`Unsupported model format: ${this.modelData.format}`);
      }

      this.setModel(loadedObject);
    } catch (error) {
      this.loadError = error instanceof Error ? error.message : "Unknown error";
      console.error(`[ModelLayer] Failed to load model: ${this.loadError}`);
      this.createPlaceholder();
    } finally {
      this.isLoading = false;
    }
  }

  /**
   * Resolve asset ID to URL
   */
  private async resolveAssetUrl(assetId: string): Promise<string> {
    // For now, assume assetId is a URL or path
    // In production, this would query the asset manager
    return assetId;
  }

  /**
   * Load GLTF/GLB model
   */
  private loadGLTF(url: string): Promise<THREE.Object3D> {
    return new Promise((resolve, reject) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const loader = ModelLayer.gltfLoader;
      if (loader != null && typeof loader === "object" && typeof loader.load === "function") {
        loader.load(
          url,
          (gltf: GLTF) => {
            // Extract animations
            if (gltf.animations && gltf.animations.length > 0) {
              this.animationClips = gltf.animations;
              this.setupAnimations(gltf.scene);
            }
            resolve(gltf.scene);
          },
          undefined,
          reject,
        );
      } else {
        reject(new Error("GLTF loader not initialized"));
      }
    });
  }

  /**
   * Load OBJ model
   */
  private loadOBJ(url: string): Promise<THREE.Object3D> {
    return new Promise((resolve, reject) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const loader = ModelLayer.objLoader;
      if (loader != null && typeof loader === "object" && typeof loader.load === "function") {
        loader.load(url, resolve, undefined, reject);
      } else {
        reject(new Error("OBJ loader not initialized"));
      }
    });
  }

  /**
   * Load FBX model
   */
  private loadFBX(url: string): Promise<THREE.Object3D> {
    return new Promise((resolve, reject) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const loader = ModelLayer.fbxLoader;
      if (loader != null && typeof loader === "object" && typeof loader.load === "function") {
        loader.load(
          url,
          (object: THREE.Group) => {
            // FBX files often contain animations
            if (object.animations && object.animations.length > 0) {
              this.animationClips = object.animations;
              this.setupAnimations(object);
            }
            resolve(object);
          },
          undefined,
          reject,
        );
      } else {
        reject(new Error("FBX loader not initialized"));
      }
    });
  }

  /**
   * Load Collada (DAE) model
   */
  private loadCollada(url: string): Promise<THREE.Object3D> {
    return new Promise((resolve, reject) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const loader = ModelLayer.colladaLoader;
      if (loader != null && typeof loader === "object" && typeof loader.load === "function") {
        loader.load(
          url,
          (collada: Collada) => {
            // Collada may have animations
            if (collada.scene.animations && collada.scene.animations.length > 0) {
              this.animationClips = collada.scene.animations;
              this.setupAnimations(collada.scene);
            }
            resolve(collada.scene);
          },
          undefined,
          reject,
        );
      } else {
        reject(new Error("Collada loader not initialized"));
      }
    });
  }

  /**
   * Load USD/USDZ model
   * Note: USD support in Three.js is limited. This is a placeholder for future implementation.
   */
  private async loadUSD(url: string): Promise<THREE.Object3D> {
    // USD/USDZ support requires additional libraries or custom implementation
    // For now, we'll try to use USDZLoader if available, or create a placeholder
    try {
      // Dynamic import to avoid bundle bloat if not used
      const { USDZLoader } = await import(
        "three/examples/jsm/loaders/USDZLoader.js"
      );
      const loader = new USDZLoader();
      return new Promise((resolve, reject) => {
        loader.load(url, resolve, undefined, reject);
      });
    } catch {
      console.warn(
        "[ModelLayer] USD/USDZ loader not available. Creating placeholder.",
      );
      return this.createUSDPlaceholder();
    }
  }

  /**
   * Create placeholder for USD when loader unavailable
   */
  private createUSDPlaceholder(): THREE.Object3D {
    const group = new THREE.Group();
    group.name = "usd_placeholder";

    // Create a simple cube with USD icon texture
    const geometry = new THREE.BoxGeometry(100, 100, 100);
    const material = new THREE.MeshStandardMaterial({
      color: 0x4a90d9,
      wireframe: true,
    });
    const mesh = new THREE.Mesh(geometry, material);
    group.add(mesh);

    return group;
  }

  /**
   * Create placeholder model when loading fails or no asset
   */
  private createPlaceholder(): void {
    const group = new THREE.Group();
    group.name = `model_placeholder_${this.id}`;

    // Create wireframe cube
    const geometry = new THREE.BoxGeometry(100, 100, 100);
    const material = new THREE.MeshBasicMaterial({
      color: 0xff6600,
      wireframe: true,
      transparent: true,
      opacity: 0.5,
    });
    const mesh = new THREE.Mesh(geometry, material);
    group.add(mesh);

    // Add axis helper
    const axisHelper = new THREE.AxesHelper(75);
    group.add(axisHelper);

    this.setModel(group);
  }

  /**
   * Set the loaded model
   */
  private setModel(object: THREE.Object3D): void {
    // Remove existing model
    if (this.model) {
      this.group.remove(this.model);
      this.disposeModel();
    }

    this.model = object;
    this.model.name = `model_${this.id}`;

    // Store original materials
    this.storeOriginalMaterials();

    // Apply shadow settings
    this.applyShadowSettings();

    // Apply material overrides if any
    if (this.modelData.materialOverride) {
      this.applyMaterialOverride(this.modelData.materialOverride);
    }

    // Calculate bounding box
    this.calculateBoundingBox();

    // Create helpers
    this.updateBoundingBoxHelper();
    this.updateSkeletonHelper();

    // Add to group
    this.group.add(this.model);
  }

  /**
   * Store original materials for later restoration
   */
  private storeOriginalMaterials(): void {
    this.originalMaterials.clear();

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const model = this.model;
    if (model != null && typeof model === "object" && typeof model.traverse === "function") {
      model.traverse((child) => {
        if (child instanceof THREE.Mesh) {
          this.originalMaterials.set(child, child.material);
        }
      });
    }
  }

  /**
   * Apply shadow settings to model
   */
  private applyShadowSettings(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const model = this.model;
    if (model != null && typeof model === "object" && typeof model.traverse === "function") {
      model.traverse((child) => {
        if (child instanceof THREE.Mesh) {
          child.castShadow = this.modelData.castShadow;
          child.receiveShadow = this.modelData.receiveShadow;
          child.frustumCulled = this.modelData.frustumCulled;
          child.renderOrder = this.modelData.renderOrder;
        }
      });
    }
  }

  /**
   * Calculate and store bounding box
   */
  private calculateBoundingBox(): void {
    if (!this.model) return;

    const box = new THREE.Box3().setFromObject(this.model);
    const center = box.getCenter(new THREE.Vector3());
    const size = box.getSize(new THREE.Vector3());

    this.modelData.boundingBox = {
      min: { x: box.min.x, y: box.min.y, z: box.min.z },
      max: { x: box.max.x, y: box.max.y, z: box.max.z },
      center: { x: center.x, y: center.y, z: center.z },
      size: { x: size.x, y: size.y, z: size.z },
    };
  }

  // ============================================================================
  // ANIMATION
  // ============================================================================

  /**
   * Setup animation mixer and actions
   */
  private setupAnimations(object: THREE.Object3D): void {
    this.mixer = new THREE.AnimationMixer(object);

    // Update model data with clip info - ensure animation object exists
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: modelData.animation ∈ ModelAnimation | undefined → ModelAnimation (create if missing)
    const animationValue = (typeof this.modelData.animation === "object" && this.modelData.animation !== null) ? this.modelData.animation : undefined;
    const animation = (animationValue !== undefined) ? animationValue : (this.modelData.animation = {
        clips: [],
        time: {
          id: `${this.id}_anim_time`,
          name: "Animation Time",
          type: "number" as const,
          value: 0,
          animated: false,
          keyframes: [],
        },
        speed: 1,
        loop: true,
        autoPlay: false,
      });

    animation.clips = this.animationClips.map((clip) => ({
      name: clip.name,
      duration: clip.duration,
      frameCount: Math.round(clip.duration * this.compositionFps),
    }));

    // Auto-play first clip if enabled
    if (animation.autoPlay && this.animationClips.length > 0) {
      this.playAnimation(this.animationClips[0].name);
    }
  }

  /**
   * Play an animation clip by name
   */
  playAnimation(clipName: string): void {
    if (!this.mixer) return;

    const clip = this.animationClips.find((c) => c.name === clipName);
    if (!clip) return;

    // Stop current action
    if (this.currentAction) {
      this.currentAction.stop();
    }

    // Create and play new action
    this.currentAction = this.mixer.clipAction(clip);
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const animation = (this.modelData != null && typeof this.modelData === "object" && "animation" in this.modelData && this.modelData.animation != null && typeof this.modelData.animation === "object") ? this.modelData.animation : undefined;
    const loop = (animation != null && typeof animation === "object" && "loop" in animation && typeof animation.loop === "boolean" && animation.loop) ? true : false;
    this.currentAction.setLoop(
      loop ? THREE.LoopRepeat : THREE.LoopOnce,
      Infinity,
    );
    this.currentAction.play();

    if (this.modelData.animation) {
      this.modelData.animation.activeClip = clipName;
    }
  }

  /**
   * Stop current animation
   */
  stopAnimation(): void {
    if (this.currentAction) {
      this.currentAction.stop();
      this.currentAction = null;
    }
    if (this.modelData.animation) {
      this.modelData.animation.activeClip = undefined;
    }
  }

  /**
   * Set animation time directly (for scrubbing)
   */
  setAnimationTime(time: number): void {
    if (!this.mixer || !this.currentAction) return;
    // Validate time (NaN would corrupt animation state)
    const validTime = Number.isFinite(time) ? Math.max(0, time) : 0;
    this.currentAction.time = validTime;
    this.mixer.update(0);
  }

  /**
   * Update animation mixer
   */
  private updateAnimation(deltaTime: number): void {
    if (!this.mixer) return;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: modelData.animation.speed ∈ number | undefined → number (default 1)
    const animationData = (typeof this.modelData.animation === "object" && this.modelData.animation !== null && "speed" in this.modelData.animation && typeof this.modelData.animation.speed === "number" && Number.isFinite(this.modelData.animation.speed)) ? this.modelData.animation.speed : undefined;
    const speed = (animationData !== undefined) ? animationData : 1;
    this.mixer.update(deltaTime * speed);
  }

  // ============================================================================
  // MATERIAL OVERRIDES
  // ============================================================================

  /**
   * Apply material override to all meshes
   */
  applyMaterialOverride(override: ModelMaterialOverride): void {
    if (!this.model) return;

    this.model.traverse((child) => {
      if (child instanceof THREE.Mesh) {
        this.applyMaterialOverrideToMesh(child, override);
      }
    });
  }

  /**
   * Apply material override to a single mesh
   */
  private applyMaterialOverrideToMesh(
    mesh: THREE.Mesh,
    override: ModelMaterialOverride,
  ): void {
    // Use depth material for depth map export
    if (override.useDepthMaterial) {
      mesh.material = new THREE.MeshDepthMaterial({
        depthPacking: THREE.RGBADepthPacking,
      });
      return;
    }

    // Use normal material for normal map export
    if (override.useNormalMaterial) {
      mesh.material = new THREE.MeshNormalMaterial();
      return;
    }

    // Clone material to avoid affecting shared materials
    let material = Array.isArray(mesh.material)
      ? mesh.material[0].clone()
      : mesh.material.clone();

    // Apply overrides
    if (override.wireframe !== undefined && "wireframe" in material) {
      (material as THREE.MeshStandardMaterial).wireframe = override.wireframe;
    }

    if (override.wireframeColor && override.wireframe) {
      material = new THREE.MeshBasicMaterial({
        color: override.wireframeColor,
        wireframe: true,
      });
    } else if (override.colorOverride) {
      // Type-safe color assignment - check if material has color property
      if (
        material instanceof THREE.MeshStandardMaterial ||
        material instanceof THREE.MeshBasicMaterial ||
        material instanceof THREE.MeshPhongMaterial ||
        material instanceof THREE.MeshLambertMaterial
      ) {
        material.color = new THREE.Color(override.colorOverride);
      }
    }

    if (override.opacityOverride !== undefined) {
      material.transparent = override.opacityOverride < 1;
      material.opacity = override.opacityOverride;
    }

    if (override.flatShading !== undefined && "flatShading" in material) {
      (material as THREE.MeshStandardMaterial).flatShading =
        override.flatShading;
      material.needsUpdate = true;
    }

    if (material instanceof THREE.MeshStandardMaterial) {
      if (override.metalness !== undefined) {
        material.metalness = override.metalness;
      }
      if (override.roughness !== undefined) {
        material.roughness = override.roughness;
      }
      if (override.emissive) {
        material.emissive = new THREE.Color(override.emissive);
      }
      if (override.emissiveIntensity !== undefined) {
        material.emissiveIntensity = override.emissiveIntensity;
      }
    }

    mesh.material = material;
  }

  /**
   * Restore original materials
   */
  restoreOriginalMaterials(): void {
    this.originalMaterials.forEach((material, mesh) => {
      mesh.material = material;
    });
  }

  // ============================================================================
  // HELPERS
  // ============================================================================

  /**
   * Update bounding box helper visibility
   */
  private updateBoundingBoxHelper(): void {
    // Remove existing helper
    if (this.boundingBoxHelper) {
      this.group.remove(this.boundingBoxHelper);
      this.boundingBoxHelper.dispose();
      this.boundingBoxHelper = null;
    }

    if (this.modelData.showBoundingBox && this.model) {
      this.boundingBoxHelper = new THREE.BoxHelper(this.model, 0x00ff00);
      this.boundingBoxHelper.name = `bbox_helper_${this.id}`;
      this.group.add(this.boundingBoxHelper);
    }
  }

  /**
   * Update skeleton helper visibility
   */
  private updateSkeletonHelper(): void {
    // Remove existing helper
    if (this.skeletonHelper) {
      this.group.remove(this.skeletonHelper);
      this.skeletonHelper.dispose();
      this.skeletonHelper = null;
    }

    if (this.modelData.showSkeleton && this.model) {
      // Find skinned mesh with skeleton
      let skeleton: THREE.Skeleton | null = null;
      this.model.traverse((child) => {
        if (child instanceof THREE.SkinnedMesh && child.skeleton) {
          skeleton = child.skeleton;
        }
      });

      if (skeleton) {
        this.skeletonHelper = new SkeletonHelper(this.model);
        this.skeletonHelper.name = `skeleton_helper_${this.id}`;
        (this.skeletonHelper.material as THREE.LineBasicMaterial).linewidth = 2;
        this.group.add(this.skeletonHelper);
      }
    }
  }

  // ============================================================================
  // SETTERS
  // ============================================================================

  /**
   * Set model scale
   */
  setScale(scale: number | { x: number; y: number; z: number }): void {
    if (!this.model) return;

    if (typeof scale === "number") {
      // Validate scale (NaN would corrupt model transform)
      const validScale = Number.isFinite(scale) ? scale : 1;
      this.model.scale.setScalar(validScale);
    } else {
      // Validate all components (NaN would corrupt model transform)
      const validX = Number.isFinite(scale.x) ? scale.x : 1;
      const validY = Number.isFinite(scale.y) ? scale.y : 1;
      const validZ = Number.isFinite(scale.z) ? scale.z : 1;
      this.model.scale.set(validX, validY, validZ);
    }

    // Update bounding box helper
    if (this.boundingBoxHelper) {
      this.boundingBoxHelper.update();
    }
  }

  /**
   * Set bounding box visibility
   */
  setShowBoundingBox(show: boolean): void {
    this.modelData.showBoundingBox = show;
    this.updateBoundingBoxHelper();
  }

  /**
   * Set skeleton visibility
   */
  setShowSkeleton(show: boolean): void {
    this.modelData.showSkeleton = show;
    this.updateSkeletonHelper();
  }

  /**
   * Set FPS for animation sync
   * @deprecated Use setCompositionFps from BaseLayer instead
   */
  setFPS(fps: number): void {
    this.setCompositionFps(fps);
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Get the loaded model object
   */
  getModel(): THREE.Object3D | null {
    return this.model;
  }

  /**
   * Get available animation clips
   */
  getAnimationClips(): ModelAnimationClip[] {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: modelData.animation.clips ∈ ModelAnimationClip[] | undefined → ModelAnimationClip[] (default [])
    const animationData = (typeof this.modelData.animation === "object" && this.modelData.animation !== null && "clips" in this.modelData.animation && Array.isArray(this.modelData.animation.clips)) ? this.modelData.animation.clips : undefined;
    return (animationData !== undefined) ? animationData : [];
  }

  /**
   * Get model-specific bounding box data
   */
  getModelBoundingBox(): ModelBoundingBox | undefined {
    return this.modelData.boundingBox;
  }

  /**
   * Check if model is loading
   */
  isModelLoading(): boolean {
    return this.isLoading;
  }

  /**
   * Get load error if any
   */
  getLoadError(): string | null {
    return this.loadError;
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Use composition fps for correct animation timing (not hardcoded 30fps)
    const fps = this.compositionFps;
    const layerId = this.id;

    // Evaluate animated scale
    let scale: number;
    if (
      typeof this.modelData.scale === "object" &&
      "value" in this.modelData.scale
    ) {
      scale = interpolateProperty(this.modelData.scale, frame, fps, layerId);
      this.setScale(scale);
    }

    // Evaluate animation time if keyframed
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const animation = (this.modelData != null && typeof this.modelData === "object" && "animation" in this.modelData && this.modelData.animation != null && typeof this.modelData.animation === "object") ? this.modelData.animation : undefined;
    const animationTime = (animation != null && typeof animation === "object" && "time" in animation && animation.time != null) ? animation.time : undefined;
    if (animationTime != null) {
      const time = interpolateProperty(
        animationTime,
        frame,
        fps,
        layerId,
      );
      this.setAnimationTime(time);
    }

    // Update animation mixer (for auto-playing animations)
    const animationAutoPlay = (animation != null && typeof animation === "object" && "autoPlay" in animation && typeof animation.autoPlay === "boolean" && animation.autoPlay) ? true : false;
    if (this.mixer && animationAutoPlay) {
      const deltaTime = 1 / this.compositionFps;
      this.updateAnimation(deltaTime);
    }

    // Update helpers
    if (this.boundingBoxHelper) {
      this.boundingBoxHelper.update();
    }
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    const props = state.properties;

    if (props.scale !== undefined) {
      this.setScale(props.scale as number);
    }

    if (props.animationTime !== undefined) {
      this.setAnimationTime(props.animationTime as number);
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<ModelLayerData> | undefined;

    if (data) {
      // Handle asset change (requires reload)
      if (
        data.assetId !== undefined &&
        data.assetId !== this.modelData.assetId
      ) {
        this.modelData.assetId = data.assetId;
        if (data.format) {
          this.modelData.format = data.format;
        }
        this.loadModel();
      }

      // Handle material override change
      if (data.materialOverride !== undefined) {
        this.modelData.materialOverride = data.materialOverride;
        if (data.materialOverride) {
          this.applyMaterialOverride(data.materialOverride);
        } else {
          this.restoreOriginalMaterials();
        }
      }

      // Handle shadow settings
      if (data.castShadow !== undefined || data.receiveShadow !== undefined) {
        if (data.castShadow !== undefined) {
          this.modelData.castShadow = data.castShadow;
        }
        if (data.receiveShadow !== undefined) {
          this.modelData.receiveShadow = data.receiveShadow;
        }
        this.applyShadowSettings();
      }

      // Handle helper visibility
      if (data.showBoundingBox !== undefined) {
        this.setShowBoundingBox(data.showBoundingBox);
      }
      if (data.showSkeleton !== undefined) {
        this.setShowSkeleton(data.showSkeleton);
      }

      // Handle animation settings
      if (data.animation !== undefined) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: modelData.animation ∈ ModelAnimation | undefined → ModelAnimation (create if missing)
        // Deterministic: Ensure animation object exists before accessing properties
        if (!this.modelData.animation) {
          this.modelData.animation = {
            clips: [],
            time: {
              id: `${this.id}_anim_time`,
              name: "Animation Time",
              type: "number" as const,
              value: 0,
              animated: false,
              keyframes: [],
            },
            speed: 1,
            loop: false,
            autoPlay: false,
          };
        }
        // Deterministic: Type guard ensures animation is defined after check
        const animation = this.modelData.animation;
        if (!animation) {
          throw new Error("[ModelLayer] Animation should be defined after initialization check");
        }
        if (data.animation.clips !== undefined) {
          animation.clips = data.animation.clips;
        }
        if (data.animation.activeClip !== undefined) {
          animation.activeClip = data.animation.activeClip;
        }
        if (data.animation.time !== undefined) {
          animation.time = data.animation.time;
        }
        if (data.animation.speed !== undefined) {
          animation.speed = data.animation.speed;
        }
        if (data.animation.loop !== undefined) {
          animation.loop = data.animation.loop;
        }
        if (data.animation.autoPlay !== undefined) {
          animation.autoPlay = data.animation.autoPlay;
        }
        // Deterministic: Explicit null check before calling playAnimation
        if (data.animation.activeClip) {
          // Type guard ensures animation is defined
          const activeAnimation = this.modelData.animation;
          if (activeAnimation) {
            this.playAnimation(data.animation.activeClip);
          }
        }
      }
    }
  }

  protected onDispose(): void {
    this.disposeModel();
  }

  /**
   * Dispose model resources
   */
  private disposeModel(): void {
    // Stop animations
    if (this.mixer) {
      this.mixer.stopAllAction();
      this.mixer = null;
    }

    // Dispose helpers
    if (this.boundingBoxHelper) {
      this.boundingBoxHelper.dispose();
      this.boundingBoxHelper = null;
    }
    if (this.skeletonHelper) {
      this.skeletonHelper.dispose();
      this.skeletonHelper = null;
    }

    // Dispose model geometries and materials
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const model = this.model;
    if (model != null && typeof model === "object" && typeof model.traverse === "function") {
      model.traverse((child) => {
        if (child instanceof THREE.Mesh) {
          child.geometry.dispose();
          if (Array.isArray(child.material)) {
            child.material.forEach((m) => m.dispose());
          } else {
            child.material.dispose();
          }
        }
      });
    }

    this.originalMaterials.clear();
    this.animationClips = [];
    this.currentAction = null;
    this.model = null;
  }
}
