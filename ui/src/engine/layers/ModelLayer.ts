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

import * as THREE from 'three';
import { GLTFLoader, type GLTF } from 'three/examples/jsm/loaders/GLTFLoader.js';
import { OBJLoader } from 'three/examples/jsm/loaders/OBJLoader.js';
import { FBXLoader } from 'three/examples/jsm/loaders/FBXLoader.js';
import { ColladaLoader, type Collada } from 'three/examples/jsm/loaders/ColladaLoader.js';
import { DRACOLoader } from 'three/examples/jsm/loaders/DRACOLoader.js';
import { KTX2Loader } from 'three/examples/jsm/loaders/KTX2Loader.js';
import { MeshoptDecoder } from 'three/examples/jsm/libs/meshopt_decoder.module.js';
import { SkeletonHelper } from 'three';
import type {
  Layer,
  ModelLayerData,
  ModelFormat,
  ModelMaterialOverride,
  ModelAnimationClip,
  ModelBoundingBox,
} from '@/types/project';
import { BaseLayer } from './BaseLayer';
import { interpolateProperty } from '@/services/interpolation';

export class ModelLayer extends BaseLayer {
  /** The loaded 3D model */
  private model: THREE.Group | THREE.Object3D | null = null;

  /** Original materials (for restoring after override) */
  private originalMaterials: Map<THREE.Mesh, THREE.Material | THREE.Material[]> = new Map();

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

  /** Composition FPS for animation sync */
  private fps = 30;

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
      ModelLayer.dracoLoader.setDecoderPath('/draco/');
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
      name: 'Scale',
      type: 'number' as const,
      value: 1,
      animated: false,
      keyframes: [],
    };

    return {
      assetId: data?.assetId ?? '',
      format: data?.format ?? 'gltf',
      scale: data?.scale ?? defaultScale,
      uniformScale: data?.uniformScale ?? true,
      materialOverride: data?.materialOverride,
      animation: data?.animation,
      boundingBox: data?.boundingBox,
      castShadow: data?.castShadow ?? true,
      receiveShadow: data?.receiveShadow ?? true,
      frustumCulled: data?.frustumCulled ?? true,
      renderOrder: data?.renderOrder ?? 0,
      showBoundingBox: data?.showBoundingBox ?? false,
      showSkeleton: data?.showSkeleton ?? false,
      envMapIntensity: data?.envMapIntensity ?? 1,
      lod: data?.lod,
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
        case 'gltf':
        case 'glb':
          loadedObject = await this.loadGLTF(url);
          break;
        case 'obj':
          loadedObject = await this.loadOBJ(url);
          break;
        case 'fbx':
          loadedObject = await this.loadFBX(url);
          break;
        case 'dae':
          loadedObject = await this.loadCollada(url);
          break;
        case 'usd':
        case 'usda':
        case 'usdc':
        case 'usdz':
          loadedObject = await this.loadUSD(url);
          break;
        default:
          throw new Error(`Unsupported model format: ${this.modelData.format}`);
      }

      this.setModel(loadedObject);
    } catch (error) {
      this.loadError = error instanceof Error ? error.message : 'Unknown error';
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
      ModelLayer.gltfLoader!.load(
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
        reject
      );
    });
  }

  /**
   * Load OBJ model
   */
  private loadOBJ(url: string): Promise<THREE.Object3D> {
    return new Promise((resolve, reject) => {
      ModelLayer.objLoader!.load(url, resolve, undefined, reject);
    });
  }

  /**
   * Load FBX model
   */
  private loadFBX(url: string): Promise<THREE.Object3D> {
    return new Promise((resolve, reject) => {
      ModelLayer.fbxLoader!.load(
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
        reject
      );
    });
  }

  /**
   * Load Collada (DAE) model
   */
  private loadCollada(url: string): Promise<THREE.Object3D> {
    return new Promise((resolve, reject) => {
      ModelLayer.colladaLoader!.load(
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
        reject
      );
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
      const { USDZLoader } = await import('three/examples/jsm/loaders/USDZLoader.js');
      const loader = new USDZLoader();
      return new Promise((resolve, reject) => {
        loader.load(url, resolve, undefined, reject);
      });
    } catch {
      console.warn('[ModelLayer] USD/USDZ loader not available. Creating placeholder.');
      return this.createUSDPlaceholder();
    }
  }

  /**
   * Create placeholder for USD when loader unavailable
   */
  private createUSDPlaceholder(): THREE.Object3D {
    const group = new THREE.Group();
    group.name = 'usd_placeholder';

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

    this.model?.traverse((child) => {
      if (child instanceof THREE.Mesh) {
        this.originalMaterials.set(child, child.material);
      }
    });
  }

  /**
   * Apply shadow settings to model
   */
  private applyShadowSettings(): void {
    this.model?.traverse((child) => {
      if (child instanceof THREE.Mesh) {
        child.castShadow = this.modelData.castShadow;
        child.receiveShadow = this.modelData.receiveShadow;
        child.frustumCulled = this.modelData.frustumCulled;
        child.renderOrder = this.modelData.renderOrder;
      }
    });
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

    // Update model data with clip info
    if (!this.modelData.animation) {
      this.modelData.animation = {
        clips: [],
        time: {
          id: `${this.id}_anim_time`,
          name: 'Animation Time',
          type: 'number' as const,
          value: 0,
          animated: false,
          keyframes: [],
        },
        speed: 1,
        loop: true,
        autoPlay: false,
      };
    }

    this.modelData.animation!.clips = this.animationClips.map((clip) => ({
      name: clip.name,
      duration: clip.duration,
      frameCount: Math.round(clip.duration * this.fps),
    }));

    // Auto-play first clip if enabled
    if (this.modelData.animation.autoPlay && this.animationClips.length > 0) {
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
    this.currentAction.setLoop(
      this.modelData.animation?.loop ? THREE.LoopRepeat : THREE.LoopOnce,
      Infinity
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
    this.currentAction.time = time;
    this.mixer.update(0);
  }

  /**
   * Update animation mixer
   */
  private updateAnimation(deltaTime: number): void {
    if (!this.mixer) return;

    const speed = this.modelData.animation?.speed ?? 1;
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
  private applyMaterialOverrideToMesh(mesh: THREE.Mesh, override: ModelMaterialOverride): void {
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
    if (override.wireframe !== undefined) {
      (material as any).wireframe = override.wireframe;
    }

    if (override.wireframeColor && override.wireframe) {
      material = new THREE.MeshBasicMaterial({
        color: override.wireframeColor,
        wireframe: true,
      });
    } else if (override.colorOverride) {
      (material as any).color = new THREE.Color(override.colorOverride);
    }

    if (override.opacityOverride !== undefined) {
      material.transparent = override.opacityOverride < 1;
      material.opacity = override.opacityOverride;
    }

    if (override.flatShading !== undefined && 'flatShading' in material) {
      (material as THREE.MeshStandardMaterial).flatShading = override.flatShading;
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

    if (typeof scale === 'number') {
      this.model.scale.setScalar(scale);
    } else {
      this.model.scale.set(scale.x, scale.y, scale.z);
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
   */
  setFPS(fps: number): void {
    this.fps = fps;
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
    return this.modelData.animation?.clips ?? [];
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
    // Evaluate animated scale
    let scale: number;
    if (typeof this.modelData.scale === 'object' && 'value' in this.modelData.scale) {
      scale = interpolateProperty(this.modelData.scale, frame);
      this.setScale(scale);
    }

    // Evaluate animation time if keyframed
    if (this.modelData.animation?.time) {
      const time = interpolateProperty(this.modelData.animation.time, frame);
      this.setAnimationTime(time);
    }

    // Update animation mixer (for auto-playing animations)
    if (this.mixer && this.modelData.animation?.autoPlay) {
      const deltaTime = 1 / this.fps;
      this.updateAnimation(deltaTime);
    }

    // Update helpers
    if (this.boundingBoxHelper) {
      this.boundingBoxHelper.update();
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    const props = state.properties;

    if (props['scale'] !== undefined) {
      this.setScale(props['scale'] as number);
    }

    if (props['animationTime'] !== undefined) {
      this.setAnimationTime(props['animationTime'] as number);
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<ModelLayerData> | undefined;

    if (data) {
      // Handle asset change (requires reload)
      if (data.assetId !== undefined && data.assetId !== this.modelData.assetId) {
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
        Object.assign(this.modelData.animation ?? {}, data.animation);
        if (data.animation.activeClip) {
          this.playAnimation(data.animation.activeClip);
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
    this.model?.traverse((child) => {
      if (child instanceof THREE.Mesh) {
        child.geometry.dispose();
        if (Array.isArray(child.material)) {
          child.material.forEach((m) => m.dispose());
        } else {
          child.material.dispose();
        }
      }
    });

    this.originalMaterials.clear();
    this.animationClips = [];
    this.currentAction = null;
    this.model = null;
  }
}
