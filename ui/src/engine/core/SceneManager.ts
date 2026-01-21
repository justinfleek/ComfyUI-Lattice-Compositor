/**
 * SceneManager - Three.js Scene Management
 *
 * Manages the Three.js scene graph with separate groups for:
 * - Composition layers (main content)
 * - Overlay elements (gizmos, guides, selection)
 * - Debug helpers (axis, grid)
 */

import * as THREE from "three";
import { EXRLoader } from "three/examples/jsm/loaders/EXRLoader.js";
import { RGBELoader } from "three/examples/jsm/loaders/RGBELoader.js";
import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

// ============================================================================
// TYPE EXTENSIONS FOR THREE.JS COMPATIBILITY
// ============================================================================

/**
 * Extended Object3D interface for compatibility with objects from different Three.js instances
 * These properties exist at runtime but may not pass instanceof checks
 */
interface CompatibleObject3D {
  updateMatrixWorld?: (force?: boolean) => void;
  updateWorldMatrix?: (updateParents?: boolean, updateChildren?: boolean) => void;
  children?: CompatibleObject3D[];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: parent ∈ CompatibleObject3D | null (Three.js API allows null for root)
  // Note: Three.js Object3D.parent can be null - this is API requirement
  parent?: CompatibleObject3D | null;
  dispatchEvent?: (event: { type: string }) => void;
}

/** Environment map configuration */
export interface EnvironmentMapConfig {
  enabled: boolean;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null/undefined
  // Pattern match: url ∈ string (empty string = no URL, never null/undefined)
  url: string;
  intensity: number;
  rotation: number; // Y-axis rotation in degrees
  backgroundBlur: number; // 0-1, blur for background
  useAsBackground: boolean; // Show HDRI as scene background
  toneMapping: boolean; // Apply tone mapping
}

export class SceneManager {
  /** The main Three.js scene */
  public readonly scene: THREE.Scene;

  /** Group for composition layers (rendered content) */
  public readonly compositionGroup: THREE.Group;

  /** Group for UI overlay elements */
  public readonly overlayGroup: THREE.Group;

  /** Group for debug helpers */
  public readonly debugGroup: THREE.Group;

  /** Environment map texture */
  private environmentMap: THREE.Texture | null = null;

  /** Environment map configuration */
  private envConfig: EnvironmentMapConfig = {
    enabled: false,
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null/undefined
    // Pattern match: url ∈ string (empty string = no URL, never null/undefined)
    url: "",
    intensity: 1,
    rotation: 0,
    backgroundBlur: 0,
    useAsBackground: true,
    toneMapping: true,
  };

  /** PMREM Generator for environment maps */
  private pmremGenerator: THREE.PMREMGenerator | null = null;

  /** HDRI loaders */
  private rgbeLoader: RGBELoader | null = null;
  private exrLoader: EXRLoader | null = null;

  /** Composition bounds frame */
  private compositionBounds: THREE.LineLoop | null = null;

  /** Composition grid helper */
  private compositionGrid: THREE.Group | null = null;

  /** Dark overlay outside composition */
  private outsideOverlay: THREE.Mesh | null = null;

  /** Composition dimensions */
  private compositionWidth: number = 1920;
  private compositionHeight: number = 1080;

  /** O(1) layer lookup map - optimization for frequent ID-based lookups */
  private layerLookupMap: Map<string, THREE.Object3D> = new Map();

  /** Track Z positions to avoid unnecessary sorting */
  private zPositionCache: Map<THREE.Object3D, number> = new Map();
  private needsZSort: boolean = false;

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
  // Pattern match: backgroundColor ∈ string (empty string = transparent, never null)
  constructor(backgroundColor: string = "") {
    // Create main scene
    this.scene = new THREE.Scene();
    this.scene.name = "LatticeScene";

    // Set background
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    // Pattern match: backgroundColor ∈ string (empty string = transparent)
    if (backgroundColor.length > 0) {
      this.scene.background = new THREE.Color(backgroundColor);
    } else {
      // Three.js API contract: null means "transparent background"
      // This is the ONLY acceptable null assignment in this file (Three.js API requirement)
      this.scene.background = null;
    }

    // Create layer groups
    this.compositionGroup = new THREE.Group();
    this.compositionGroup.name = "composition";
    this.scene.add(this.compositionGroup);

    this.overlayGroup = new THREE.Group();
    this.overlayGroup.name = "overlay";
    this.overlayGroup.renderOrder = 1000; // Render on top
    this.scene.add(this.overlayGroup);

    this.debugGroup = new THREE.Group();
    this.debugGroup.name = "debug";
    this.debugGroup.visible = false;
    this.scene.add(this.debugGroup);

    // Add default lighting for 3D layers
    this.setupDefaultLighting();
  }

  /**
   * Set up default ambient and directional lighting
   */
  private setupDefaultLighting(): void {
    // Ambient light for base illumination
    const ambient = new THREE.AmbientLight(0xffffff, 0.6);
    ambient.name = "ambientLight";
    this.scene.add(ambient);

    // Key light (main directional)
    const keyLight = new THREE.DirectionalLight(0xffffff, 0.8);
    keyLight.name = "keyLight";
    keyLight.position.set(1000, -1000, 2000);
    keyLight.castShadow = true;
    keyLight.shadow.mapSize.width = 2048;
    keyLight.shadow.mapSize.height = 2048;
    this.scene.add(keyLight);

    // Fill light (softer, opposite side)
    const fillLight = new THREE.DirectionalLight(0xffffff, 0.3);
    fillLight.name = "fillLight";
    fillLight.position.set(-500, 500, 1000);
    this.scene.add(fillLight);
  }

  // ============================================================================
  // COMPOSITION MANAGEMENT
  // ============================================================================

  /**
   * Add object to composition group
   */
  addToComposition(object: THREE.Object3D): void {
    this.compositionGroup.add(object);
    this.markNeedsZSort(); // Mark for sorting instead of immediate sort

    // Update lookup map for O(1) access
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null/optional chaining
    // Pattern match: layerId ∈ string (empty string = no ID, never null)
    const layerId = (object.userData !== null && typeof object.userData === "object" && "layerId" in object.userData && typeof object.userData.layerId === "string" && object.userData.layerId.length > 0) ? object.userData.layerId : "";
    if (layerId.length > 0) {
      this.layerLookupMap.set(layerId, object);
    }
  }

  /**
   * Remove object from composition group
   */
  removeFromComposition(object: THREE.Object3D): void {
    this.compositionGroup.remove(object);

    // Remove from lookup map
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null/optional chaining
    // Pattern match: layerId ∈ string (empty string = no ID, never null)
    const layerId = (object.userData !== null && typeof object.userData === "object" && "layerId" in object.userData && typeof object.userData.layerId === "string" && object.userData.layerId.length > 0) ? object.userData.layerId : "";
    if (layerId.length > 0) {
      this.layerLookupMap.delete(layerId);
    }

    // Clean up Z position cache
    this.zPositionCache.delete(object);
  }

  /**
   * Sort composition layers by Z position for proper depth ordering
   * Optimized to only sort when Z positions have actually changed
   */
  sortByZ(): void {
    // Check if any Z positions have changed since last sort
    if (!this.needsZSort) {
      let hasChanges = false;
      for (const child of this.compositionGroup.children) {
        const cachedZ = this.zPositionCache.get(child);
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        // Pattern match: z coordinate ∈ number (always finite, never undefined)
        const safeCurrentZ: number = (typeof child.position.z === "number" && Number.isFinite(child.position.z)) ? child.position.z : 0;
        // Pattern match: Map.get() returns number | undefined, but we check explicitly
        const cachedZValue = (typeof cachedZ === "number" && Number.isFinite(cachedZ)) ? cachedZ : -Infinity;
        if (cachedZValue === -Infinity || cachedZValue !== safeCurrentZ) {
          hasChanges = true;
          break;
        }
      }
      if (!hasChanges) {
        return; // No Z changes, skip sorting
      }
    }

    // Perform the sort
    this.compositionGroup.children.sort((a, b) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: z coordinates ∈ number (coordinate-like, can be negative, never undefined)
      const zARaw = a.position.z;
      const zA: number = (typeof zARaw === "number" && Number.isFinite(zARaw)) ? zARaw : 0;
      const zBRaw = b.position.z;
      const zB: number = (typeof zBRaw === "number" && Number.isFinite(zBRaw)) ? zBRaw : 0;
      return zA - zB;
    });

    // Update the Z position cache
    for (const child of this.compositionGroup.children) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      // Pattern match: z coordinate ∈ number (coordinate-like, can be negative, never undefined)
      const zRaw = child.position.z;
      const z: number = (typeof zRaw === "number" && Number.isFinite(zRaw)) ? zRaw : 0;
      this.zPositionCache.set(child, z);
    }

    // Clear the dirty flag
    this.needsZSort = false;
  }

  /**
   * Mark that Z sorting is needed (call when Z positions may have changed)
   */
  markNeedsZSort(): void {
    this.needsZSort = true;
  }

  /**
   * Get all composition layer objects
   */
  getCompositionObjects(): THREE.Object3D[] {
    return [...this.compositionGroup.children];
  }

  // ============================================================================
  // OVERLAY MANAGEMENT
  // ============================================================================

  /**
   * Add object to overlay group
   */
  addToOverlay(object: THREE.Object3D): void {
    this.overlayGroup.add(object);
  }

  /**
   * Remove object from overlay group
   */
  removeFromOverlay(object: THREE.Object3D): void {
    this.overlayGroup.remove(object);
  }

  /**
   * Clear all overlay objects
   */
  clearOverlay(): void {
    while (this.overlayGroup.children.length > 0) {
      const child = this.overlayGroup.children[0];
      this.overlayGroup.remove(child);
      this.disposeObject(child);
    }
  }

  /**
   * Add a UI element directly to the scene (for transform controls, etc.)
   * UI elements are added to the scene root so they're always visible
   *
   * Note: When multiple Three.js instances are loaded (common in ComfyUI with many extensions),
   * the instanceof check in scene.add() can fail. We handle this by directly manipulating
   * the children array as a fallback.
   */
  addUIElement(object: THREE.Object3D): void {
    if (!object) return;

    // Check if the object passes instanceof (same Three.js instance)
    if (object instanceof THREE.Object3D) {
      this.scene.add(object);
      return;
    }

    // Object is from a different Three.js instance (common in ComfyUI
    // when model-viewer or other extensions load their own Three.js)
    // Try to make it work anyway by ensuring it has the required methods
    console.warn(
      "[SceneManager] UI element from different Three.js instance - attempting compatibility fix",
    );

    // Ensure the object has required methods by binding them from our THREE.Object3D
    // This is a compatibility shim for multi-Three.js environments
    // Type-safe interface defined at top of file
    // Runtime check: properties exist at runtime but may not be in TypeScript types
    const proto = THREE.Object3D.prototype;
    const obj = object as THREE.Object3D & CompatibleObject3D;

    // Patch missing methods if they don't exist or are from wrong prototype
    if (typeof obj.updateMatrixWorld !== "function") {
      obj.updateMatrixWorld = proto.updateMatrixWorld.bind(object);
    }
    if (typeof obj.updateWorldMatrix !== "function") {
      // Wrap to match optional parameter signature
      obj.updateWorldMatrix = (updateParents?: boolean, updateChildren?: boolean) => {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        // Pattern match: updateParents/updateChildren ∈ boolean | undefined → boolean (never check undefined)
        const updateParentsValue: boolean = (typeof updateParents === "boolean") ? updateParents : true;
        const updateChildrenValue: boolean = (typeof updateChildren === "boolean") ? updateChildren : true;
        proto.updateWorldMatrix.call(object, updateParentsValue, updateChildrenValue);
      };
    }

    // Recursively patch children
    if (obj.children && Array.isArray(obj.children)) {
      const patchChild = (child: CompatibleObject3D) => {
        if (typeof child.updateMatrixWorld !== "function") {
          child.updateMatrixWorld = proto.updateMatrixWorld.bind(child as THREE.Object3D);
        }
        if (typeof child.updateWorldMatrix !== "function") {
          // Wrap to match optional parameter signature
          child.updateWorldMatrix = (updateParents?: boolean, updateChildren?: boolean) => {
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
            // Pattern match: updateParents/updateChildren ∈ boolean | undefined → boolean (never check undefined)
            const updateParentsValue: boolean = (typeof updateParents === "boolean") ? updateParents : true;
            const updateChildrenValue: boolean = (typeof updateChildren === "boolean") ? updateChildren : true;
            proto.updateWorldMatrix.call(child as THREE.Object3D, updateParentsValue, updateChildrenValue);
          };
        }
        if (child.children) {
          child.children.forEach(patchChild);
        }
      };
      obj.children.forEach(patchChild);
    }

    // Force add to scene by temporarily spoofing the prototype
    try {
      // Manually add since scene.add() will reject it
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null/undefined checks
      // Pattern match: obj.parent ∈ CompatibleObject3D | null | undefined
      if (typeof obj.parent === "object" && obj.parent !== null && "remove" in obj.parent && typeof obj.parent.remove === "function") {
        obj.parent.remove(obj);
      }
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy type escapes
      // Pattern match: Force add to scene (cross-Three.js compatibility)
      // Type assertion needed because Scene expects Object3D but we have CompatibleObject3D
      // Note: Using type assertion here is acceptable for cross-Three.js compatibility shim
      // Pattern match: obj.parent accepts CompatibleObject3D | null, and Scene is compatible
      (obj as { parent?: CompatibleObject3D | null }).parent = this.scene as CompatibleObject3D;
      // Type guard: Ensure obj is compatible with THREE.Object3D before adding to scene
      // CompatibleObject3D has all required properties, so this is safe
      const objAsThree = obj as THREE.Object3D & CompatibleObject3D;
      this.scene.children.push(objAsThree);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      if ("dispatchEvent" in obj && typeof obj.dispatchEvent === "function") {
        obj.dispatchEvent({ type: "added" });
      }
      console.log(
        "[SceneManager] Successfully added UI element with compatibility shim",
      );
    } catch (error) {
      console.error("[SceneManager] Failed to add UI element:", error);
    }
  }

  /**
   * Remove a UI element from the scene
   */
  removeUIElement(object: THREE.Object3D): void {
    if (!object) return;

    // Try normal remove first
    const childCountBefore = this.scene.children.length;
    this.scene.remove(object);

    // If remove() failed, manually remove from children array
    // Type-safe handling for objects from different Three.js instances
    if (this.scene.children.length === childCountBefore) {
      const index = this.scene.children.indexOf(object);
      if (index !== -1) {
        this.scene.children.splice(index, 1);
        // Type-safe parent assignment for compatibility objects
        // Runtime check: parent property exists at runtime but may not be in TypeScript types
        const compatObj = object as THREE.Object3D & { parent?: THREE.Object3D | null };
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null assignments
            // Pattern match: Clear parent (Three.js API allows null for root objects)
            // Note: Three.js Object3D.parent can be null for root objects - this is API requirement
            compatObj.parent = null;
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        if ("dispatchEvent" in object && typeof object.dispatchEvent === "function") {
          object.dispatchEvent({ type: "removed" });
        }
      }
    }
  }

  /**
   * Prepare scene for render by ensuring all objects have required methods.
   * This handles cases where TransformControls or other UI elements from
   * different Three.js instances create new children dynamically.
   *
   * The Multiple Three.js instances issue occurs because ComfyUI extensions
   * may load their own Three.js, causing instanceof checks to fail and
   * internal structures (like children arrays) to be incompatible.
   */
  prepareForRender(): void {
      // NOTE: This function patches Three.js runtime objects, which are NOT JSON-serializable.
      // We use a permissive type here that allows Three.js objects (Matrix4, Layers, functions, etc.)
      // This is acceptable because these are internal runtime patches, not JSON data.
      type ThreeJSObjectPatch = THREE.Object3D & {
        matrix?: THREE.Matrix4;
        matrixWorld?: THREE.Matrix4;
        layers?: THREE.Layers;
        children?: THREE.Object3D[];
        updateMatrixWorld?: (force?: boolean) => void;
        updateMatrix?: () => void;
        matrixAutoUpdate?: boolean;
        matrixWorldAutoUpdate?: boolean;
        matrixWorldNeedsUpdate?: boolean;
        parent?: ThreeJSObjectPatch | null;
      };
      const ensureMethods = (obj: THREE.Object3D | RuntimeValue, depth = 0) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      // Safety check
      if ((typeof obj !== "object" || obj === null) || depth > 50) return;

      // Type guard: ensure obj is an object-like structure
      // Cast to ThreeJSObjectPatch to allow Three.js runtime objects
      const objAny = obj as unknown as ThreeJSObjectPatch;
      
      // CRITICAL: Ensure children is always an array
      // This fixes "Cannot read properties of undefined (reading 'length')"
      // when TransformControls from another Three.js instance creates gizmo parts
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined/null checks
      if (typeof objAny.children !== "object" || objAny.children === null || !Array.isArray(objAny.children)) {
        objAny.children = [];
      }

      // Ensure matrix properties exist
      if (!objAny.matrix) {
        objAny.matrix = new THREE.Matrix4();
      }
      if (!objAny.matrixWorld) {
        objAny.matrixWorld = new THREE.Matrix4();
      }

      // CRITICAL: Ensure layers property exists
      // This fixes "Cannot read properties of undefined (reading 'test')"
      // when Three.js calls camera.layers.test(object.layers) during render
      if (!objAny.layers) {
        objAny.layers = new THREE.Layers();
      }

      // Only patch updateMatrixWorld if it's missing
      // (TransformControls from our bundle should have it)
      if (typeof objAny.updateMatrixWorld !== "function") {
        objAny.updateMatrixWorld = function (this: ThreeJSObjectPatch, force?: boolean) {
          try {
            const self = this as ThreeJSObjectPatch;
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
            if (self.matrixAutoUpdate && "updateMatrix" in self && typeof self.updateMatrix === "function") {
              (self.updateMatrix as () => void)();
            }
            if (self.matrixWorldNeedsUpdate || force) {
              if (self.matrixWorldAutoUpdate !== false) {
                // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null checks
                // Pattern match: self.parent ∈ CompatibleObject3D | null | undefined
                const parentValue = self.parent;
                if (parentValue === null || (typeof parentValue !== "object")) {
                  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined/null checks
                  const matrixWorldValue = self.matrixWorld;
                  const matrixValue = self.matrix;
                  if (matrixWorldValue && matrixValue && typeof matrixWorldValue.copy === "function") {
                    matrixWorldValue.copy(matrixValue);
                  }
                } else {
                  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined/null checks
                  // Pattern match: parent is guaranteed to be object here (not null/undefined)
                  const parentObj = parentValue as unknown as ThreeJSObjectPatch;
                  const parentMatrixWorld = parentObj.matrixWorld;
                  const matrixWorld = self.matrixWorld;
                  const matrixValue = self.matrix;
                  if (parentMatrixWorld && matrixWorld && matrixValue && typeof matrixWorld.multiplyMatrices === "function") {
                    matrixWorld.multiplyMatrices(parentMatrixWorld, matrixValue);
                  }
                }
              }
              self.matrixWorldNeedsUpdate = false;
              force = true;
            }
            // Safe children iteration
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
            const children = self.children;
            if (Array.isArray(children)) {
              for (let i = 0; i < children.length; i++) {
                const child = children[i];
                if (
                  typeof child === "object" &&
                  child !== null &&
                  (child.matrixWorldAutoUpdate === true || force === true)
                ) {
                  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
                  const childRecord = child as unknown as ThreeJSObjectPatch;
                  const updateFn = childRecord.updateMatrixWorld;
                  if (typeof updateFn === "function") {
                    updateFn.call(childRecord, force);
                  }
                }
              }
            }
          } catch (_e) {
            // Silently ignore errors in cross-instance objects
          }
        };
      }

      // Recursively check children - process ALL objects, even if instanceof passes
      // because TransformControls creates children dynamically
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      const children = objAny.children;
      if (Array.isArray(children)) {
        for (let i = 0; i < children.length; i++) {
          ensureMethods(children[i], depth + 1);
        }
      }
    };

    // Check all scene children
    try {
      for (const child of this.scene.children) {
        ensureMethods(child, 0);
      }
    } catch (e) {
      console.warn("[SceneManager] Error in prepareForRender:", e);
    }
  }

  // ============================================================================
  // DEBUG HELPERS
  // ============================================================================

  /**
   * Toggle debug helpers visibility
   */
  setDebugVisible(visible: boolean): void {
    this.debugGroup.visible = visible;
  }

  /**
   * Add axis helper to debug group
   */
  addAxisHelper(size: number = 500): void {
    const existing = this.debugGroup.getObjectByName("axisHelper");
    if (existing) {
      this.debugGroup.remove(existing);
    }

    const helper = new THREE.AxesHelper(size);
    helper.name = "axisHelper";
    this.debugGroup.add(helper);
  }

  /**
   * Add grid helper to debug group
   */
  addGridHelper(size: number = 2000, divisions: number = 40): void {
    const existing = this.debugGroup.getObjectByName("gridHelper");
    if (existing) {
      this.debugGroup.remove(existing);
    }

    const helper = new THREE.GridHelper(size, divisions, 0x444444, 0x222222);
    helper.name = "gridHelper";
    helper.rotation.x = Math.PI / 2; // Rotate to XY plane
    this.debugGroup.add(helper);
  }

  // ============================================================================
  // BACKGROUND
  // ============================================================================

  /**
   * Set scene background color
   * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
   * Pattern match: color ∈ string (empty string = transparent, never null)
   */
  setBackground(color: string): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (color.length > 0) {
      this.scene.background = new THREE.Color(color);
    } else {
      // Three.js API contract: null means "transparent background"
      // This is the ONLY acceptable null assignment in this method (Three.js API requirement)
      this.scene.background = null;
    }
  }

  /**
   * Get current background color
   * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
   * Pattern match: Returns string (empty string = transparent, never null)
   */
  getBackground(): string {
    if (this.scene.background instanceof THREE.Color) {
      return `#${this.scene.background.getHexString()}`;
    }
    // Pattern match: No background = empty string (never null)
    return "";
  }

  // ============================================================================
  // ENVIRONMENT MAP (HDRI)
  // ============================================================================

  /**
   * Initialize PMREM generator (requires WebGL renderer)
   * Must be called before loading environment maps
   */
  initializeEnvironmentSupport(renderer: THREE.WebGLRenderer): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.pmremGenerator !== null && typeof this.pmremGenerator === "object" && "dispose" in this.pmremGenerator && typeof this.pmremGenerator.dispose === "function") {
      this.pmremGenerator.dispose();
    }
    this.pmremGenerator = new THREE.PMREMGenerator(renderer);
    this.pmremGenerator.compileEquirectangularShader();
  }

  /**
   * Load and set an environment map from URL (HDR, EXR, or standard image)
   * @param url - URL to the environment map file
   * @param config - Optional environment configuration
   */
  async loadEnvironmentMap(
    url: string,
    config?: Partial<EnvironmentMapConfig>,
  ): Promise<THREE.Texture> {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.pmremGenerator === null || typeof this.pmremGenerator !== "object") {
      throw new Error(
        "Environment support not initialized. Call initializeEnvironmentSupport() first.",
      );
    }

    // Update config
    if (config) {
      Object.assign(this.envConfig, config);
    }
    this.envConfig.url = url;
    this.envConfig.enabled = true;

    // Determine loader based on extension
    const isHDR = url.toLowerCase().endsWith(".hdr");
    const isEXR = url.toLowerCase().endsWith(".exr");

    return new Promise((resolve, reject) => {
      if (isHDR) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
        if (this.rgbeLoader === null || typeof this.rgbeLoader !== "object") {
          this.rgbeLoader = new RGBELoader();
        }
        this.rgbeLoader.load(
          url,
          (texture) => this.processEnvironmentTexture(texture, resolve),
          undefined,
          reject,
        );
      } else if (isEXR) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
        if (this.exrLoader === null || typeof this.exrLoader !== "object") {
          this.exrLoader = new EXRLoader();
        }
        this.exrLoader.load(
          url,
          (texture) => this.processEnvironmentTexture(texture, resolve),
          undefined,
          reject,
        );
      } else {
        // Standard image format (jpg, png)
        const loader = new THREE.TextureLoader();
        loader.load(
          url,
          (texture) => {
            texture.mapping = THREE.EquirectangularReflectionMapping;
            this.processEnvironmentTexture(texture, resolve);
          },
          undefined,
          reject,
        );
      }
    });
  }

  /**
   * Process loaded environment texture
   */
  private processEnvironmentTexture(
    texture: THREE.Texture,
    resolve: (tex: THREE.Texture) => void,
  ): void {
    // Generate PMREM from equirectangular texture
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
    // Pattern match: envMap ∈ THREE.Texture (use empty texture instead of null)
    let envMap: THREE.Texture;
    if (this.pmremGenerator !== null && typeof this.pmremGenerator === "object" && "fromEquirectangular" in this.pmremGenerator && typeof this.pmremGenerator.fromEquirectangular === "function") {
      envMap = this.pmremGenerator.fromEquirectangular(texture).texture;
    } else {
      // Pattern match: No PMREM generator = use empty texture (never null)
      envMap = new THREE.DataTexture(new Uint8Array([0, 0, 0, 0]), 1, 1);
    }
    texture.dispose();

    // Store and apply
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    // Pattern match: envMap is always defined (either PMREM texture or empty texture)
    this.setEnvironmentMapTexture(envMap);
    resolve(envMap);
  }

  /**
   * Set environment map from pre-loaded texture
   * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null
   * Pattern match: texture ∈ THREE.Texture (empty texture = no env map, never null)
   */
  setEnvironmentMapTexture(texture: THREE.Texture): void {
    // Dispose old environment map
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.environmentMap !== null && typeof this.environmentMap === "object" && this.environmentMap !== texture && "dispose" in this.environmentMap && typeof this.environmentMap.dispose === "function") {
      this.environmentMap.dispose();
    }

    // Pattern match: Check if texture is empty (1x1 black texture = sentinel)
    const isEmptyTexture = texture instanceof THREE.DataTexture && texture.image.width === 1 && texture.image.height === 1;
    
    if (!isEmptyTexture) {
      this.environmentMap = texture;
      
      if (this.envConfig.enabled) {
        // Set as scene environment for reflections
        this.scene.environment = texture;

        // Set as background if configured
        if (this.envConfig.useAsBackground) {
          this.scene.background = texture;
          this.scene.backgroundIntensity = this.envConfig.intensity;
          this.scene.backgroundBlurriness = this.envConfig.backgroundBlur;
          this.scene.backgroundRotation.y =
            this.envConfig.rotation * (Math.PI / 180);
        }

        // Set environment intensity and rotation
        this.scene.environmentIntensity = this.envConfig.intensity;
        this.scene.environmentRotation.y =
          this.envConfig.rotation * (Math.PI / 180);
      } else {
        // Three.js API contract: null means "no environment map"
        // This is the ONLY acceptable null assignment in this method (Three.js API requirement)
        this.scene.environment = null;
        if (this.envConfig.useAsBackground) {
          this.scene.background = null;
        }
      }
    } else {
      // Pattern match: Empty texture = clear environment map
      // Three.js API contract: null means "no environment map"
      // This is the ONLY acceptable null assignment in this method (Three.js API requirement)
      this.environmentMap = null;
      this.scene.environment = null;
      if (this.envConfig.useAsBackground) {
        this.scene.background = null;
      }
    }
  }

  /**
   * Update environment map configuration
   */
  setEnvironmentConfig(config: Partial<EnvironmentMapConfig>): void {
    Object.assign(this.envConfig, config);

    // Apply changes
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.environmentMap !== null && typeof this.environmentMap === "object") {
      if (this.envConfig.enabled) {
        this.scene.environment = this.environmentMap;
        this.scene.environmentIntensity = this.envConfig.intensity;
        this.scene.environmentRotation.y =
          this.envConfig.rotation * (Math.PI / 180);

        if (this.envConfig.useAsBackground) {
          this.scene.background = this.environmentMap;
          this.scene.backgroundIntensity = this.envConfig.intensity;
          this.scene.backgroundBlurriness = this.envConfig.backgroundBlur;
          this.scene.backgroundRotation.y =
            this.envConfig.rotation * (Math.PI / 180);
        }
      } else {
        this.scene.environment = null;
        if (this.envConfig.useAsBackground) {
          this.scene.background = null;
        }
      }
    }
  }

  /**
   * Get current environment map configuration
   */
  getEnvironmentConfig(): EnvironmentMapConfig {
    return { ...this.envConfig };
  }

  /**
   * Get current environment map texture
   */
  getEnvironmentMap(): THREE.Texture | null {
    return this.environmentMap;
  }

  /**
   * Enable or disable environment map
   */
  setEnvironmentEnabled(enabled: boolean): void {
    this.setEnvironmentConfig({ enabled });
  }

  /**
   * Set environment intensity
   */
  setEnvironmentIntensity(intensity: number): void {
    this.setEnvironmentConfig({ intensity });
  }

  /**
   * Set environment rotation (degrees)
   */
  setEnvironmentRotation(rotation: number): void {
    this.setEnvironmentConfig({ rotation });
  }

  /**
   * Set background blur amount (0-1)
   */
  setBackgroundBlur(blur: number): void {
    this.setEnvironmentConfig({ backgroundBlur: blur });
  }

  /**
   * Toggle using HDRI as background
   */
  setUseAsBackground(use: boolean): void {
    this.setEnvironmentConfig({ useAsBackground: use });
  }

  // ============================================================================
  // COMPOSITION BOUNDS
  // ============================================================================

  /**
   * Set composition dimensions and create/update bounds frame
   */
  setCompositionSize(width: number, height: number): void {
    this.compositionWidth = width;
    this.compositionHeight = height;
    this.updateCompositionBounds();
    this.updateCompositionGrid();
    this.updateOutsideOverlay();
  }

  /**
   * Get composition dimensions
   */
  getCompositionSize(): { width: number; height: number } {
    return { width: this.compositionWidth, height: this.compositionHeight };
  }

  /**
   * Create or update composition bounds frame
   */
  private updateCompositionBounds(): void {
    // Remove existing bounds
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.compositionBounds !== null && typeof this.compositionBounds === "object") {
      this.overlayGroup.remove(this.compositionBounds);
      this.compositionBounds.geometry.dispose();
      (this.compositionBounds.material as THREE.Material).dispose();
    }

    const w = this.compositionWidth;
    const h = this.compositionHeight;

    // Create rectangle points (in screen space, Y negated)
    const points = [
      new THREE.Vector3(0, 0, 0),
      new THREE.Vector3(w, 0, 0),
      new THREE.Vector3(w, -h, 0),
      new THREE.Vector3(0, -h, 0),
    ];

    const geometry = new THREE.BufferGeometry().setFromPoints(points);
    const material = new THREE.LineBasicMaterial({
      color: 0x4a90d9,
      linewidth: 2,
      depthTest: false,
    });

    this.compositionBounds = new THREE.LineLoop(geometry, material);
    this.compositionBounds.name = "compositionBounds";
    this.compositionBounds.renderOrder = 998;
    this.overlayGroup.add(this.compositionBounds);
  }

  /**
   * Show/hide composition bounds
   */
  setCompositionBoundsVisible(visible: boolean): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.compositionBounds !== null && typeof this.compositionBounds === "object") {
      this.compositionBounds.visible = visible;
    }
  }

  /**
   * Create or update composition grid
   * Shows a grid inside the composition area for spatial reference
   */
  updateCompositionGrid(divisions: number = 20): void {
    try {
      // Remove existing grid
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (this.compositionGrid !== null && typeof this.compositionGrid === "object") {
        this.overlayGroup.remove(this.compositionGrid);
        this.compositionGrid.traverse((obj) => {
          if (obj instanceof THREE.Line) {
            obj.geometry.dispose();
            (obj.material as THREE.Material).dispose();
          }
        });
      }

      const w = this.compositionWidth;
      const h = this.compositionHeight;
      const gridGroup = new THREE.Group();
      gridGroup.name = "compositionGrid";

      const material = new THREE.LineBasicMaterial({
        color: 0x333333,
        transparent: true,
        opacity: 0.5,
        depthTest: false,
      });

      // Vertical lines - grid at z=0 (composition plane)
      const stepX = w / divisions;
      for (let i = 0; i <= divisions; i++) {
        const x = i * stepX;
        const points = [
          new THREE.Vector3(x, 0, 0),
          new THREE.Vector3(x, -h, 0),
        ];
        const geometry = new THREE.BufferGeometry().setFromPoints(points);
        const line = new THREE.Line(geometry, material.clone());
        gridGroup.add(line);
      }

      // Horizontal lines
      const stepY = h / divisions;
      for (let i = 0; i <= divisions; i++) {
        const y = -i * stepY;
        const points = [new THREE.Vector3(0, y, 0), new THREE.Vector3(w, y, 0)];
        const geometry = new THREE.BufferGeometry().setFromPoints(points);
        const line = new THREE.Line(geometry, material.clone());
        gridGroup.add(line);
      }

      // Center crosshair and XYZ axes at composition center
      // This is where 3D objects with anchor (0,0,0) should appear
      const centerX = w / 2;
      const centerY = -h / 2;
      const axisLength = Math.min(w, h) / 4; // Proportional axis length

      // X axis (red) - horizontal from center
      const xAxisMaterial = new THREE.LineBasicMaterial({
        color: 0xff4444,
        transparent: true,
        opacity: 0.9,
        depthTest: false,
        linewidth: 2,
      });
      const xAxisPoints = [
        new THREE.Vector3(centerX, centerY, 0),
        new THREE.Vector3(centerX + axisLength, centerY, 0),
      ];
      const xAxisGeom = new THREE.BufferGeometry().setFromPoints(xAxisPoints);
      gridGroup.add(new THREE.Line(xAxisGeom, xAxisMaterial));

      // Y axis (green) - vertical from center (up is positive)
      const yAxisMaterial = new THREE.LineBasicMaterial({
        color: 0x44ff44,
        transparent: true,
        opacity: 0.9,
        depthTest: false,
        linewidth: 2,
      });
      const yAxisPoints = [
        new THREE.Vector3(centerX, centerY, 0),
        new THREE.Vector3(centerX, centerY + axisLength, 0),
      ];
      const yAxisGeom = new THREE.BufferGeometry().setFromPoints(yAxisPoints);
      gridGroup.add(new THREE.Line(yAxisGeom, yAxisMaterial));

      // Z axis (blue) - depth from center (toward camera)
      const zAxisMaterial = new THREE.LineBasicMaterial({
        color: 0x4444ff,
        transparent: true,
        opacity: 0.9,
        depthTest: false,
        linewidth: 2,
      });
      const zAxisPoints = [
        new THREE.Vector3(centerX, centerY, 0),
        new THREE.Vector3(centerX, centerY, axisLength),
      ];
      const zAxisGeom = new THREE.BufferGeometry().setFromPoints(zAxisPoints);
      gridGroup.add(new THREE.Line(zAxisGeom, zAxisMaterial));

      // Origin marker (white dot at center) - use Line instead of Mesh for compatibility
      try {
        const originMarkerGeom = new THREE.SphereGeometry(4, 8, 8);
        const originMarkerMat = new THREE.MeshBasicMaterial({
          color: 0xffffff,
          transparent: true,
          opacity: 0.8,
          depthTest: false,
        });
        const originMarker = new THREE.Mesh(originMarkerGeom, originMarkerMat);
        originMarker.position.set(centerX, centerY, 0);
        originMarker.renderOrder = 998;
        gridGroup.add(originMarker);
      } catch (_meshError) {
        // Mesh creation failed (likely Three.js multi-instance conflict)
        // Fall back to a simple crosshair at the origin
        console.warn(
          "[SceneManager] Could not create origin marker mesh, using crosshair fallback",
        );
        const crossSize = 8;
        const crossMat = new THREE.LineBasicMaterial({
          color: 0xffffff,
          depthTest: false,
        });
        const crossH = new THREE.BufferGeometry().setFromPoints([
          new THREE.Vector3(centerX - crossSize, centerY, 0),
          new THREE.Vector3(centerX + crossSize, centerY, 0),
        ]);
        const crossV = new THREE.BufferGeometry().setFromPoints([
          new THREE.Vector3(centerX, centerY - crossSize, 0),
          new THREE.Vector3(centerX, centerY + crossSize, 0),
        ]);
        gridGroup.add(new THREE.Line(crossH, crossMat));
        gridGroup.add(new THREE.Line(crossV, crossMat.clone()));
      }

      // Subtle center crosshair lines (dimmer than axes)
      const centerMaterial = new THREE.LineBasicMaterial({
        color: 0x555555,
        transparent: true,
        opacity: 0.5,
        depthTest: false,
      });

      // Vertical center line (full height)
      const vCenterPoints = [
        new THREE.Vector3(centerX, 0, 0),
        new THREE.Vector3(centerX, -h, 0),
      ];
      const vCenterGeom = new THREE.BufferGeometry().setFromPoints(
        vCenterPoints,
      );
      gridGroup.add(new THREE.Line(vCenterGeom, centerMaterial));

      // Horizontal center line (full width)
      const hCenterPoints = [
        new THREE.Vector3(0, centerY, 0),
        new THREE.Vector3(w, centerY, 0),
      ];
      const hCenterGeom = new THREE.BufferGeometry().setFromPoints(
        hCenterPoints,
      );
      gridGroup.add(new THREE.Line(hCenterGeom, centerMaterial.clone()));

      gridGroup.renderOrder = 997;
      this.compositionGrid = gridGroup;
      this.overlayGroup.add(gridGroup);
    } catch (error) {
      console.warn("[SceneManager] Failed to create composition grid:", error);
      // Grid is not critical for functionality, continue without it
    }
  }

  /**
   * Show/hide composition grid
   */
  setCompositionGridVisible(visible: boolean): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.compositionGrid !== null && typeof this.compositionGrid === "object") {
      this.compositionGrid.visible = visible;
    }
  }

  /**
   * Create dark overlay outside composition bounds
   * Creates a large plane with a rectangular hole for the composition area
   */
  updateOutsideOverlay(): void {
    try {
      // Remove existing overlay
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (this.outsideOverlay !== null && typeof this.outsideOverlay === "object") {
        this.overlayGroup.remove(this.outsideOverlay);
        this.outsideOverlay.geometry.dispose();
        (this.outsideOverlay.material as THREE.Material).dispose();
      }

      const w = this.compositionWidth;
      const h = this.compositionHeight;

      // Create a large plane with a hole using ShapeGeometry
      const size = Math.max(w, h) * 10; // Large enough to cover viewport

      // Outer shape (large rectangle)
      const outer = new THREE.Shape();
      outer.moveTo(-size, size);
      outer.lineTo(size + w, size);
      outer.lineTo(size + w, -size - h);
      outer.lineTo(-size, -size - h);
      outer.lineTo(-size, size);

      // Inner hole (composition bounds) - wind in opposite direction
      const hole = new THREE.Path();
      hole.moveTo(0, 0);
      hole.lineTo(0, -h);
      hole.lineTo(w, -h);
      hole.lineTo(w, 0);
      hole.lineTo(0, 0);

      outer.holes.push(hole);

      const geometry = new THREE.ShapeGeometry(outer);
      const material = new THREE.MeshBasicMaterial({
        color: 0x000000,
        transparent: true,
        opacity: 0.6,
        side: THREE.DoubleSide,
        depthTest: false,
      });

      this.outsideOverlay = new THREE.Mesh(geometry, material);
      this.outsideOverlay.name = "outsideOverlay";
      this.outsideOverlay.position.z = -2; // Behind composition but in front of far background
      this.outsideOverlay.renderOrder = 996;
      this.overlayGroup.add(this.outsideOverlay);
    } catch (error) {
      console.warn("[SceneManager] Failed to create outside overlay:", error);
      // Overlay is not critical for functionality, continue without it
    }
  }

  /**
   * Show/hide outside overlay
   */
  setOutsideOverlayVisible(visible: boolean): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.outsideOverlay !== null && typeof this.outsideOverlay === "object") {
      this.outsideOverlay.visible = visible;
    }
  }

  // ============================================================================
  // RAYCASTING
  // ============================================================================

  /**
   * Raycast against composition objects
   */
  raycastComposition(
    raycaster: THREE.Raycaster,
  ): THREE.Intersection<THREE.Object3D>[] {
    return raycaster.intersectObjects(this.compositionGroup.children, true);
  }

  /**
   * Find layer object by ID - O(1) lookup via Map
   * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
   * Pattern match: Returns THREE.Object3D (throws error if not found, never null)
   */
  findLayerById(layerId: string): THREE.Object3D {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    // Pattern match: Map.get() returns THREE.Object3D | undefined
    const layer = this.layerLookupMap.get(layerId);
    if (typeof layer === "object" && layer !== null) {
      return layer;
    }
    // Pattern match: Layer not found - throw error instead of returning null
    throw new Error(`Layer with ID "${layerId}" not found in scene`);
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  /**
   * Dispose object and its resources
   */
  private disposeObject(object: THREE.Object3D): void {
    if (object instanceof THREE.Mesh) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      if ("geometry" in object && object.geometry !== null && typeof object.geometry === "object" && "dispose" in object.geometry && typeof object.geometry.dispose === "function") {
        object.geometry.dispose();
      }

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      if (Array.isArray(object.material)) {
        object.material.forEach((m) => {
          this.disposeMaterial(m);
        });
      } else if (object.material !== null && typeof object.material === "object") {
        this.disposeMaterial(object.material);
      }
    }

    // Recursively dispose children
    while (object.children.length > 0) {
      const child = object.children[0];
      object.remove(child);
      this.disposeObject(child);
    }
  }

  /**
   * Dispose material and its textures
   */
  private disposeMaterial(material: THREE.Material): void {
    // Dispose textures
    const mat = material as THREE.MeshStandardMaterial;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    const disposeMap = (map: RuntimeValue) => {
      if (map !== null && typeof map === "object" && "dispose" in map && typeof map.dispose === "function") {
        map.dispose();
      }
    };
    disposeMap(mat.map);
    disposeMap(mat.normalMap);
    disposeMap(mat.roughnessMap);
    disposeMap(mat.metalnessMap);
    disposeMap(mat.aoMap);
    disposeMap(mat.emissiveMap);
    disposeMap(mat.alphaMap);
    disposeMap(mat.envMap);

    material.dispose();
  }

  /**
   * Dispose all scene resources
   */
  dispose(): void {
    // Dispose composition
    while (this.compositionGroup.children.length > 0) {
      const child = this.compositionGroup.children[0];
      this.compositionGroup.remove(child);
      this.disposeObject(child);
    }

    // Clear lookup map and Z cache
    this.layerLookupMap.clear();
    this.zPositionCache.clear();

    // Dispose overlay
    this.clearOverlay();

    // Dispose debug
    while (this.debugGroup.children.length > 0) {
      const child = this.debugGroup.children[0];
      this.debugGroup.remove(child);
      this.disposeObject(child);
    }

    // Dispose environment map resources
    if (this.environmentMap) {
      this.environmentMap.dispose();
      this.environmentMap = null;
    }
    if (this.pmremGenerator) {
      this.pmremGenerator.dispose();
      this.pmremGenerator = null;
    }

    // Clear scene
    this.scene.clear();
  }
}
