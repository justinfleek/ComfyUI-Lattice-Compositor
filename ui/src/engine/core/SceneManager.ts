/**
 * SceneManager - Three.js Scene Management
 *
 * Manages the Three.js scene graph with separate groups for:
 * - Composition layers (main content)
 * - Overlay elements (gizmos, guides, selection)
 * - Debug helpers (axis, grid)
 */

import * as THREE from 'three';

export class SceneManager {
  /** The main Three.js scene */
  public readonly scene: THREE.Scene;

  /** Group for composition layers (rendered content) */
  public readonly compositionGroup: THREE.Group;

  /** Group for UI overlay elements */
  public readonly overlayGroup: THREE.Group;

  /** Group for debug helpers */
  public readonly debugGroup: THREE.Group;

  /** Composition bounds frame */
  private compositionBounds: THREE.LineLoop | null = null;

  /** Composition dimensions */
  private compositionWidth: number = 1920;
  private compositionHeight: number = 1080;

  /** O(1) layer lookup map - optimization for frequent ID-based lookups */
  private layerLookupMap: Map<string, THREE.Object3D> = new Map();

  /** Track Z positions to avoid unnecessary sorting */
  private zPositionCache: Map<THREE.Object3D, number> = new Map();
  private needsZSort: boolean = false;

  constructor(backgroundColor: string | null = null) {
    // Create main scene
    this.scene = new THREE.Scene();
    this.scene.name = 'WeylScene';

    // Set background
    if (backgroundColor) {
      this.scene.background = new THREE.Color(backgroundColor);
    } else {
      this.scene.background = null; // Transparent
    }

    // Create layer groups
    this.compositionGroup = new THREE.Group();
    this.compositionGroup.name = 'composition';
    this.scene.add(this.compositionGroup);

    this.overlayGroup = new THREE.Group();
    this.overlayGroup.name = 'overlay';
    this.overlayGroup.renderOrder = 1000; // Render on top
    this.scene.add(this.overlayGroup);

    this.debugGroup = new THREE.Group();
    this.debugGroup.name = 'debug';
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
    ambient.name = 'ambientLight';
    this.scene.add(ambient);

    // Key light (main directional)
    const keyLight = new THREE.DirectionalLight(0xffffff, 0.8);
    keyLight.name = 'keyLight';
    keyLight.position.set(1000, -1000, 2000);
    keyLight.castShadow = true;
    keyLight.shadow.mapSize.width = 2048;
    keyLight.shadow.mapSize.height = 2048;
    this.scene.add(keyLight);

    // Fill light (softer, opposite side)
    const fillLight = new THREE.DirectionalLight(0xffffff, 0.3);
    fillLight.name = 'fillLight';
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
    const layerId = object.userData?.layerId;
    if (layerId) {
      this.layerLookupMap.set(layerId, object);
    }
  }

  /**
   * Remove object from composition group
   */
  removeFromComposition(object: THREE.Object3D): void {
    this.compositionGroup.remove(object);

    // Remove from lookup map
    const layerId = object.userData?.layerId;
    if (layerId) {
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
        const currentZ = child.position.z || 0;
        if (cachedZ === undefined || cachedZ !== currentZ) {
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
      return (a.position.z || 0) - (b.position.z || 0);
    });

    // Update the Z position cache
    for (const child of this.compositionGroup.children) {
      this.zPositionCache.set(child, child.position.z || 0);
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
   */
  addUIElement(object: THREE.Object3D): void {
    this.scene.add(object);
  }

  /**
   * Remove a UI element from the scene
   */
  removeUIElement(object: THREE.Object3D): void {
    this.scene.remove(object);
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
    const existing = this.debugGroup.getObjectByName('axisHelper');
    if (existing) {
      this.debugGroup.remove(existing);
    }

    const helper = new THREE.AxesHelper(size);
    helper.name = 'axisHelper';
    this.debugGroup.add(helper);
  }

  /**
   * Add grid helper to debug group
   */
  addGridHelper(size: number = 2000, divisions: number = 40): void {
    const existing = this.debugGroup.getObjectByName('gridHelper');
    if (existing) {
      this.debugGroup.remove(existing);
    }

    const helper = new THREE.GridHelper(size, divisions, 0x444444, 0x222222);
    helper.name = 'gridHelper';
    helper.rotation.x = Math.PI / 2; // Rotate to XY plane
    this.debugGroup.add(helper);
  }

  // ============================================================================
  // BACKGROUND
  // ============================================================================

  /**
   * Set scene background color
   */
  setBackground(color: string | null): void {
    if (color) {
      this.scene.background = new THREE.Color(color);
    } else {
      this.scene.background = null;
    }
  }

  /**
   * Get current background color
   */
  getBackground(): string | null {
    if (this.scene.background instanceof THREE.Color) {
      return '#' + this.scene.background.getHexString();
    }
    return null;
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
    if (this.compositionBounds) {
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
    this.compositionBounds.name = 'compositionBounds';
    this.compositionBounds.renderOrder = 998;
    this.overlayGroup.add(this.compositionBounds);
  }

  /**
   * Show/hide composition bounds
   */
  setCompositionBoundsVisible(visible: boolean): void {
    if (this.compositionBounds) {
      this.compositionBounds.visible = visible;
    }
  }

  // ============================================================================
  // RAYCASTING
  // ============================================================================

  /**
   * Raycast against composition objects
   */
  raycastComposition(
    raycaster: THREE.Raycaster
  ): THREE.Intersection<THREE.Object3D>[] {
    return raycaster.intersectObjects(this.compositionGroup.children, true);
  }

  /**
   * Find layer object by ID - O(1) lookup via Map
   */
  findLayerById(layerId: string): THREE.Object3D | null {
    return this.layerLookupMap.get(layerId) ?? null;
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  /**
   * Dispose object and its resources
   */
  private disposeObject(object: THREE.Object3D): void {
    if (object instanceof THREE.Mesh) {
      object.geometry?.dispose();

      if (Array.isArray(object.material)) {
        object.material.forEach(m => {
          this.disposeMaterial(m);
        });
      } else if (object.material) {
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
    mat.map?.dispose();
    mat.normalMap?.dispose();
    mat.roughnessMap?.dispose();
    mat.metalnessMap?.dispose();
    mat.aoMap?.dispose();
    mat.emissiveMap?.dispose();
    mat.alphaMap?.dispose();
    mat.envMap?.dispose();

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

    // Clear scene
    this.scene.clear();
  }
}
