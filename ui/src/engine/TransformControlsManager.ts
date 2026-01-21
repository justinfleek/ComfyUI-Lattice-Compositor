/**
 * Transform Controls Manager
 *
 * Extracted from LatticeEngine.ts - handles layer manipulation via
 * Three.js TransformControls (translate, rotate, scale gizmos).
 *
 * Features:
 * - Layer selection and gizmo attachment
 * - Transform mode switching (translate/rotate/scale)
 * - Multi-Three.js instance compatibility
 * - Transform change callbacks for store updates
 */

import * as THREE from "three";
import { TransformControls } from "three/examples/jsm/controls/TransformControls.js";
import type { JSONValue } from "@/types/dataAsset";
import type { CameraController } from "./core/CameraController";
import type { LayerManager } from "./core/LayerManager";
import type { RenderPipeline } from "./core/RenderPipeline";
import type { SceneManager } from "./core/SceneManager";

// ============================================================================
// TYPE EXTENSIONS FOR THREE.JS COMPATIBILITY
// ============================================================================

/**
 * Extended Object3D interface for compatibility with objects from different Three.js instances
 * These properties exist at runtime but may not pass instanceof checks
 */
interface CompatibleObject3D {
  children?: THREE.Object3D[];
  matrix?: THREE.Matrix4;
  matrixWorld?: THREE.Matrix4;
}

/**
 * Extended TransformControls interface with visible property
 * TransformControls has visible property at runtime but TypeScript types may not expose it
 */
interface TransformControlsWithVisible extends TransformControls {
  visible?: boolean;
}

/** Layer transform update from TransformControls manipulation */
export interface LayerTransformUpdate {
  position?: { x: number; y: number; z?: number };
  rotation?: number; // Z rotation in degrees
  rotationX?: number;
  rotationY?: number;
  rotationZ?: number;
  scale?: { x: number; y: number; z?: number };
}

export type TransformMode = "translate" | "rotate" | "scale";

export interface TransformControlsManagerDeps {
  scene: SceneManager;
  layers: LayerManager;
  camera: CameraController;
  renderer: RenderPipeline;
  emit: (type: string, data?: JSONValue) => void;
  getLayerObject: (layerId: string) => THREE.Object3D | null;
  resetOrbitTargetToCenter: () => void;
  setOrbitTarget: (x: number, y: number, z: number) => void;
}

export class TransformControlsManager {
  private transformControls: TransformControls | null = null;
  private selectedLayerId: string | null = null;
  private transformMode: TransformMode = "translate";
  private onTransformChange:
    | ((layerId: string, transform: LayerTransformUpdate) => void)
    | null = null;

  constructor(private readonly deps: TransformControlsManagerDeps) {}

  /**
   * Recursively ensure all objects in the hierarchy have proper children arrays
   * This is needed to prevent crashes when TransformControls or other objects
   * from different Three.js instances are added to the scene.
   */
  private ensureObjectChildren(obj: THREE.Object3D, depth = 0): void {
    if (!obj || depth > 50) return;

    // Type-safe access for compatibility objects
    // CompatibleObject3D interface defined at top of file
    // Runtime check: properties exist at runtime but may not be in TypeScript types
    const compatObj = obj as THREE.Object3D & CompatibleObject3D;

    // Ensure children is an array
    if (compatObj.children === undefined || compatObj.children === null) {
      compatObj.children = [];
    }

    // Ensure matrix properties exist
    if (!compatObj.matrix) {
      compatObj.matrix = new THREE.Matrix4();
    }
    if (!compatObj.matrixWorld) {
      compatObj.matrixWorld = new THREE.Matrix4();
    }

    // Recursively process children
    const children = compatObj.children;
    if (Array.isArray(children)) {
      for (const child of children) {
        this.ensureObjectChildren(child, depth + 1);
      }
    }
  }

  /**
   * Initialize transform controls for layer manipulation
   * Wrapped in try-catch for multi-Three.js instance compatibility
   */
  initialize(): void {
    if (this.transformControls) {
      return; // Already initialized
    }

    try {
      const camera = this.deps.camera.getCamera();
      const domElement = this.deps.renderer.getDomElement();

      this.transformControls = new TransformControls(camera, domElement);
      this.transformControls.setMode(this.transformMode);
      this.transformControls.setSpace("world");

      // Style the controls
      this.transformControls.setSize(1.0);

      // Ensure all gizmo objects have proper children arrays
      // (fixes multi-Three.js instance issues)
      // TransformControls extends Object3D internally but TypeScript types may not reflect this
      // System F/Omega: Use `as unknown as` for intentional conversions when runtime supports it
      this.ensureObjectChildren(
        this.transformControls as unknown as THREE.Object3D,
      );

      // Add to scene (TransformControls extends Object3D internally)
      this.deps.scene.addUIElement(
        this.transformControls as unknown as THREE.Object3D,
      );
    } catch (e) {
      console.error("[TransformControlsManager] Failed to initialize:", e);
      this.transformControls = null;
      return;
    }

    // Track if we're actively dragging (to avoid spurious updates on selection)
    let isDragging = false;

    // Disable orbit/pan during transform and track dragging state
    this.transformControls.addEventListener(
      "dragging-changed",
      (event: { value: boolean }) => {
        isDragging = event.value;
        this.deps.emit("transform-dragging", { dragging: event.value });
      },
    );

    // Handle transform changes - ONLY when actually dragging
    this.transformControls.addEventListener("change", () => {
      // Only fire callback during actual drag operations, not on selection/attach
      if (!isDragging) return;
      if (!this.transformControls || !this.selectedLayerId) return;

      const object = this.transformControls.object;
      if (!object) return;

      // Get the layer to access anchor point
      const layer = this.deps.layers.getLayer(this.selectedLayerId);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const getLayerData = (layer != null && typeof layer === "object" && typeof layer.getLayerData === "function") ? layer.getLayerData : undefined;
      const layerData = getLayerData != null ? getLayerData() : undefined;
      const transform = (layerData != null && typeof layerData === "object" && "transform" in layerData && layerData.transform != null && typeof layerData.transform === "object") ? layerData.transform : undefined;
      const anchorPoint = (transform != null && typeof transform === "object" && "anchorPoint" in transform && transform.anchorPoint != null && typeof transform.anchorPoint === "object") ? transform.anchorPoint : undefined;
      const anchorPointValue = (anchorPoint != null && typeof anchorPoint === "object" && "value" in anchorPoint && anchorPoint.value != null && typeof anchorPoint.value === "object") ? anchorPoint.value : undefined;
      // Type-safe access - anchorPoint.value is { x: number; y: number; z?: number }
      const anchorX = (typeof anchorPointValue === "object" && anchorPointValue !== null && "x" in anchorPointValue) ? anchorPointValue.x : 0;
      const anchorY = (typeof anchorPointValue === "object" && anchorPointValue !== null && "y" in anchorPointValue) ? anchorPointValue.y : 0;
      const anchorZ = (typeof anchorPointValue === "object" && anchorPointValue !== null && "z" in anchorPointValue) ? anchorPointValue.z : 0;

      // Convert 3D position back to layer position by adding anchor point back
      // The 3D object position is offset by anchor point in applyTransform()
      const transform: LayerTransformUpdate = {
        position: {
          x: object.position.x + anchorX,
          y: -object.position.y + anchorY, // Y is negated in 3D space
          z: object.position.z + anchorZ,
        },
        rotationX: THREE.MathUtils.radToDeg(object.rotation.x),
        rotationY: THREE.MathUtils.radToDeg(object.rotation.y),
        rotationZ: THREE.MathUtils.radToDeg(object.rotation.z),
        scale: {
          x: object.scale.x * 100, // Convert back to percentage
          y: object.scale.y * 100,
          z: object.scale.z * 100,
        },
      };

      // Also set rotation for 2D layers
      transform.rotation = transform.rotationZ;

      if (this.onTransformChange) {
        this.onTransformChange(this.selectedLayerId, transform);
      }
    });

    // Handle mouseup to finalize transform
    this.transformControls.addEventListener("mouseUp", () => {
      this.deps.emit("transform-end", { layerId: this.selectedLayerId });
    });
  }

  /**
   * Set transform change callback
   * Called whenever a layer is transformed via the controls
   */
  setTransformChangeCallback(
    callback:
      | ((layerId: string, transform: LayerTransformUpdate) => void)
      | null,
  ): void {
    this.onTransformChange = callback;
  }

  /**
   * Select a layer and attach transform controls
   * @param layerId - Layer ID to select, or null to deselect
   */
  selectLayer(layerId: string | null): void {
    // Initialize transform controls if not already done
    if (!this.transformControls) {
      this.initialize();
    }

    // Deselect current layer - wrap in try-catch for multi-Three.js compatibility
    if (this.selectedLayerId && this.transformControls) {
      try {
        this.transformControls.detach();
      } catch (e) {
        console.warn("[TransformControlsManager] detach error:", e);
      }
    }

    this.selectedLayerId = layerId;

    if (!layerId || !this.transformControls) {
      // No layer selected - reset orbit target to composition center
      this.deps.resetOrbitTargetToCenter();
      return;
    }

    // Get the layer object and attach - wrap in try-catch for multi-Three.js compatibility
    const layerObject = this.deps.getLayerObject(layerId);
    if (layerObject) {
      try {
        this.transformControls.attach(layerObject);
      } catch (e) {
        console.warn("[TransformControlsManager] attach error:", e);
      }
    }
  }

  /**
   * Focus the camera on a layer's position
   * This moves the orbit target to the layer without changing camera rotation
   */
  focusOnLayer(layerId: string): void {
    const layerObject = this.deps.getLayerObject(layerId);
    if (layerObject) {
      const worldPos = new THREE.Vector3();
      layerObject.getWorldPosition(worldPos);
      // Convert back to screen coordinates (negate Y)
      this.deps.setOrbitTarget(worldPos.x, -worldPos.y, worldPos.z);
    }
  }

  /**
   * Get the currently selected layer ID
   */
  getSelectedLayerId(): string | null {
    return this.selectedLayerId;
  }

  /**
   * Set the transform mode
   * @param mode - 'translate' | 'rotate' | 'scale'
   */
  setMode(mode: TransformMode): void {
    this.transformMode = mode;
    if (this.transformControls) {
      this.transformControls.setMode(mode);
    }
  }

  /**
   * Get the current transform mode
   */
  getMode(): TransformMode {
    return this.transformMode;
  }

  /**
   * Set transform controls visibility
   */
  setVisible(visible: boolean): void {
    if (this.transformControls) {
      // Type-safe access to visible property
      // TransformControlsWithVisible interface defined at top of file
      const controlsWithVisible = this.transformControls as TransformControlsWithVisible;
      if (controlsWithVisible.visible !== undefined) {
        controlsWithVisible.visible = visible;
      }
      this.transformControls.enabled = visible;
    }
  }

  /**
   * Check if transform controls are dragging
   * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
   */
  isDragging(): boolean {
    const controls = this.transformControls;
    return (controls !== null && controls !== undefined && typeof controls === "object" && "dragging" in controls && typeof controls.dragging === "boolean") ? controls.dragging : false;
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    if (this.transformControls) {
      this.transformControls.dispose();
      this.transformControls = null;
    }
    this.selectedLayerId = null;
    this.onTransformChange = null;
  }
}
