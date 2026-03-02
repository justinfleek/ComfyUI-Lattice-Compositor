/**
 * NestedCompLayer - Nested Composition
 *
 * Allows compositions to be nested within other compositions.
 * Features:
 *
 * - References another composition by ID
 * - Independent timeline with time remapping
 * - Flatten transform option (render in parent's 3D space)
 * - Frame rate override
 * - Renders nested comp to texture for parent
 *
 * ComfyUI Integration:
 * - Maps to sub-graphs in ComfyUI workflow
 * - Each nested comp can have its own workflow inputs/outputs
 */

import * as THREE from "three";
import type {
  AnimatableProperty,
  Composition,
  Layer,
  NestedCompData,
} from "@/types/project";
import { KeyframeEvaluator } from "../animation/KeyframeEvaluator";
import { BaseLayer } from "./BaseLayer";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export interface NestedCompRenderContext {
  /** Function to render a composition to a texture 
   * System F/Omega: Throws explicit errors instead of returning null
   * Caller should wrap in try/catch if "rendering failure" is an expected state
   */
  renderComposition: (
    compositionId: string,
    frame: number,
  ) => THREE.Texture;
  /** Function to get composition by ID */
  getComposition: (compositionId: string) => Composition | null;
  /** Function to get nested layer instances when collapsed */
  getCompositionLayers?: (
    compositionId: string,
  ) => import("./BaseLayer").BaseLayer[];
}

/** Transform values for combining collapsed nested comp transforms */
export interface CombinedTransform {
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number; z: number };
  opacity: number;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                   // nested // comp // layer
// ════════════════════════════════════════════════════════════════════════════

export class NestedCompLayer extends BaseLayer {
  // Nested comp data
  private nestedCompData: NestedCompData;

  // Render context (provided by LayerManager)
  private renderContext: NestedCompRenderContext | null = null;

  // Display mesh
  private mesh: THREE.Mesh | null = null;
  private material: THREE.MeshBasicMaterial | null = null;

  // Cached render texture
  private renderTexture: THREE.Texture | null = null;

  // Animation evaluator for time remap
  private readonly nestedCompEvaluator: KeyframeEvaluator;

  // Cached composition reference
  private cachedComposition: Composition | null = null;

  // Parent composition FPS for frame rate conversion
  private parentFPS: number = 16;

  // Collapsed state (for flatten transform)
  private isCollapsed: boolean = false;

  constructor(layerData: Layer) {
    super(layerData);

    this.nestedCompEvaluator = new KeyframeEvaluator();

    // Extract nested comp data
    this.nestedCompData = this.extractNestedCompData(layerData);

    // Create placeholder mesh
    this.createMesh();

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // initialization
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Extract nested comp data with defaults
   */
  private extractNestedCompData(layerData: Layer): NestedCompData {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: data ∈ NestedCompData | null → NestedCompData (with explicit defaults)
    const data = (layerData.data !== null && typeof layerData.data === "object") ? layerData.data as NestedCompData : null;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: Extract each property with explicit type narrowing and defaults
    const compositionIdValue = (data !== null && typeof data === "object" && "compositionId" in data && typeof data.compositionId === "string") ? data.compositionId : "";
    const speedMapEnabledValue = (data !== null && typeof data === "object" && "speedMapEnabled" in data && typeof data.speedMapEnabled === "boolean") ? data.speedMapEnabled : ((data !== null && typeof data === "object" && "timeRemapEnabled" in data && typeof data.timeRemapEnabled === "boolean") ? data.timeRemapEnabled : false);
    const speedMapValue = (data !== null && typeof data === "object" && "speedMap" in data) ? data.speedMap : ((data !== null && typeof data === "object" && "timeRemap" in data) ? data.timeRemap : undefined);
    const timeRemapEnabledValue = (data !== null && typeof data === "object" && "timeRemapEnabled" in data && typeof data.timeRemapEnabled === "boolean") ? data.timeRemapEnabled : ((data !== null && typeof data === "object" && "speedMapEnabled" in data && typeof data.speedMapEnabled === "boolean") ? data.speedMapEnabled : false);
    const timeRemapValue = (data !== null && typeof data === "object" && "timeRemap" in data) ? data.timeRemap : ((data !== null && typeof data === "object" && "speedMap" in data) ? data.speedMap : undefined);
    const flattenTransformValue = (data !== null && typeof data === "object" && "flattenTransform" in data && typeof data.flattenTransform === "boolean") ? data.flattenTransform : false;
    const overrideFrameRateValue = (data !== null && typeof data === "object" && "overrideFrameRate" in data && typeof data.overrideFrameRate === "boolean") ? data.overrideFrameRate : false;
    const frameRateValue = (data !== null && typeof data === "object" && "frameRate" in data) ? data.frameRate : undefined;

    return {
      compositionId: compositionIdValue,
      // Speed map (new naming)
      speedMapEnabled: speedMapEnabledValue,
      speedMap: speedMapValue,
      // Backwards compatibility aliases
      timeRemapEnabled: timeRemapEnabledValue,
      timeRemap: timeRemapValue,
      flattenTransform: flattenTransformValue,
      overrideFrameRate: overrideFrameRateValue,
      frameRate: frameRateValue,
    };
  }

  /**
   * Create display mesh
   */
  private createMesh(): void {
    // Start with 1x1, will be resized when composition is set
    const geometry = new THREE.PlaneGeometry(1, 1);
    this.material = new THREE.MeshBasicMaterial({
      color: 0x444444,
      transparent: true,
      side: THREE.DoubleSide,
    });

    this.mesh = new THREE.Mesh(geometry, this.material);
    this.mesh.name = `nestedComp_${this.id}`;
    this.group.add(this.mesh);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                         // render // context
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set the render context (required for nested comp rendering)
   * Called by LayerManager after creation
   */
  setRenderContext(context: NestedCompRenderContext): void {
    this.renderContext = context;

    // Try to load composition
    this.loadComposition();
  }

  /**
   * Set parent composition FPS for frame rate conversion
   */
  setFPS(fps: number): void {
    // Validate FPS (NaN or <= 0 would break frame calculations)
    this.parentFPS = Number.isFinite(fps) && fps > 0 ? fps : 16;
  }

  /**
   * Load and cache the referenced composition
   */
  private loadComposition(): void {
    if (!this.renderContext || !this.nestedCompData.compositionId) {
      return;
    }

    this.cachedComposition = this.renderContext.getComposition(
      this.nestedCompData.compositionId,
    );

    if (this.cachedComposition) {
      // Resize mesh to match composition
      this.resizeMesh(
        this.cachedComposition.settings.width,
        this.cachedComposition.settings.height,
      );
    }
  }

  /**
   * Resize mesh to match composition dimensions
   */
  private resizeMesh(width: number, height: number): void {
    if (!this.mesh) return;

    this.mesh.geometry.dispose();
    this.mesh.geometry = new THREE.PlaneGeometry(width, height);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // time // calculation
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Calculate the frame in the nested composition
   * based on parent frame, timeStretch, and speed map (time remapping)
   *
   * DETERMINISM: This is a pure function of (parentFrame, layer state).
   * Same inputs always produce same outputs.
   */
  private calculateNestedFrame(parentFrame: number): number {
    if (!this.cachedComposition) return 0;

    // Validate FPS values (NaN would corrupt frame calculations)
    const rawNestedFps =
      this.nestedCompData.overrideFrameRate && this.nestedCompData.frameRate
        ? this.nestedCompData.frameRate
        : this.cachedComposition.settings.fps;
    const nestedFps =
      Number.isFinite(rawNestedFps) && rawNestedFps > 0 ? rawNestedFps : 16;

    // If speed map is enabled, use that (overrides timeStretch)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: speedMapEnabled ∈ boolean | undefined → boolean (fallback to timeRemapEnabled)
    const speedMapEnabledValue = (typeof this.nestedCompData.speedMapEnabled === "boolean") ? this.nestedCompData.speedMapEnabled : ((typeof this.nestedCompData.timeRemapEnabled === "boolean") ? this.nestedCompData.timeRemapEnabled : false);
    // Pattern match: speedMap ∈ AnimatableProperty | undefined → AnimatableProperty | undefined (fallback to timeRemap)
    const speedMapPropValue = (this.nestedCompData.speedMap !== undefined) ? this.nestedCompData.speedMap : this.nestedCompData.timeRemap;
    if (speedMapEnabledValue && speedMapPropValue) {
      const remappedTime = speedMapPropValue.animated
        ? this.nestedCompEvaluator.evaluate(speedMapPropValue, parentFrame)
        : speedMapPropValue.value;

      // Validate remapped time (NaN would break rendering)
      const validTime = Number.isFinite(remappedTime) ? remappedTime : 0;
      return Math.floor(validTime * nestedFps);
    }

    // Get layer's timeStretch (100 = normal, 200 = half speed, -100 = reversed)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: timeStretch ∈ number | undefined → number (default 100)
    const rawTimeStretch = (typeof this.layerData.timeStretch === "number" && Number.isFinite(this.layerData.timeStretch)) ? this.layerData.timeStretch : 100;
    const timeStretch = Number.isFinite(rawTimeStretch) ? rawTimeStretch : 100;
    const isReversed = timeStretch < 0;

    // Calculate effective speed: 100% stretch = 1x, 200% = 0.5x, 50% = 2x
    const stretchFactor = timeStretch !== 0 ? 100 / Math.abs(timeStretch) : 0;

    // Calculate frame relative to layer start
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: startFrame ∈ number | undefined → number (default 0)
    const layerStartFrame = (typeof this.layerData.startFrame === "number" && Number.isFinite(this.layerData.startFrame)) ? this.layerData.startFrame : 0;
    const layerFrame = parentFrame - layerStartFrame;

    // Apply time stretch and frame rate conversion
    let nestedFrame: number;
    if (
      this.nestedCompData.overrideFrameRate &&
      this.nestedCompData.frameRate
    ) {
      // Validate parent FPS to prevent division by zero
      const parentFps =
        Number.isFinite(this.parentFPS) && this.parentFPS > 0
          ? this.parentFPS
          : 16;
      const childFps =
        Number.isFinite(this.nestedCompData.frameRate) &&
        this.nestedCompData.frameRate > 0
          ? this.nestedCompData.frameRate
          : 16;
      nestedFrame = layerFrame * stretchFactor * (childFps / parentFps);
    } else {
      nestedFrame = layerFrame * stretchFactor;
    }

    // Handle reversed playback
    if (isReversed) {
      const nestedDuration = this.cachedComposition.settings.frameCount;
      nestedFrame = nestedDuration - 1 - nestedFrame;
    }

    // Final validation - NaN frame would break rendering
    return Number.isFinite(nestedFrame) ? Math.floor(nestedFrame) : 0;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // frame // evaluation
  // ════════════════════════════════════════════════════════════════════════════

  protected onEvaluateFrame(frame: number): void {
    if (
      !this.renderContext ||
      !this.cachedComposition ||
      !this.nestedCompData.compositionId
    ) {
      return;
    }

    // Calculate nested frame
    const nestedFrame = this.calculateNestedFrame(frame);

    // Clamp to composition bounds
    const clampedFrame = Math.max(
      0,
      Math.min(nestedFrame, this.cachedComposition.settings.frameCount - 1),
    );

    // Request render of nested composition
    // System F/Omega: renderComposition throws explicit errors - wrap in try/catch for expected failures
    try {
      this.renderTexture = this.renderContext.renderComposition(
        this.nestedCompData.compositionId,
        clampedFrame,
      );
      
      // Update material with rendered texture
      if (this.material) {
        this.material.map = this.renderTexture;
        this.material.color.setHex(0xffffff);
        this.material.needsUpdate = true;
      }
    } catch (error) {
      // Rendering failed - show placeholder (expected state for missing/empty comps)
      this.renderTexture = null;
      if (this.material) {
        this.material.map = null;
        this.material.color.setHex(0x444444);
        this.material.needsUpdate = true;
      }
    }
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    const props = state.properties;

    // Apply opacity to material (opacity is on EvaluatedLayer, not transform)
    // Validate opacity (NaN would corrupt material)
    if (state.opacity !== undefined && this.material) {
      const validOpacity = Number.isFinite(state.opacity) ? state.opacity : 100;
      this.material.opacity = Math.max(0, Math.min(100, validOpacity)) / 100;
      this.material.needsUpdate = true;
    }

    // Apply speed map if evaluated
    // Check both new 'speedMap' and legacy 'timeRemap' for backwards compatibility
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: props.speedMap ∈ PropertyValue | undefined → PropertyValue | undefined (fallback to timeRemap)
    const speedMapValue = (props.speedMap !== undefined) ? props.speedMap : props.timeRemap;
    const speedMapEnabled =
      (typeof this.nestedCompData.speedMapEnabled === "boolean") ? this.nestedCompData.speedMapEnabled : ((typeof this.nestedCompData.timeRemapEnabled === "boolean") ? this.nestedCompData.timeRemapEnabled : false);
    const speedMapProp =
      (this.nestedCompData.speedMap !== undefined) ? this.nestedCompData.speedMap : this.nestedCompData.timeRemap;
    if (speedMapValue !== undefined && speedMapEnabled && speedMapProp) {
      // Update the speed map value for the next evaluation cycle
      speedMapProp.value = speedMapValue as number;
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // property // updates
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Set the source composition
   */
  setComposition(compositionId: string): void {
    this.nestedCompData.compositionId = compositionId;
    this.loadComposition();
  }

  /**
   * Enable/disable speed map (time remapping)
   */
  setSpeedMapEnabled(enabled: boolean): void {
    this.nestedCompData.speedMapEnabled = enabled;
    this.nestedCompData.timeRemapEnabled = enabled; // Backwards compatibility
  }

  /** @deprecated Use setSpeedMapEnabled instead */
  setTimeRemapEnabled(enabled: boolean): void {
    this.setSpeedMapEnabled(enabled);
  }

  /**
   * Set speed map property
   */
  setSpeedMap(speedMap: AnimatableProperty<number>): void {
    this.nestedCompData.speedMap = speedMap;
    this.nestedCompData.timeRemap = speedMap; // Backwards compatibility
  }

  /** @deprecated Use setSpeedMap instead */
  setTimeRemap(timeRemap: AnimatableProperty<number>): void {
    this.setSpeedMap(timeRemap);
  }

  /**
   * Enable/disable flatten transform
   */
  setFlattenTransform(flatten: boolean): void {
    this.nestedCompData.flattenTransform = flatten;
    this.isCollapsed = flatten;

    // When flattened, hide this layer's mesh (nested layers render directly in parent scene)
    if (this.mesh) {
      this.mesh.visible = !flatten;
    }
  }

  /** @deprecated Use setFlattenTransform instead */
  setCollapseTransformations(collapse: boolean): void {
    this.setFlattenTransform(collapse);
  }

  /**
   * Check if flatten transform is enabled
   */
  isFlattenEnabled(): boolean {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: flattenTransform ∈ boolean | undefined → boolean (default false)
    return (typeof this.nestedCompData.flattenTransform === "boolean") ? this.nestedCompData.flattenTransform : false;
  }

  /** @deprecated Use isFlattenEnabled instead */
  isCollapseEnabled(): boolean {
    return this.isFlattenEnabled();
  }

  /**
   * Get the current transform values of this nested comp layer
   * Used when combining transforms for collapsed nested layers
   */
  getParentTransform(): CombinedTransform {
    return {
      position: {
        x: this.group.position.x,
        y: -this.group.position.y, // Convert back to screen coords
        z: this.group.position.z,
      },
      rotation: {
        x: THREE.MathUtils.radToDeg(this.group.rotation.x),
        y: THREE.MathUtils.radToDeg(this.group.rotation.y),
        z: THREE.MathUtils.radToDeg(-this.group.rotation.z), // Convert back
      },
      scale: {
        x: this.group.scale.x * 100,
        y: this.group.scale.y * 100,
        z: this.group.scale.z * 100,
      },
      opacity: this.getOpacity(),
    };
  }

  /**
   * Get opacity value (for collapsed layer opacity combination)
   */
  private getOpacity(): number {
    // Get opacity from material
    if (this.material) {
      return this.material.opacity * 100;
    }
    return 100;
  }

  /**
   * Combine parent (this nested comp) and nested layer transforms
   * Used when flatten transform is enabled
   *
   * @param nestedTransform - The transform of a nested layer
   * @returns Combined transform for rendering in parent scene
   */
  combineTransforms(nestedTransform: CombinedTransform): CombinedTransform {
    const parent = this.getParentTransform();

    // Position: nested position offset by parent position (accounting for scale)
    const combinedPosition = {
      x:
        parent.position.x + (nestedTransform.position.x * parent.scale.x) / 100,
      y:
        parent.position.y + (nestedTransform.position.y * parent.scale.y) / 100,
      z:
        parent.position.z + (nestedTransform.position.z * parent.scale.z) / 100,
    };

    // Rotation: add rotations (simplified - true 3D would use quaternions)
    const combinedRotation = {
      x: parent.rotation.x + nestedTransform.rotation.x,
      y: parent.rotation.y + nestedTransform.rotation.y,
      z: parent.rotation.z + nestedTransform.rotation.z,
    };

    // Scale: multiply scales
    const combinedScale = {
      x: (parent.scale.x * nestedTransform.scale.x) / 100,
      y: (parent.scale.y * nestedTransform.scale.y) / 100,
      z: (parent.scale.z * nestedTransform.scale.z) / 100,
    };

    // Opacity: multiply (normalized to 0-100)
    const combinedOpacity =
      (parent.opacity / 100) * (nestedTransform.opacity / 100) * 100;

    return {
      position: combinedPosition,
      rotation: combinedRotation,
      scale: combinedScale,
      opacity: combinedOpacity,
    };
  }

  /**
   * Get the IDs of layers in the nested composition
   * Used for managing collapsed layers in the parent scene
   */
  getNestedLayerIds(): string[] {
    if (!this.cachedComposition) {
      return [];
    }
    return this.cachedComposition.layers.map((l) => l.id);
  }

  /**
   * Check if this nested comp contains 3D layers
   * Flatten transform is most useful when nested comp has 3D layers
   */
  hasNested3DLayers(): boolean {
    if (!this.cachedComposition) {
      return false;
    }
    return this.cachedComposition.layers.some((l) => l.threeD);
  }

  /**
   * Override frame rate
   */
  setFrameRateOverride(override: boolean, fps?: number): void {
    this.nestedCompData.overrideFrameRate = override;
    this.nestedCompData.frameRate = fps;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                           // layer // update
  // ════════════════════════════════════════════════════════════════════════════

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<NestedCompData> | undefined;

    if (data) {
      if (data.compositionId !== undefined && data.compositionId !== null) {
        this.setComposition(data.compositionId);
      }
      // Check speedMap first (new naming), then timeRemap (backwards compatibility)
      if (
        data.speedMapEnabled !== undefined ||
        data.timeRemapEnabled !== undefined
      ) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: speedMapEnabled ∈ boolean | undefined → boolean (fallback chain: timeRemapEnabled → false)
        const speedMapEnabledUpdate = (typeof data.speedMapEnabled === "boolean") ? data.speedMapEnabled : ((typeof data.timeRemapEnabled === "boolean") ? data.timeRemapEnabled : false);
        this.setSpeedMapEnabled(speedMapEnabledUpdate);
      }
      if (data.speedMap !== undefined || data.timeRemap !== undefined) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: speedMap ∈ AnimatableProperty | undefined → AnimatableProperty (fallback to timeRemap, non-null assertion removed)
        const speedMapUpdate = (data.speedMap !== undefined) ? data.speedMap : data.timeRemap;
        if (speedMapUpdate !== undefined) {
          this.setSpeedMap(speedMapUpdate);
        }
      }
      if (data.flattenTransform !== undefined) {
        this.setFlattenTransform(data.flattenTransform);
      }
      if (
        data.overrideFrameRate !== undefined ||
        data.frameRate !== undefined
      ) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: overrideFrameRate ∈ boolean | undefined → boolean (fallback chain: nestedCompData.overrideFrameRate → false)
        const overrideFrameRateUpdate = (typeof data.overrideFrameRate === "boolean") ? data.overrideFrameRate : ((typeof this.nestedCompData.overrideFrameRate === "boolean") ? this.nestedCompData.overrideFrameRate : false);
        // Pattern match: frameRate ∈ number | undefined → number | undefined (fallback to nestedCompData.frameRate)
        const frameRateUpdate = (typeof data.frameRate === "number" && Number.isFinite(data.frameRate)) ? data.frameRate : this.nestedCompData.frameRate;
        this.setFrameRateOverride(overrideFrameRateUpdate, frameRateUpdate);
      }
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // getters
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Get nested comp data
   */
  getNestedCompData(): NestedCompData {
    return { ...this.nestedCompData };
  }

  /**
   * Get referenced composition
   */
  getComposition(): Composition | null {
    return this.cachedComposition;
  }

  /**
   * Get composition ID
   */
  getCompositionId(): string | null {
    return this.nestedCompData.compositionId;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                  // disposal
  // ════════════════════════════════════════════════════════════════════════════

  protected onDispose(): void {
    if (this.material) {
      this.material.dispose();
    }

    if (this.mesh) {
      this.mesh.geometry.dispose();
      this.group.remove(this.mesh);
    }

    // Note: renderTexture is managed by the render context
    this.renderTexture = null;
    this.cachedComposition = null;
  }
}
