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

import * as THREE from 'three';
import type { Layer, NestedCompData, Composition, AnimatableProperty } from '@/types/project';
import { BaseLayer } from './BaseLayer';
import { KeyframeEvaluator } from '../animation/KeyframeEvaluator';

// ============================================================================
// TYPES
// ============================================================================

export interface NestedCompRenderContext {
  /** Function to render a composition to a texture */
  renderComposition: (compositionId: string, frame: number) => THREE.Texture | null;
  /** Function to get composition by ID */
  getComposition: (compositionId: string) => Composition | null;
  /** Function to get nested layer instances when collapsed */
  getCompositionLayers?: (compositionId: string) => import('./BaseLayer').BaseLayer[];
}

/** Transform values for combining collapsed nested comp transforms */
export interface CombinedTransform {
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number; z: number };
  opacity: number;
}

// ============================================================================
// NESTED COMP LAYER
// ============================================================================

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

  // Flatten transform state
  private isCollapsed: boolean = false;
  private collapsedLayerIds: string[] = [];

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

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Extract nested comp data with defaults
   */
  private extractNestedCompData(layerData: Layer): NestedCompData {
    const data = layerData.data as NestedCompData | null;

    return {
      compositionId: data?.compositionId ?? '',
      // Speed map (new naming)
      speedMapEnabled: data?.speedMapEnabled ?? data?.timeRemapEnabled ?? false,
      speedMap: data?.speedMap ?? data?.timeRemap,
      // Backwards compatibility aliases
      timeRemapEnabled: data?.timeRemapEnabled ?? data?.speedMapEnabled ?? false,
      timeRemap: data?.timeRemap ?? data?.speedMap,
      flattenTransform: data?.flattenTransform ?? false,
      overrideFrameRate: data?.overrideFrameRate ?? false,
      frameRate: data?.frameRate,
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

  // ============================================================================
  // RENDER CONTEXT
  // ============================================================================

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
    this.parentFPS = fps;
  }

  /**
   * Load and cache the referenced composition
   */
  private loadComposition(): void {
    if (!this.renderContext || !this.nestedCompData.compositionId) {
      return;
    }

    this.cachedComposition = this.renderContext.getComposition(
      this.nestedCompData.compositionId
    );

    if (this.cachedComposition) {
      // Resize mesh to match composition
      this.resizeMesh(
        this.cachedComposition.settings.width,
        this.cachedComposition.settings.height
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

  // ============================================================================
  // TIME CALCULATION
  // ============================================================================

  /**
   * Calculate the frame in the nested composition
   * based on parent frame, timeStretch, and speed map (time remapping)
   *
   * DETERMINISM: This is a pure function of (parentFrame, layer state).
   * Same inputs always produce same outputs.
   */
  private calculateNestedFrame(parentFrame: number): number {
    if (!this.cachedComposition) return 0;

    const nestedFps = this.nestedCompData.overrideFrameRate && this.nestedCompData.frameRate
      ? this.nestedCompData.frameRate
      : this.cachedComposition.settings.fps;

    // If speed map is enabled, use that (overrides timeStretch)
    const speedMapEnabled = this.nestedCompData.speedMapEnabled ?? this.nestedCompData.timeRemapEnabled;
    const speedMapProp = this.nestedCompData.speedMap ?? this.nestedCompData.timeRemap;
    if (speedMapEnabled && speedMapProp) {
      const remappedTime = speedMapProp.animated
        ? this.nestedCompEvaluator.evaluate(speedMapProp, parentFrame)
        : speedMapProp.value;

      return Math.floor(remappedTime * nestedFps);
    }

    // Get layer's timeStretch (100 = normal, 200 = half speed, -100 = reversed)
    const timeStretch = this.layerData.timeStretch ?? 100;
    const isReversed = timeStretch < 0;

    // Calculate effective speed: 100% stretch = 1x, 200% = 0.5x, 50% = 2x
    const stretchFactor = timeStretch !== 0 ? 100 / Math.abs(timeStretch) : 0;

    // Calculate frame relative to layer start
    const layerStartFrame = this.layerData.startFrame ?? 0;
    const layerFrame = parentFrame - layerStartFrame;

    // Apply time stretch and frame rate conversion
    let nestedFrame: number;
    if (this.nestedCompData.overrideFrameRate && this.nestedCompData.frameRate) {
      const parentFps = this.parentFPS;
      const childFps = this.nestedCompData.frameRate;
      nestedFrame = layerFrame * stretchFactor * (childFps / parentFps);
    } else {
      nestedFrame = layerFrame * stretchFactor;
    }

    // Handle reversed playback
    if (isReversed) {
      const nestedDuration = this.cachedComposition.settings.frameCount;
      nestedFrame = nestedDuration - 1 - nestedFrame;
    }

    return Math.floor(nestedFrame);
  }

  // ============================================================================
  // FRAME EVALUATION
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    if (!this.renderContext || !this.cachedComposition) {
      return;
    }

    // Calculate nested frame
    const nestedFrame = this.calculateNestedFrame(frame);

    // Clamp to composition bounds
    const clampedFrame = Math.max(
      0,
      Math.min(nestedFrame, this.cachedComposition.settings.frameCount - 1)
    );

    // Request render of nested composition
    this.renderTexture = this.renderContext.renderComposition(
      this.nestedCompData.compositionId,
      clampedFrame
    );

    // Update material with rendered texture
    if (this.material) {
      if (this.renderTexture) {
        this.material.map = this.renderTexture;
        this.material.color.setHex(0xffffff);
      } else {
        this.material.map = null;
        this.material.color.setHex(0x444444);
      }
      this.material.needsUpdate = true;
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    const props = state.properties;

    // Apply opacity to material
    if (state.transform?.opacity !== undefined && this.material) {
      this.material.opacity = state.transform.opacity / 100;
      this.material.needsUpdate = true;
    }

    // Apply speed map if evaluated
    // Check both new 'speedMap' and legacy 'timeRemap' for backwards compatibility
    const speedMapValue = props['speedMap'] ?? props['timeRemap'];
    const speedMapEnabled = this.nestedCompData.speedMapEnabled ?? this.nestedCompData.timeRemapEnabled;
    const speedMapProp = this.nestedCompData.speedMap ?? this.nestedCompData.timeRemap;
    if (speedMapValue !== undefined && speedMapEnabled && speedMapProp) {
      // Update the speed map value for the next evaluation cycle
      speedMapProp.value = speedMapValue as number;
    }
  }

  // ============================================================================
  // PROPERTY UPDATES
  // ============================================================================

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
    return this.nestedCompData.flattenTransform;
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
      x: parent.position.x + (nestedTransform.position.x * parent.scale.x / 100),
      y: parent.position.y + (nestedTransform.position.y * parent.scale.y / 100),
      z: parent.position.z + (nestedTransform.position.z * parent.scale.z / 100),
    };

    // Rotation: add rotations (simplified - true 3D would use quaternions)
    const combinedRotation = {
      x: parent.rotation.x + nestedTransform.rotation.x,
      y: parent.rotation.y + nestedTransform.rotation.y,
      z: parent.rotation.z + nestedTransform.rotation.z,
    };

    // Scale: multiply scales
    const combinedScale = {
      x: parent.scale.x * nestedTransform.scale.x / 100,
      y: parent.scale.y * nestedTransform.scale.y / 100,
      z: parent.scale.z * nestedTransform.scale.z / 100,
    };

    // Opacity: multiply (normalized to 0-100)
    const combinedOpacity = (parent.opacity / 100) * (nestedTransform.opacity / 100) * 100;

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
    return this.cachedComposition.layers.map(l => l.id);
  }

  /**
   * Check if this nested comp contains 3D layers
   * Flatten transform is most useful when nested comp has 3D layers
   */
  hasNested3DLayers(): boolean {
    if (!this.cachedComposition) {
      return false;
    }
    return this.cachedComposition.layers.some(l => l.threeD);
  }

  /**
   * Override frame rate
   */
  setFrameRateOverride(override: boolean, fps?: number): void {
    this.nestedCompData.overrideFrameRate = override;
    this.nestedCompData.frameRate = fps;
  }

  // ============================================================================
  // LAYER UPDATE
  // ============================================================================

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<NestedCompData> | undefined;

    if (data) {
      if (data.compositionId !== undefined) {
        this.setComposition(data.compositionId);
      }
      // Check speedMap first (new naming), then timeRemap (backwards compatibility)
      if (data.speedMapEnabled !== undefined || data.timeRemapEnabled !== undefined) {
        this.setSpeedMapEnabled(data.speedMapEnabled ?? data.timeRemapEnabled ?? false);
      }
      if (data.speedMap !== undefined || data.timeRemap !== undefined) {
        this.setSpeedMap((data.speedMap ?? data.timeRemap)!);
      }
      if (data.flattenTransform !== undefined) {
        this.setFlattenTransform(data.flattenTransform);
      }
      if (data.overrideFrameRate !== undefined || data.frameRate !== undefined) {
        this.setFrameRateOverride(
          data.overrideFrameRate ?? this.nestedCompData.overrideFrameRate,
          data.frameRate ?? this.nestedCompData.frameRate
        );
      }
    }
  }

  // ============================================================================
  // GETTERS
  // ============================================================================

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
  getCompositionId(): string {
    return this.nestedCompData.compositionId;
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

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
