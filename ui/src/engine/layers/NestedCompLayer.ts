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
  private parentFPS: number = 30;

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
      timeRemapEnabled: data?.timeRemapEnabled ?? false,
      timeRemap: data?.timeRemap,
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
   * based on parent frame and time remapping
   */
  private calculateNestedFrame(parentFrame: number): number {
    if (!this.cachedComposition) return 0;

    // If time remap is enabled, use that
    if (this.nestedCompData.timeRemapEnabled && this.nestedCompData.timeRemap) {
      const remappedTime = this.nestedCompData.timeRemap.animated
        ? this.nestedCompEvaluator.evaluate(this.nestedCompData.timeRemap, parentFrame)
        : this.nestedCompData.timeRemap.value;

      // Convert time (seconds) to frame
      const fps = this.nestedCompData.overrideFrameRate && this.nestedCompData.frameRate
        ? this.nestedCompData.frameRate
        : this.cachedComposition.settings.fps;

      return Math.floor(remappedTime * fps);
    }

    // Direct mapping - parent frame = child frame
    // Handle frame rate differences if override is set
    if (this.nestedCompData.overrideFrameRate && this.nestedCompData.frameRate) {
      const parentFps = this.parentFPS;
      const childFps = this.nestedCompData.frameRate;
      return Math.floor(parentFrame * (childFps / parentFps));
    }

    return parentFrame;
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

    // Apply time remap if evaluated
    if (props['timeRemap'] !== undefined && this.nestedCompData.timeRemapEnabled && this.nestedCompData.timeRemap) {
      // Update the time remap value for the next evaluation cycle
      this.nestedCompData.timeRemap.value = props['timeRemap'] as number;
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
   * Enable/disable time remapping
   */
  setTimeRemapEnabled(enabled: boolean): void {
    this.nestedCompData.timeRemapEnabled = enabled;
  }

  /**
   * Set time remap property
   */
  setTimeRemap(timeRemap: AnimatableProperty<number>): void {
    this.nestedCompData.timeRemap = timeRemap;
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
      if (data.timeRemapEnabled !== undefined) {
        this.setTimeRemapEnabled(data.timeRemapEnabled);
      }
      if (data.timeRemap !== undefined) {
        this.setTimeRemap(data.timeRemap);
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
