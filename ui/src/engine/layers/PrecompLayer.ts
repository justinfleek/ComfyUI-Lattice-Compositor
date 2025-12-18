/**
 * PrecompLayer - Nested Composition (Pre-Composition)
 *
 * Allows compositions to be nested within other compositions,
 * just like After Effects pre-comps. Features:
 *
 * - References another composition by ID
 * - Independent timeline with time remapping
 * - Collapse transformations option
 * - Frame rate override
 * - Renders nested comp to texture for parent
 *
 * ComfyUI Integration:
 * - Maps to sub-graphs in ComfyUI workflow
 * - Each precomp can have its own workflow inputs/outputs
 */

import * as THREE from 'three';
import type { Layer, PrecompData, Composition, AnimatableProperty } from '@/types/project';
import { BaseLayer } from './BaseLayer';
import { KeyframeEvaluator } from '../animation/KeyframeEvaluator';

// ============================================================================
// TYPES
// ============================================================================

export interface PrecompRenderContext {
  /** Function to render a composition to a texture */
  renderComposition: (compositionId: string, frame: number) => THREE.Texture | null;
  /** Function to get composition by ID */
  getComposition: (compositionId: string) => Composition | null;
  /** Function to get nested layer instances when collapsed */
  getCompositionLayers?: (compositionId: string) => import('./BaseLayer').BaseLayer[];
}

/** Transform values for combining collapsed precomp transforms */
export interface CombinedTransform {
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  scale: { x: number; y: number; z: number };
  opacity: number;
}

// ============================================================================
// PRECOMP LAYER
// ============================================================================

export class PrecompLayer extends BaseLayer {
  // Precomp data
  private precompData: PrecompData;

  // Render context (provided by LayerManager)
  private renderContext: PrecompRenderContext | null = null;

  // Display mesh
  private mesh: THREE.Mesh | null = null;
  private material: THREE.MeshBasicMaterial | null = null;

  // Cached render texture
  private renderTexture: THREE.Texture | null = null;

  // Animation evaluator for time remap
  private readonly precompEvaluator: KeyframeEvaluator;

  // Cached composition reference
  private cachedComposition: Composition | null = null;

  // Parent composition FPS for frame rate conversion
  private parentFPS: number = 30;

  // Collapse transformations state
  private isCollapsed: boolean = false;
  private collapsedLayerIds: string[] = [];

  constructor(layerData: Layer) {
    super(layerData);

    this.precompEvaluator = new KeyframeEvaluator();

    // Extract precomp data
    this.precompData = this.extractPrecompData(layerData);

    // Create placeholder mesh
    this.createMesh();

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Extract precomp data with defaults
   */
  private extractPrecompData(layerData: Layer): PrecompData {
    const data = layerData.data as PrecompData | null;

    return {
      compositionId: data?.compositionId ?? '',
      timeRemapEnabled: data?.timeRemapEnabled ?? false,
      timeRemap: data?.timeRemap,
      collapseTransformations: data?.collapseTransformations ?? false,
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
    this.mesh.name = `precomp_${this.id}`;
    this.group.add(this.mesh);
  }

  // ============================================================================
  // RENDER CONTEXT
  // ============================================================================

  /**
   * Set the render context (required for precomp rendering)
   * Called by LayerManager after creation
   */
  setRenderContext(context: PrecompRenderContext): void {
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
    if (!this.renderContext || !this.precompData.compositionId) {
      return;
    }

    this.cachedComposition = this.renderContext.getComposition(
      this.precompData.compositionId
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
    if (this.precompData.timeRemapEnabled && this.precompData.timeRemap) {
      const remappedTime = this.precompData.timeRemap.animated
        ? this.precompEvaluator.evaluate(this.precompData.timeRemap, parentFrame)
        : this.precompData.timeRemap.value;

      // Convert time (seconds) to frame
      const fps = this.precompData.overrideFrameRate && this.precompData.frameRate
        ? this.precompData.frameRate
        : this.cachedComposition.settings.fps;

      return Math.floor(remappedTime * fps);
    }

    // Direct mapping - parent frame = child frame
    // Handle frame rate differences if override is set
    if (this.precompData.overrideFrameRate && this.precompData.frameRate) {
      const parentFps = this.parentFPS;
      const childFps = this.precompData.frameRate;
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
      this.precompData.compositionId,
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
    if (props['timeRemap'] !== undefined && this.precompData.timeRemapEnabled && this.precompData.timeRemap) {
      // Update the time remap value for the next evaluation cycle
      this.precompData.timeRemap.value = props['timeRemap'] as number;
    }
  }

  // ============================================================================
  // PROPERTY UPDATES
  // ============================================================================

  /**
   * Set the source composition
   */
  setComposition(compositionId: string): void {
    this.precompData.compositionId = compositionId;
    this.loadComposition();
  }

  /**
   * Enable/disable time remapping
   */
  setTimeRemapEnabled(enabled: boolean): void {
    this.precompData.timeRemapEnabled = enabled;
  }

  /**
   * Set time remap property
   */
  setTimeRemap(timeRemap: AnimatableProperty<number>): void {
    this.precompData.timeRemap = timeRemap;
  }

  /**
   * Enable/disable collapse transformations
   */
  setCollapseTransformations(collapse: boolean): void {
    this.precompData.collapseTransformations = collapse;
    this.isCollapsed = collapse;

    // When collapsed, hide this layer's mesh (nested layers render directly in parent scene)
    if (this.mesh) {
      this.mesh.visible = !collapse;
    }
  }

  /**
   * Check if collapse transformations is enabled
   */
  isCollapseEnabled(): boolean {
    return this.precompData.collapseTransformations;
  }

  /**
   * Get the current transform values of this precomp layer
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
   * Combine parent (this precomp) and nested layer transforms
   * Used when collapse transformations is enabled
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
   * Check if this precomp contains 3D layers
   * Collapse is most useful when nested comp has 3D layers
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
    this.precompData.overrideFrameRate = override;
    this.precompData.frameRate = fps;
  }

  // ============================================================================
  // LAYER UPDATE
  // ============================================================================

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<PrecompData> | undefined;

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
      if (data.collapseTransformations !== undefined) {
        this.setCollapseTransformations(data.collapseTransformations);
      }
      if (data.overrideFrameRate !== undefined || data.frameRate !== undefined) {
        this.setFrameRateOverride(
          data.overrideFrameRate ?? this.precompData.overrideFrameRate,
          data.frameRate ?? this.precompData.frameRate
        );
      }
    }
  }

  // ============================================================================
  // GETTERS
  // ============================================================================

  /**
   * Get precomp data
   */
  getPrecompData(): PrecompData {
    return { ...this.precompData };
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
    return this.precompData.compositionId;
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
