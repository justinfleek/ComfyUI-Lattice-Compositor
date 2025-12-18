/**
 * AdjustmentLayer - Apply Effects to Layers Below
 *
 * An adjustment layer in After Effects applies its effects to all layers
 * below it in the layer stack. This is achieved through:
 *
 * 1. Rendering all affected layers to a texture
 * 2. Applying the adjustment layer's effects to that texture
 * 3. Displaying the result in place of the affected layers
 *
 * Key behaviors:
 * - The adjustment layer itself is transparent
 * - Effects are applied to composited result of layers below
 * - Respects the adjustment layer's opacity and blend mode
 * - Multiple adjustment layers stack correctly
 */

import * as THREE from 'three';
import type { Layer, AnimatableProperty } from '@/types/project';
import { BaseLayer } from './BaseLayer';
import { processEffectStack, hasEnabledEffects } from '@/services/effectProcessor';
import { layerLogger } from '@/utils/logger';

// ============================================================================
// TYPES
// ============================================================================

export interface AdjustmentRenderContext {
  /** Function to render layers below this one to a texture */
  renderLayersBelow: (adjustmentLayerId: string, frame: number) => HTMLCanvasElement | null;
  /** Function to get canvas dimensions */
  getCanvasDimensions: () => { width: number; height: number };
  /** Mark layers below as handled (don't render them normally) */
  markLayersHandled: (layerIds: string[]) => void;
}

// ============================================================================
// ADJUSTMENT LAYER
// ============================================================================

export class AdjustmentLayer extends BaseLayer {
  // Render context (provided by LayerManager)
  private renderContext: AdjustmentRenderContext | null = null;

  // Display mesh (full-screen quad)
  private mesh: THREE.Mesh | null = null;
  private material: THREE.MeshBasicMaterial | null = null;

  // Result texture (adjusted result of layers below)
  private resultTexture: THREE.Texture | null = null;

  // Canvas for effect processing
  private effectCanvas: HTMLCanvasElement | null = null;
  private effectCtx: CanvasRenderingContext2D | null = null;

  // Layer IDs that this adjustment affects
  private affectedLayerIds: string[] = [];

  // Composition dimensions
  private compWidth: number = 1;
  private compHeight: number = 1;

  constructor(layerData: Layer) {
    super(layerData);

    // Create placeholder mesh
    this.createMesh();

    // Apply initial blend mode
    this.initializeBlendMode();

    layerLogger.debug(`AdjustmentLayer created: ${this.id}`);
  }

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Create display mesh (full-screen quad for adjustment result)
   */
  private createMesh(): void {
    // Start with 1x1, will be resized to match composition
    const geometry = new THREE.PlaneGeometry(1, 1);
    this.material = new THREE.MeshBasicMaterial({
      transparent: true,
      side: THREE.DoubleSide,
      // Start invisible - only visible when we have adjusted content
      visible: false,
    });

    this.mesh = new THREE.Mesh(geometry, this.material);
    this.mesh.name = `adjustment_${this.id}`;
    this.group.add(this.mesh);
  }

  /**
   * Resize mesh to match composition dimensions
   */
  private resizeMesh(width: number, height: number): void {
    if (!this.mesh) return;

    this.compWidth = width;
    this.compHeight = height;

    this.mesh.geometry.dispose();
    this.mesh.geometry = new THREE.PlaneGeometry(width, height);

    // Create/resize effect canvas
    this.effectCanvas = document.createElement('canvas');
    this.effectCanvas.width = width;
    this.effectCanvas.height = height;
    this.effectCtx = this.effectCanvas.getContext('2d');
  }

  // ============================================================================
  // RENDER CONTEXT
  // ============================================================================

  /**
   * Set the render context (required for adjustment layer rendering)
   * Called by LayerManager after creation
   */
  setRenderContext(context: AdjustmentRenderContext): void {
    this.renderContext = context;

    // Get and apply composition dimensions
    const dims = context.getCanvasDimensions();
    this.resizeMesh(dims.width, dims.height);
  }

  /**
   * Set the IDs of layers affected by this adjustment layer
   */
  setAffectedLayers(layerIds: string[]): void {
    this.affectedLayerIds = layerIds;
  }

  /**
   * Get the IDs of layers affected by this adjustment layer
   */
  getAffectedLayers(): string[] {
    return [...this.affectedLayerIds];
  }

  // ============================================================================
  // FRAME EVALUATION
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    if (!this.renderContext || !this.mesh || !this.material) {
      return;
    }

    // Check if this adjustment layer is enabled and has effects
    if (!this.hasEnabledEffects() || !this.layerData.adjustmentLayer) {
      // Hide the mesh when not acting as adjustment
      this.material.visible = false;
      return;
    }

    // Request render of layers below
    const sourceCanvas = this.renderContext.renderLayersBelow(this.id, frame);

    if (!sourceCanvas) {
      this.material.visible = false;
      return;
    }

    // Apply effects to the source canvas
    try {
      const qualityHint = this.isDraftQuality() ? 'draft' : 'high';
      const result = processEffectStack(this.effects, sourceCanvas, frame, qualityHint);

      // Create texture from result
      this.updateResultTexture(result.canvas);

      // Mark affected layers as handled so they don't render normally
      this.renderContext.markLayersHandled(this.affectedLayerIds);

      // Show the adjusted result
      this.material.visible = true;
    } catch (error) {
      layerLogger.error(`Error processing adjustment layer ${this.id}:`, error);
      this.material.visible = false;
    }
  }

  protected override onApplyEvaluatedState(state: import('../MotionEngine').EvaluatedLayer): void {
    // Apply any evaluated effects
    if (state.effects.length > 0) {
      this.applyEvaluatedEffects(state.effects);
    }
  }

  /**
   * Update the result texture with the adjusted canvas
   */
  private updateResultTexture(canvas: HTMLCanvasElement): void {
    if (!this.material) return;

    // Dispose old texture
    if (this.resultTexture) {
      this.resultTexture.dispose();
    }

    // Create new texture from canvas
    this.resultTexture = new THREE.CanvasTexture(canvas);
    this.resultTexture.minFilter = THREE.LinearFilter;
    this.resultTexture.magFilter = THREE.LinearFilter;
    this.resultTexture.colorSpace = THREE.SRGBColorSpace;

    // Apply to material
    this.material.map = this.resultTexture;
    this.material.needsUpdate = true;
  }

  // ============================================================================
  // SOURCE CANVAS (for additional effects processing)
  // ============================================================================

  /**
   * Get source canvas for this layer
   * For adjustment layers, this is the adjusted result
   */
  protected override getSourceCanvas(): HTMLCanvasElement | null {
    if (!this.renderContext) {
      return null;
    }

    // Get the source (layers below, already adjusted)
    return this.renderContext.renderLayersBelow(this.id, 0);
  }

  // ============================================================================
  // ADJUSTMENT STATE
  // ============================================================================

  /**
   * Check if this layer is currently acting as an adjustment layer
   */
  isAdjustmentMode(): boolean {
    return this.layerData.adjustmentLayer === true;
  }

  /**
   * Set adjustment layer mode
   */
  setAdjustmentMode(enabled: boolean): void {
    this.layerData.adjustmentLayer = enabled;

    // Hide/show mesh based on mode
    if (this.material) {
      this.material.visible = enabled && this.hasEnabledEffects();
    }
  }

  // ============================================================================
  // LAYER UPDATE
  // ============================================================================

  protected onUpdate(properties: Partial<Layer>): void {
    if (properties.adjustmentLayer !== undefined) {
      this.setAdjustmentMode(properties.adjustmentLayer);
    }
  }

  // ============================================================================
  // DISPOSAL
  // ============================================================================

  protected onDispose(): void {
    if (this.resultTexture) {
      this.resultTexture.dispose();
      this.resultTexture = null;
    }

    if (this.material) {
      this.material.dispose();
    }

    if (this.mesh) {
      this.mesh.geometry.dispose();
      this.group.remove(this.mesh);
    }

    this.effectCanvas = null;
    this.effectCtx = null;
    this.affectedLayerIds = [];
  }
}

/**
 * Check if a layer is an adjustment layer
 */
export function isAdjustmentLayer(layer: Layer): boolean {
  return layer.adjustmentLayer === true;
}
