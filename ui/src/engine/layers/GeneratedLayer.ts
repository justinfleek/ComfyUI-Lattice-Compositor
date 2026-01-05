/**
 * GeneratedLayer - AI-Generated Content Layer
 *
 * Displays AI-generated content (depth maps, normal maps, edges, segments, etc.)
 * Manages generation state and auto-regeneration.
 *
 * Features:
 * - Multiple generation types (depth, normal, edge, segment, inpaint)
 * - Source layer reference
 * - Generation status tracking
 * - Auto-regeneration on source changes
 *
 * DETERMINISM: Output is deterministic given same model + seed + input
 */

import * as THREE from "three";
import type { GeneratedLayerData, Layer } from "@/types/project";
import { BaseLayer } from "./BaseLayer";

export class GeneratedLayer extends BaseLayer {
  private mesh: THREE.Mesh | null = null;
  private material: THREE.MeshBasicMaterial | null = null;
  private texture: THREE.Texture | null = null;
  private generatedData: GeneratedLayerData;
  private statusIndicator: THREE.Mesh | null = null;

  constructor(layerData: Layer) {
    super(layerData);
    this.generatedData = this.extractGeneratedData(layerData);
    this.createMesh();
  }

  /**
   * Extract generated layer data from layer object
   */
  private extractGeneratedData(layerData: Layer): GeneratedLayerData {
    const data = layerData.data as Partial<GeneratedLayerData> | undefined;
    return {
      generationType: data?.generationType ?? "depth",
      sourceLayerId: data?.sourceLayerId ?? null,
      model: data?.model ?? "depth-anything-v2",
      parameters: data?.parameters ?? {},
      generatedAssetId: data?.generatedAssetId ?? null,
      status: data?.status ?? "pending",
      autoRegenerate: data?.autoRegenerate ?? false,
      lastGenerated: data?.lastGenerated,
      errorMessage: data?.errorMessage,
    };
  }

  private createMesh(): void {
    const geometry = new THREE.PlaneGeometry(1, 1, 1, 1);

    this.material = new THREE.MeshBasicMaterial({
      color: 0xffffff,
      transparent: true,
      opacity: 1.0,
      side: THREE.DoubleSide,
    });

    this.mesh = new THREE.Mesh(geometry, this.material);
    this.mesh.name = `generated_${this.id}`;
    this.group.add(this.mesh);

    // Create status indicator
    this.createStatusIndicator();
  }

  private createStatusIndicator(): void {
    // Small indicator showing generation status
    const geometry = new THREE.CircleGeometry(10, 16);
    const material = new THREE.MeshBasicMaterial({
      color: this.getStatusColor(),
      transparent: true,
      opacity: 0.8,
    });

    this.statusIndicator = new THREE.Mesh(geometry, material);
    this.statusIndicator.position.set(-50, 50, 1);
    this.statusIndicator.name = `status_${this.id}`;
    this.group.add(this.statusIndicator);
  }

  private getStatusColor(): number {
    switch (this.generatedData.status) {
      case "pending":
        return 0xffaa00; // Orange
      case "generating":
        return 0x00aaff; // Blue
      case "complete":
        return 0x00ff00; // Green
      case "error":
        return 0xff0000; // Red
      default:
        return 0x888888; // Gray
    }
  }

  setTexture(texture: THREE.Texture): void {
    this.texture = texture;
    if (this.material) {
      this.material.map = texture;
      this.material.needsUpdate = true;
    }
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(_frame: number): void {
    // Update status indicator color
    if (this.statusIndicator) {
      (this.statusIndicator.material as THREE.MeshBasicMaterial).color.setHex(
        this.getStatusColor(),
      );
    }

    // Generated layers show their output image
    // The actual generation is handled by the AI service
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<GeneratedLayerData> | undefined;

    if (data) {
      const oldSourceId = this.generatedData.sourceLayerId;
      Object.assign(this.generatedData, data);

      // Auto-regenerate if source changed and auto-regenerate is enabled
      if (
        this.generatedData.autoRegenerate &&
        data.sourceLayerId !== undefined &&
        data.sourceLayerId !== oldSourceId
      ) {
        this.regenerate();
      }
    }
  }

  protected onDispose(): void {
    if (this.texture) {
      this.texture.dispose();
    }
    if (this.material) {
      this.material.dispose();
    }
    if (this.mesh) {
      this.mesh.geometry.dispose();
    }
    if (this.statusIndicator) {
      (this.statusIndicator.material as THREE.Material).dispose();
      this.statusIndicator.geometry.dispose();
    }
  }

  // ============================================================================
  // GENERATION-SPECIFIC METHODS
  // ============================================================================

  /**
   * Trigger regeneration of the content
   */
  async regenerate(): Promise<void> {
    this.generatedData.status = "generating";

    try {
      // Generation would be handled by AI service
      // This is a placeholder for the generation pipeline
      this.generatedData.status = "complete";
      this.generatedData.lastGenerated = new Date().toISOString();
    } catch (error) {
      this.generatedData.status = "error";
      this.generatedData.errorMessage =
        error instanceof Error ? error.message : "Unknown error";
    }
  }
}
